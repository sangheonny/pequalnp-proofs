import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_54615
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [6, 7]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [8, 14]⟩, ⟨.and, [0, 12]⟩, ⟨.and, [1, 15]⟩, ⟨.and, [2, 13]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [19, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_54615

theorem PEqualNP.Outside.L_meta_54615 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (276334 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_54615.witness, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_54615.witness]
  · decide +kernel
  · decide +kernel
