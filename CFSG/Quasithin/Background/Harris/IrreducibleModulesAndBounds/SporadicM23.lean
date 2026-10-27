module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Exclusion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1 CFSG.Blueprint
  CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem false_of_M23
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M23)) : False := by
  obtain ⟨e⟩ := hM
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* S23 := e
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  refine false_of_autInner_prime h e' m23_autInner (r := 4) m23_rank_le
    (p := 23) (by norm_num) ?_ ?_
  · show 23 ∣ Nat.card NativeSporadic.M23
    rw [m23_card]
    norm_num
  · rw [orderOf_two_zmod_23]
    norm_num

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
