module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec83Additive

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec53a_finrank_inf_of_finrank_sup_sup
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {SB SC T : Submodule K E} {n m : ℕ}
    (hSB : Module.finrank K ↥SB = n) (hSC : Module.finrank K ↥SC = n)
    (hT : Module.finrank K ↥T = 2 * m)
    (hBT : Module.finrank K ↥(SB ⊓ T) + 1 = 2 * m)
    (hCT : Module.finrank K ↥(SC ⊓ T) + 1 = 2 * m)
    (hspan : T ≤ SB ⊔ SC)
    (hdim : Module.finrank K ↥((SB ⊔ T) ⊓ (SC ⊔ T)) = 2 * m + 1) :
    Module.finrank K ↥(SB ⊓ SC) + 1 = 2 * m := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq SB T
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq SC T
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (SB ⊔ T) (SC ⊔ T)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq SB SC
  have hsup : (SB ⊔ T) ⊔ (SC ⊔ T) = SB ⊔ SC := by
    calc (SB ⊔ T) ⊔ (SC ⊔ T) = (SB ⊔ SC) ⊔ (T ⊔ T) := sup_sup_sup_comm SB T SC T
      _ = (SB ⊔ SC) ⊔ T := by rw [sup_idem]
      _ = SB ⊔ SC := sup_eq_left.mpr hspan
  rw [hsup] at h3
  omega

end CFSG.RankThree.GF2n.Stroth80
