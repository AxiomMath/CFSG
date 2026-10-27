module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KRecog
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KSylowFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KMod2Fix
public import Certificates.Certificate1491003

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

theorem identC : IdentC :=
  Certificates.certificate1491003

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup KInputs CFSG.LocalAnalysis.UniquenessCase.UC22

theorem alt6ModTwoCore_holds :
    Alt6ModTwoCore := by
  intro K _ _ hK W _ _ _ _ ρ z hz _ hfix e he
  obtain ⟨ι⟩ := nonempty_mulEquiv_model3 hK
  have hcen : center K = zpowers (ι.symm c3) :=
    center_eq_zpowers_of_mulEquiv ι model3_facts.2.2.2.2 (by rw [orderOf_c3, hK.2.1])
  have hc3 : ι.symm c3 ^ 3 = 1 := by
    have h : c3 ^ 3 = 1 := orderOf_c3 ▸ pow_orderOf_eq_one c3
    rw [← map_pow, h, map_one]
  have h1 : 1 + ρ (ι.symm c3) + ρ (ι.symm c3) ^ 2 = 0 :=
    one_add_add_sq_eq_zero ρ hc3 (hcen ▸ hz) hfix
  obtain ⟨w, hw, hw'⟩ := exists_fixed_model3_of_mod2 identC
    (orderOf_e3 ▸ pow_orderOf_eq_one e3) (ρ.comp ι.symm.toMonoidHom) h1
  have hcard : ¬ 25 ∣ Nat.card K := by
    rw [card_eq_of_isAlt6_quot hK.2.2, hK.2.1]
    norm_num
  exact exists_fixed_of_orderOf_eq_five hcard ρ (e₀ := ι.symm e3)
    (by rw [MulEquiv.orderOf_eq, orderOf_e3]) he hw hw'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
