module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KRecog
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KSylowFive
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCharFix
public import Certificates.Certificate1491004
public import Certificates.Certificate1491005

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

theorem identD : IdentD :=
  Certificates.certificate1491004

theorem identE : IdentE :=
  Certificates.certificate1491005

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup KInputs CFSG.LocalAnalysis.UniquenessCase.UC22

theorem alt6CharCore_holds :
    Alt6CharCore := by
  intro q hq hq7 K _ _ hqs hZ36 hA V _ _ _ _ ρ z hz hz3 hfix e he
  rcases hZ36 with hZ | hZ
  · obtain ⟨ι⟩ := nonempty_mulEquiv_model3 ⟨hqs, hZ, hA⟩
    have hcen : center K = zpowers (ι.symm c3) :=
      center_eq_zpowers_of_mulEquiv ι model3_facts.2.2.2.2 (by rw [orderOf_c3, hZ])
    have hc3 : ι.symm c3 ^ 3 = 1 := by
      have h : c3 ^ 3 = 1 := orderOf_c3 ▸ pow_orderOf_eq_one c3
      rw [← map_pow, h, map_one]
    have h1 : 1 + ρ (ι.symm c3) + ρ (ι.symm c3) ^ 2 = 0 :=
      one_add_add_sq_eq_zero ρ hc3 (hcen ▸ hz) hfix
    obtain ⟨v, hv, hv'⟩ := exists_fixed_model3_of_char identD
      (orderOf_e3 ▸ pow_orderOf_eq_one e3) hq hq7 (ρ.comp ι.symm.toMonoidHom) h1
    have hcard : ¬ 25 ∣ Nat.card K := by
      rw [card_eq_of_isAlt6_quot hA, hZ]
      norm_num
    exact exists_fixed_of_orderOf_eq_five hcard ρ (e₀ := ι.symm e3)
      (by rw [MulEquiv.orderOf_eq, orderOf_e3]) he hv hv'
  · obtain ⟨ι⟩ := nonempty_mulEquiv_model6 hqs hZ hA
    have hcen : center K = zpowers (ι.symm c6) :=
      center_eq_zpowers_of_mulEquiv ι model6_facts.2.2.2.2 (by rw [orderOf_c6, hZ])
    have hz' : z ∈ zpowers (ι.symm z6) := by
      have h := mem_zpowers_sq_of_orderOf_eq_three (g := ι.symm c6)
        (by rw [MulEquiv.orderOf_eq, orderOf_c6]) (hcen ▸ hz) hz3
      rwa [← map_pow] at h
    have hz6 : ι.symm z6 ^ 3 = 1 := by
      have h : z6 ^ 3 = 1 := orderOf_z6 ▸ pow_orderOf_eq_one z6
      rw [← map_pow, h, map_one]
    have h1 : 1 + ρ (ι.symm z6) + ρ (ι.symm z6) ^ 2 = 0 :=
      one_add_add_sq_eq_zero ρ hz6 hz' hfix
    obtain ⟨v, hv, hv'⟩ := exists_fixed_model6_of_char identE
      (orderOf_e6 ▸ pow_orderOf_eq_one e6) hq hq7 (ρ.comp ι.symm.toMonoidHom) h1
    have hcard : ¬ 25 ∣ Nat.card K := by
      rw [card_eq_of_isAlt6_quot hA, hZ]
      norm_num
    exact exists_fixed_of_orderOf_eq_five hcard ρ (e₀ := ι.symm e6)
      (by rw [MulEquiv.orderOf_eq, orderOf_e6]) he hv hv'

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
