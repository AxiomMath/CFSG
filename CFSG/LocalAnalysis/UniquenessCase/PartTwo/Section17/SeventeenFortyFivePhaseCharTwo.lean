module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhasePermute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2GlueHolds
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

section Main


theorem inf_le_normalizer_of_lieModel_two {X : Type} [Group X] [Finite X] {L A T : Subgroup X}
    (hL : L.Normal) {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hmod : CFSG.Blueprint.LieModel ↥L t n 2 f) {r : ℕ} (hr : r.Prime) (hr3 : r % 3 = 1)
    (hr13 : r ≠ 13) (hA : IsPGroup r A) (hT : IsPGroup 2 T) (hperm : Permutes A T)
    (hTL : IsSylowOf 2 (T ⊓ L) L) :
    A ⊓ L ≤ normalizer ((T ⊓ L : Subgroup X) : Set X) := by
  have : Fact r.Prime := ⟨hr⟩
  have hrodd : Odd r := hr.odd_of_ne_two (by rintro rfl; norm_num at hr3)
  have hAodd : Odd (Nat.card A) := by
    obtain ⟨m, hm⟩ := hA.exists_card_eq
    rw [hm]
    exact hrodd.pow
  by_cases ht : t = .Tits
  ·
    subst ht
    have hr7 : 7 ≤ r := by
      have h4 : r ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hr
      have := hr.two_le
      omega
    have hnotdvd : ¬ r ∣ Nat.card ↥L :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.not_dvd_card_of_lieModel_tits
        hmod hr hr7 hr13
    have hcard : Nat.card ↥(A ⊓ L) = 1 := by
      obtain ⟨m, hm⟩ := (hA.to_le inf_le_left).exists_card_eq
      have hdvd : r ^ m ∣ Nat.card ↥L := hm ▸ Subgroup.card_dvd_of_le inf_le_right
      have hm0 : m = 0 := by
        by_contra h
        exact hnotdvd (dvd_trans (dvd_pow_self r h) hdvd)
      rw [hm, hm0, pow_zero]
    rw [Subgroup.card_eq_one.mp hcard]
    exact bot_le
  ·
    obtain ⟨B, N, hBN⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hmod
    have hperm' : Permutes (A ⊓ L) (T ⊓ L) :=
      permutes_inf_inf_of_permutes hL hAodd hT hperm
    obtain ⟨Q, hQ⟩ := hTL
    have hQ' : (Q : Subgroup ↥L) = (T ⊓ L).subgroupOf L := by
      rw [← hQ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
    obtain ⟨i, hi⟩ := (hA.to_le inf_le_left).exists_card_eq
    have hE'card : Nat.card ↥((A ⊓ L).subgroupOf L) = r ^ i := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hi]
    have hE'odd : Odd (Nat.card ↥((A ⊓ L).subgroupOf L)) := by
      rw [hE'card]
      exact hrodd.pow
    have hEQ : Permutes ((A ⊓ L).subgroupOf L) (Q : Subgroup ↥L) := by
      rw [hQ']
      exact CFSG.Quasithin.H.Tri.subgroupOf_mul_comm inf_le_right inf_le_right hperm'
    rcases le_normalizer_or_fermat_dvd_of_splitBN hBN Q hE'odd hEQ with h | ⟨k, -, hkdvd⟩
    · have h1 := Subgroup.map_mono (f := L.subtype) h
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right] at h1
      calc A ⊓ L ≤ (normalizer ((Q : Subgroup ↥L) : Set ↥L)).map L.subtype := h1
        _ ≤ normalizer (((Q : Subgroup ↥L).map L.subtype : Subgroup X) : Set X) :=
            Subgroup.le_normalizer_map _
        _ = normalizer ((T ⊓ L : Subgroup X) : Set X) := by rw [hQ]
    · exact absurd (hE'card ▸ hkdvd) (two_pow_add_one_not_dvd_prime_pow hr hr3 k i)


theorem k45CharTwoNormal_holds : K45CharTwoNormal := by
  intro X _ _ L A₁ A₂ B T d hLn hcent hLd hd hdt hA₁ hA₂ hA₁₂ hc hB hBA₁ hBA₂ hcomm hT hperm
    hTL
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hA₁p : IsPGroup 31 A₁ := IsPGroup.of_card (n := 1) (by rw [hA₁, pow_one])
  have hA₂p : IsPGroup 31 A₂ := IsPGroup.of_card (n := 1) (by rw [hA₂, pow_one])
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set X) :=
    hc.trans (Subgroup.centralizer_le_normalizer _)
  have hsup : IsPGroup 31 ↥(A₁ ⊔ A₂) :=
    IsPGroup.to_sup_of_normal_right' hA₁p hA₂p hnorm
  have hodd : Odd (Nat.card ↥(A₁ ⊔ A₂)) := by
    obtain ⟨m, hm⟩ := hsup.exists_card_eq
    rw [hm]
    exact Odd.pow (by norm_num : Odd 31)
  have hperm' : Permutes (A₁ ⊔ A₂) T := hperm
  obtain ⟨e⟩ := hLd
  obtain ⟨t, n, f, hmod⟩ := CFSG.StandardType.ChevTwo.exists_lieModel_two_of_valid d hd e
  exact le_normalizer_inf_of_permutes_of_inf_le hLn hodd hT hperm'
    (inf_le_normalizer_of_lieModel_two hLn hmod (by norm_num) (by norm_num) (by norm_num)
      hsup hT hperm' hTL)

end Main

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

end
