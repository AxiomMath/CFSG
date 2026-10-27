module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem card_dvd_three_of_isPGroup {L R : Subgroup G} (hA5 : IsAlt (Bar2 L) 5)
    (hR : IsPGroup 3 ↥R) (hRL : R ≤ L) : Nat.card R ∣ 3 := by
  classical
  have h3fact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥R →* Bar2 L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hRL)
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [MonoidHom.mem_ker] at hx
    have hpc : (Subgroup.inclusion hRL x : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).1 hx
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hpc⟩
    obtain ⟨b, hb⟩ := hR x
    have h2 : (x : G) ^ 2 ^ a = 1 := by
      simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => (((y : ↥L) : G))) ha
    have h3 : (x : G) ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [(Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)).gcd_eq_one] at hd
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd))
  have hcard : Nat.card ↥R = Nat.card ↥f.range := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker, Subgroup.card_bot, one_mul] at h
    exact h.symm
  have hdiv : Nat.card ↥R ∣ 60 := by
    rw [hcard, ← CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.card_bar2_of_isAlt_five hA5]
    exact Subgroup.card_subgroup_dvd_card f.range
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR
  rw [hk] at hdiv ⊢
  have hk1 : k ≤ 1 := by
    by_contra h
    push Not at h
    have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
    have h96 : 3 ^ 2 ∣ 60 := h9.trans hdiv
    norm_num at h96
  interval_cases k <;> norm_num

theorem exists_cyclic_hom_of_le_normalizer {L P : Subgroup G} (hA5 : IsAlt (Bar2 L) 5)
    (hP : IsPGroup 3 ↥P) (hPN : P ≤ normalizer (L : Set G)) :
    ∃ (Q : Type) (_ : Group Q) (φ : ↥P →* Q), IsCyclic Q ∧
      ∀ x : ↥P, (x : G) ∈ L → φ x = 1 → x = 1 := by
  classical
  have h3fact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hA5
  let f : ↥P →* MulAut (Bar2 L) := (UC6S846.rhoL L).comp (Subgroup.inclusion hPN)
  have hP' : IsPGroup 3 ↥f.range :=
    hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have h120 : Nat.card (MulAut (Bar2 L)) = 120 :=
    CFSG.RankThree.PartTwo.KFacts.KS166.card_mulAut_of_alt5 e
  have hdiv : Nat.card ↥f.range ∣ 120 := by
    rw [← h120]
    exact Subgroup.card_subgroup_dvd_card f.range
  have hcard3 : Nat.card ↥f.range ∣ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP'
    rw [hk] at hdiv ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      push Not at h
      have h9 : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
      have h96 : 3 ^ 2 ∣ 120 := h9.trans hdiv
      norm_num at h96
    interval_cases k <;> norm_num
  refine ⟨↥f.range, inferInstance, f.rangeRestrict, ?_, ?_⟩
  · rcases (Nat.dvd_prime Nat.prime_three).1 hcard3 with h | h
    · have hsub : Subsingleton ↥f.range := (Nat.card_eq_one_iff_unique.1 h).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card h
  · intro x hxL hx1
    have hx1' : f x = 1 := by simpa using congrArg Subtype.val hx1
    have hf : f x = UC6S846.rhoL L ⟨x, hPN x.2⟩ := rfl
    rw [hf, UC6S846.rhoL_inner L x hxL] at hx1'
    have hcomm : ∀ y : Bar2 L,
        (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * y = y *
          (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by
      intro y
      have h := DFunLike.congr_fun hx1' y
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * y
          = ((QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) * y *
              (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L)⁻¹) *
              (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by group
        _ = y * (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by rw [h]
    have hq1 : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) = 1 :=
      CFSG.RankThree.PartTwo.KFacts.KS166.eq_one_of_commute_alt5 e hcomm
    have hpc : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).1 hq1
    obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hpc⟩
    obtain ⟨b, hb⟩ := hP x
    have h2 : (x : G) ^ 2 ^ a = 1 := by
      simpa using congrArg (fun y : ↥(CFSG.pCore 2 ↥L) => (((y : ↥L) : G))) ha
    have h3 : (x : G) ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    rw [(Nat.Coprime.pow a b (by norm_num : Nat.Coprime 2 3)).gcd_eq_one] at hd
    exact Subtype.ext (orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
