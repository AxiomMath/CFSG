module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91GammaDefs
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

private theorem r891_subgroupOf_center_eq_ga {Y : Type} [Group Y] [Finite Y]
    {R : Subgroup Y}
    (hZ : Nat.card (center Y) = 3) (hR : IsExtraspecialExpP 3 1 ↥R) (hZR : center Y ≤ R) :
    (center Y).subgroupOf R = center R := by
  obtain ⟨-, -, -, hRcenter⟩ := hR
  have hle : (center Y).subgroupOf R ≤ center R := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hx) (y : Y))
  have hcard : Nat.card ((center Y).subgroupOf R) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv, hZ]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hRcenter])

private theorem r891_card_map_ga {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    (hZR : center Y ≤ R) :
    Nat.card (R.map (QuotientGroup.mk' (center Y))) * Nat.card (center Y) = Nat.card R := by
  let φ : R →* Y ⧸ center Y := (QuotientGroup.mk' (center Y)).comp R.subtype
  have hker : MonoidHom.ker φ = (center Y).subgroupOf R := by
    ext x
    simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.coe_subtype]
  have hrange : φ.range = R.map (QuotientGroup.mk' (center Y)) := by
    ext y
    simp only [φ, MonoidHom.mem_range, MonoidHom.comp_apply, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hcard : Nat.card (MonoidHom.ker φ) * Nat.card φ.range = Nat.card R :=
    Subgroup.card_ker_mul_card_range φ
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv] at hcard
  simpa only [Nat.mul_comm] using hcard

theorem r891_rbar {Y : Type} [Group Y] [Finite Y] (hZ : Nat.card (center Y) = 3) {R : Subgroup Y}
    (hR : IsExtraspecialExpP 3 1 ↥R) (hZR : center Y ≤ R) :
    IsElemAbelian 3 (R.map (QuotientGroup.mk' (center Y))) ∧
      Nat.card (R.map (QuotientGroup.mk' (center Y))) = 9 := by
  have hcenter : (center Y).subgroupOf R = center R :=
    r891_subgroupOf_center_eq_ga hZ hR hZR
  obtain ⟨hRcard, hRexp, hRcomm, -⟩ := hR
  have hcardR : Nat.card R = 27 := by
    rw [hRcard]
    norm_num
  have hcard := r891_card_map_ga (Y := Y) (R := R) hZR
  rw [hcardR, hZ] at hcard
  have hE9 : Nat.card (R.map (QuotientGroup.mk' (center Y))) = 9 := by omega
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, hE9⟩
  · obtain ⟨x, hxR, hx⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨y, hyR, hy⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    show a.1 * b.1 = b.1 * a.1
    rw [← hx, ← hy]
    have hmem : x * y * (y * x)⁻¹ ∈ center Y := by
      have h1 : (⟨x, hxR⟩ : R) * ⟨y, hyR⟩ * (⟨x, hxR⟩ : R)⁻¹ * ⟨y, hyR⟩⁻¹ ∈ center R := by
        have h2 := Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
          (Subgroup.mem_top (⟨x, hxR⟩ : R)) (Subgroup.mem_top (⟨y, hyR⟩ : R))
        rw [← _root_.commutator_def, hRcomm] at h2
        simpa only [commutatorElement_def] using h2
      rw [← hcenter] at h1
      rw [Subgroup.mem_subgroupOf] at h1
      have hval : Subtype.val ((⟨x, hxR⟩ : R) * ⟨y, hyR⟩ * (⟨x, hxR⟩ : R)⁻¹ *
          ⟨y, hyR⟩⁻¹) = x * y * (y * x)⁻¹ := by
        show x * y * x⁻¹ * y⁻¹ = x * y * (y * x)⁻¹
        group
      rwa [hval] at h1
    have hprod : (QuotientGroup.mk' (center Y)) x * (QuotientGroup.mk' (center Y)) y *
        ((QuotientGroup.mk' (center Y)) y * (QuotientGroup.mk' (center Y)) x)⁻¹ = 1 := by
      rw [show (QuotientGroup.mk' (center Y)) x * (QuotientGroup.mk' (center Y)) y *
          ((QuotientGroup.mk' (center Y)) y * (QuotientGroup.mk' (center Y)) x)⁻¹ =
          (QuotientGroup.mk' (center Y)) (x * y * (y * x)⁻¹) by
        rw [map_mul, map_mul, map_inv, map_mul]]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    exact mul_inv_eq_one.mp hprod
  · intro a ha
    obtain ⟨x, hxR, hx⟩ := Subgroup.mem_map.mp ha
    have hx3 : x ^ 3 = 1 := by
      have h : (⟨x, hxR⟩ : R) ^ 3 = 1 := by
        have h := Monoid.pow_exponent_eq_one (⟨x, hxR⟩ : R)
        rwa [hRexp] at h
      simpa using congrArg Subtype.val h
    rw [← hx, ← map_pow, hx3, map_one]

theorem r891GammaList_of (hA7 : R891GammaA7) (hM22 : R891GammaM22) (hL3 : R891GammaL3)
    (hU3 : R891GammaU3) :
    ∀ (Y : Type) [Group Y] [Finite Y], R891List896 Y → ∀ R : Subgroup Y,
      IsExtraspecialExpP 3 1 ↥R → center Y ≤ R →
      rankThreeGamma 1 3 (R.map (QuotientGroup.mk' (center Y))) ≠ ⊤ → R891List897 Y := by
  intro Y _ _ hY R hR hZR hΓ
  rcases hY with ⟨hQ6, hZ6, hIsA6⟩ | ⟨hQ7, hZ7, hIsA7⟩ | ⟨hQ22, hZ22, hIsM22⟩ |
    (⟨p, f, hq, hQ, hZ3, hL⟩ | ⟨p, f, hq, hQ, hZ3, hL⟩) | ⟨hQON, hZON, hONz⟩
  · exact Or.inl ⟨hQ6, hZ6, hIsA6⟩
  · obtain ⟨hEab, hE9⟩ := r891_rbar hZ7 hR hZR
    exact absurd (hA7 (Y ⧸ center Y) hIsA7 _ hEab hE9) hΓ
  · obtain ⟨hEab, hE9⟩ := r891_rbar hZ22 hR hZR
    exact absurd (hM22 (Y ⧸ center Y) hIsM22 _ hEab hE9) hΓ
  · obtain ⟨hEab, hE9⟩ := r891_rbar hZ3 hR hZR
    by_cases h4 : p ^ f = 4
    · have hadm := CFSG.Blueprint.LieModel.admissible hL
      have hp : p.Prime := hadm.1
      have hf : 1 ≤ f := hadm.2.1
      have hp4 : p ∣ 4 := h4 ▸ dvd_pow_self p (by omega)
      have hp2 : p ∣ 2 := by
        apply hp.dvd_of_dvd_pow (n := 2)
        simpa using hp4
      have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2
      subst hpeq
      have hfeq : f = 2 := by
        have hpow : 2 ^ f = 2 ^ 2 := by
          rw [h4]
          norm_num
        exact Nat.pow_right_injective (a := 2) le_rfl hpow
      subst hfeq
      exact Or.inr (Or.inl ⟨hQ, hZ3, hL⟩)
    · exact absurd (hL3 (Y ⧸ center Y) p f hq h4 hL _ hEab hE9) hΓ
  · obtain ⟨hEab, hE9⟩ := r891_rbar hZ3 hR hZR
    exact absurd (hU3 (Y ⧸ center Y) p f hq hL _ hEab hE9) hΓ
  · exact Or.inr (Or.inr ⟨hQON, hZON, hONz⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
