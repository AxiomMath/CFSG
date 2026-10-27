module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165SylB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin CFSG.ABGLocalTools
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem finite_mulAut_carrier (S : OmegaModel W) : Finite (MulAut W) := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by
    rw [S.card_eq]
    exact pow_ne_zero 4 Nat.card_pos.ne')
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

theorem not_two_pow_eight_dvd_card (hK : Nat.card S.K = 8) {B : Subgroup (MulAut W)}
    (hBN : B ≤ omegaNorm S) : ¬ 2 ^ 8 ∣ Nat.card B := by
  haveI := S.finite_mulAut_carrier
  intro h
  have h1 : Nat.card B ∣ Nat.card ↥(omegaNorm S) := Subgroup.card_dvd_of_le hBN
  have h2 : Nat.card ↥(omegaNorm S) ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := card_omegaNorm_dvd S hK
  have h3 : 2 ^ 8 ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := h.trans (h1.trans h2)
  obtain ⟨c, hc⟩ := h3
  omega

theorem isSylowOf_two_t0Sub (hK : Nat.card S.K = 8) {B : Subgroup (MulAut W)}
    (hΩB : S.omega ≤ B) (hBN : B ≤ omegaNorm S) (ht : tAut S ∈ B) :
    IsSylowOf 2 (t0Sub S) B := by
  haveI := S.finite_mulAut_carrier
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT0 : t0Sub S ≤ B :=
    sup_le ((u0Sub_le_omega0 S).trans ((omega0_le_omega S).trans hΩB))
      (Subgroup.zpowers_le.mpr ht)
  rw [isSylowOf_iff]
  refine ⟨hT0, isPGroup_two_t0Sub S hK, ?_⟩
  intro h2
  have hmul := Subgroup.relIndex_mul_card (H := t0Sub S) (K := B)
  rw [inf_eq_left.mpr hT0, card_t0Sub S hK] at hmul
  have h8 : 2 ^ 8 ∣ Nat.card B := by
    rw [← hmul]
    obtain ⟨c, hc⟩ := h2
    rw [hc]
    exact ⟨c, by ring⟩
  exact not_two_pow_eight_dvd_card S hK hBN h8

theorem inf_isoSub_eq_omega (hK : Nat.card S.K = 8) (hΩ : Nat.card S.omega = 254016)
    {B : Subgroup (MulAut W)} (hΩB : S.omega ≤ B) (ht : tAut S ∉ B) :
    B ⊓ isoSub S = S.omega := by
  haveI := S.finite_mulAut_carrier
  refine le_antisymm ?_ (le_inf hΩB (omega_le_isoSub S))
  intro x hx
  by_contra hxω
  have hxI : x ∈ isoSub S := hx.2
  have hxB : x ∈ B := hx.1
  let I : Subgroup (MulAut W) := isoSub S
  let H : Subgroup ↥I := S.omega.subgroupOf I
  have hHcard : Nat.card ↥H = 254016 := by
    have h := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (omega_le_isoSub S)).toEquiv
    rw [h, hΩ]
  have hIcard : Nat.card ↥I = 508032 := card_isoSub S hK
  have hHindex : H.index = 2 := by
    have hmul := Subgroup.card_mul_index H
    rw [hHcard, hIcard] at hmul
    omega
  obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff).mp hHindex
  let t' : ↥I := ⟨tAut S, tAut_mem_isoSub S⟩
  let x' : ↥I := ⟨x, hxI⟩
  have ht' : t' ∉ H := by
    intro h
    exact ht (hΩB (Subgroup.mem_subgroupOf.mp h))
  have hx' : x' ∉ H := by
    intro h
    exact hxω (Subgroup.mem_subgroupOf.mp h)
  have h1 : t' * a ∈ H := by
    rcases ha t' with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h ht'
  have h2 : x' * a ∈ H := by
    rcases ha x' with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hx'
  have h3 : t' * x'⁻¹ ∈ H := by
    have h4 : (t' * a) * (x' * a)⁻¹ = t' * x'⁻¹ := by group
    rw [← h4]
    exact mul_mem h1 (inv_mem h2)
  have h5 : tAut S * x⁻¹ ∈ S.omega := by
    have h := Subgroup.mem_subgroupOf.mp h3
    simpa [t', x'] using h
  have h6 : tAut S = (tAut S * x⁻¹) * x := by group
  refine ht ?_
  rw [h6]
  exact mul_mem (hΩB h5) hxB

theorem isSylowOf_two_u0Sub (hK : Nat.card S.K = 8) (hΩ : Nat.card S.omega = 254016)
    {B : Subgroup (MulAut W)} (hΩB : S.omega ≤ B) (hBN : B ≤ omegaNorm S) (ht : tAut S ∉ B) :
    IsSylowOf 2 (u0Sub S) B := by
  haveI := S.finite_mulAut_carrier
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥B := Finite.of_injective (Subtype.val) Subtype.coe_injective
  have hUB : u0Sub S ≤ B :=
    (u0Sub_le_omega0 S).trans ((omega0_le_omega S).trans hΩB)
  rw [isSylowOf_iff]
  refine ⟨hUB, isPGroup_two_u0Sub S, ?_⟩
  intro h2
  have hmul := Subgroup.relIndex_mul_card (H := u0Sub S) (K := B)
  rw [inf_eq_left.mpr hUB, card_u0Sub S hK] at hmul
  have h27 : 2 ^ 7 ∣ Nat.card B := by
    rw [← hmul]
    obtain ⟨c, hc⟩ := h2
    rw [hc]
    exact ⟨c, by ring⟩
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥B) 2 (n := 7) h27
  have hK'card : Nat.card ↥(K.map B.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective, hKcard]
  have hK'P : IsPGroup 2 ↥(K.map B.subtype) := IsPGroup.of_card hK'card
  have hK'B : K.map B.subtype ≤ B := Subgroup.map_subtype_le K
  have hK'N : K.map B.subtype ≤ omegaNorm S := hK'B.trans hBN
  have hK'iso : K.map B.subtype ≤ isoSub S :=
    le_isoSub_of_isPGroup S hK Nat.prime_two (by norm_num) (by norm_num) hK'P hK'N
  have hK'omega : K.map B.subtype ≤ S.omega := by
    rw [← inf_isoSub_eq_omega S hK hΩ hΩB ht]
    exact le_inf hK'B hK'iso
  have hdiv : 2 ^ 7 ∣ Nat.card S.omega := by
    rw [← hK'card]
    exact Subgroup.card_dvd_of_le hK'omega
  rw [hΩ] at hdiv
  obtain ⟨c, hc⟩ := hdiv
  omega

theorem exists_isSylowOf_two_normalized_by_seven (hK : Nat.card S.K = 8)
    (hΩ : Nat.card S.omega = 254016) {B : Subgroup (MulAut W)} (hΩB : S.omega ≤ B)
    (hBN : B ≤ omegaNorm S) :
    ∃ (T' : Subgroup (MulAut W)) (d : SL(2, S.K)), T' ≤ B ∧ T' ≤ isoSub S ∧
      IsSylowOf 2 T' B ∧ orderOf (S.jHom (d, d)) = 7 ∧
      S.jHom (d, d) ∈ Subgroup.normalizer (T' : Set (MulAut W)) := by
  obtain ⟨d, hd7, hdN⟩ := exists_diag_mem_normalizer_u0Sub S hK
  have hU : u0Sub S ≤ S.omega := (u0Sub_le_omega0 S).trans (omega0_le_omega S)
  by_cases ht : tAut S ∈ B
  · refine ⟨t0Sub S, d, ?_, t0Sub_le_isoSub S, isSylowOf_two_t0Sub S hK hΩB hBN ht, hd7,
      mem_normalizer_t0Sub_of_commute S hdN (commute_jHom_diag_tAut S d)⟩
    exact sup_le (hU.trans hΩB) (Subgroup.zpowers_le.mpr ht)
  · exact ⟨u0Sub S, d, hU.trans hΩB, hU.trans (omega_le_isoSub S),
      isSylowOf_two_u0Sub S hK hΩ hΩB hBN ht, hd7, hdN⟩

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
