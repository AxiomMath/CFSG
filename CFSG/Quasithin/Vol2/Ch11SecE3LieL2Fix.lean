module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.CGT.Timmesfeld75.L2Sylow
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch11SecCFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b CFSG.CGT
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner congr_conj)
open scoped MatrixGroups

section Field

variable {K : Type} [Field K] [Finite K]

theorem card_eqLocusField_sq_le {σ : K ≃+* K} (hσ : σ ≠ 1) :
    Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) ^ 2 ≤ Nat.card K := by
  classical
  set S := σ.toRingHom.eqLocusField (RingHom.id K) with hS
  have := Fintype.ofFinite K
  have hd : 2 ≤ Module.finrank S K := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < Module.finrank S K := Module.finrank_pos
    have h1 : Module.finrank S K = 1 := by omega
    apply hσ
    ext x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).mp h1 x
    have hcS : σ (c : K) = (c : K) := RingHom.mem_eqLocusField.mp c.2
    rw [← hc, Algebra.smul_def, mul_one]
    exact hcS
  have hcard : Nat.card K = Nat.card S ^ Module.finrank S K := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ↥S) (V := K)]
  rw [hcard]
  exact Nat.pow_le_pow_right Nat.card_pos hd

theorem card_le_card_eqLocusField {ι : Type*} [Finite ι] {σ : K ≃+* K} {d : K} (f : ι → K)
    (hf : Function.Injective f) (hX : ∀ i, d ^ 2 * σ (f i) = f i) :
    Nat.card ι ≤ Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) := by
  classical
  by_cases h0 : ∃ i, f i ≠ 0
  · obtain ⟨i₀, hi₀⟩ := h0
    have hd : d ≠ 0 := by
      rintro rfl
      apply hi₀
      rw [← hX i₀]
      ring
    have hmem : ∀ i, f i * (f i₀)⁻¹ ∈ σ.toRingHom.eqLocusField (RingHom.id K) := by
      intro i
      rw [RingHom.mem_eqLocusField, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingHom.id_apply, map_mul, map_inv₀]
      have h1 : σ (f i) = f i / d ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 hd), mul_comm, hX i]
      have h2 : σ (f i₀) = f i₀ / d ^ 2 := by
        rw [eq_div_iff (pow_ne_zero 2 hd), mul_comm, hX i₀]
      rw [h1, h2]
      field_simp
    refine Nat.card_le_card_of_injective (fun i => ⟨f i * (f i₀)⁻¹, hmem i⟩) fun i j hij => ?_
    have h := congrArg Subtype.val hij
    simp only at h
    exact hf (mul_right_cancel₀ (inv_ne_zero hi₀) h)
  · push Not at h0
    have : Subsingleton ι := ⟨fun i j => hf (by rw [h0 i, h0 j])⟩
    have h1 : Nat.card ι ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr this
    exact h1.trans Nat.card_pos

theorem two_le_card_eqLocusField (σ : K ≃+* K) :
    2 ≤ Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) :=
  Finite.one_lt_card

end Field

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem slFieldAut_utriElt (σ : K ≃+* K) (x : K) :
    slFieldAut K σ (Timmesfeld75.utriElt x) = Timmesfeld75.utriElt (σ x) := by
  refine Timmesfeld75.sl2_ext ?_ ?_ ?_ ?_ <;>
    simp [slFieldAut_apply, Timmesfeld75.utriElt_apply_00, Timmesfeld75.utriElt_apply_01,
      Timmesfeld75.utriElt_apply_10, Timmesfeld75.utriElt_apply_11]

theorem card_le_of_fixed_sl2 {M : SL(2, K)} {σ : K ≃+* K} {B : Subgroup SL(2, K)}
    (hB : IsPGroup 2 B)
    (hfix : ∀ y ∈ B, (MulAut.conj M * slFieldAut K σ) y = y) :
    Nat.card B ≤ Nat.card (σ.toRingHom.eqLocusField (RingHom.id K)) := by
  classical
  obtain ⟨Q, hBQ⟩ := hB.exists_le_sylow
  obtain ⟨h₀, hQ⟩ := Timmesfeld75.exists_conjSubgroup_utri_eq_of_sylow Q
  set M' : SL(2, K) := h₀⁻¹ * M * slFieldAut K σ h₀ with hM'
  have hzU : ∀ y ∈ B, h₀⁻¹ * y * h₀ ∈ Timmesfeld75.utri K := by
    intro y hy
    have hyQ : y ∈ (Q : Subgroup SL(2, K)) := hBQ hy
    rw [← hQ, Timmesfeld75.mem_conjSubgroup] at hyQ
    exact hyQ
  have hz : ∀ y ∈ B, M' * slFieldAut K σ (h₀⁻¹ * y * h₀) * M'⁻¹ = h₀⁻¹ * y * h₀ := by
    intro y hy
    have h1 : M * slFieldAut K σ y * M⁻¹ = y := by
      have := hfix y hy
      rwa [MulAut.mul_apply, MulAut.conj_apply] at this
    rw [hM', map_mul, map_mul, map_inv]
    calc h₀⁻¹ * M * slFieldAut K σ h₀ *
          ((slFieldAut K σ h₀)⁻¹ * slFieldAut K σ y * slFieldAut K σ h₀) *
          (h₀⁻¹ * M * slFieldAut K σ h₀)⁻¹
        = h₀⁻¹ * (M * slFieldAut K σ y * M⁻¹) * h₀ := by group
      _ = h₀⁻¹ * y * h₀ := by rw [h1]
  set f : ↥B → K := fun y => (h₀⁻¹ * (y : SL(2, K)) * h₀) 0 1 with hf
  have hutri : ∀ y : ↥B, h₀⁻¹ * (y : SL(2, K)) * h₀ = Timmesfeld75.utriElt (f y) := fun y =>
    Timmesfeld75.eq_utriElt_of_mem_utri (hzU y y.2)
  have hfinj : Function.Injective f := by
    intro y y' hyy
    have h1 : h₀⁻¹ * (y : SL(2, K)) * h₀ = h₀⁻¹ * (y' : SL(2, K)) * h₀ := by
      rw [hutri, hutri, hyy]
    exact Subtype.ext (by simpa using h1)
  refine card_le_card_eqLocusField (d := M' 0 0) f hfinj fun y => ?_
  have h1 := hz y y.2
  rw [hutri y, slFieldAut_utriElt] at h1
  have h2 : (M' * Timmesfeld75.utriElt (σ (f y)) * M'⁻¹) 0 1 =
      (Timmesfeld75.utriElt (f y) : SL(2, K)) 0 1 := by rw [h1]
  rw [Timmesfeld75.conj_utriElt_apply_01, Timmesfeld75.utriElt_apply_01] at h2
  exact h2

end Model

end CFSG.Quasithin.Vol2.Ch11.SecE3
