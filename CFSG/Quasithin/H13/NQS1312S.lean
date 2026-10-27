module

public import CFSG.Quasithin.H13.NQS1312T

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup
open scoped IsMulCommutative

variable {G : Type} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]
  {Φ : Additive V ≃ₗ[ZMod 2] W6}

@[expose] noncomputable def tau (Φ : Additive V ≃ₗ[ZMod 2] W6) :
    normalizer (V : Set G) →* GL (Fin 6) (ZMod 2) :=
  glLin.symm.toMonoidHom.comp
    ((linConj Φ).toMonoidHom.comp (u3ConjLin V (normalizer (V : Set G)) le_rfl))

theorem tau_eq_iff {n : normalizer (V : Set G)} {k : GL (Fin 6) (ZMod 2)} :
    tau Φ n = k ↔ linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k := by
  unfold tau
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  constructor
  · rintro rfl
    exact (MulEquiv.apply_symm_apply _ _).symm
  · intro h
    rw [h, MulEquiv.symm_apply_apply]

theorem tau_eq_one_iff {n : normalizer (V : Set G)} :
    tau Φ n = 1 ↔ (n : G) ∈ centralizer (V : Set G) := by
  rw [tau_eq_iff, map_one]
  constructor
  · intro h
    exact (u3ConjLin_eq_one_iff n).1 ((linConj Φ).injective (h.trans (map_one _).symm))
  · intro h
    rw [(u3ConjLin_eq_one_iff n).2 h, map_one]

theorem false_of_pow_two_pow {κ : GL (Fin 6) (ZMod 2)} {f : List ℕ}
    (hf : (κ : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat f) (h3 : mul6 f (mul6 f f) = id6)
    (hv : ∃ v < 64, vapp f v ≠ v ∧ vapp f v < 64) {m : ℕ} (hm : κ ^ 2 ^ m = 1) : False := by
  have hk3 : κ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hf, pow_three, ← colMat_mul6, ← colMat_mul6, h3,
      colMat_id6]
  have hcop : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  have hk1 : κ = 1 := by
    have := (pow_gcd_eq_one (a := κ) (m := 2 ^ m) (n := 3)).2 ⟨hm, hk3⟩
    rwa [hcop, pow_one] at this
  obtain ⟨v, hv64, hvne, hvlt⟩ := hv
  have h1 := glLin_vecOf_of_coe hf v
  rw [hk1, map_one] at h1
  exact hvne (vecOf_injective hvlt hv64 h1.symm)

theorem false_of_tau_order_three [Finite G] {R : Subgroup G} (hR : IsPGroup 2 R) {g : G}
    (hg : g ∈ R) (hgN : g ∈ normalizer (V : Set G)) {f : List ℕ}
    (hf : ((tau Φ ⟨g, hgN⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat f)
    (h3 : mul6 f (mul6 f f) = id6) (hv : ∃ v < 64, vapp f v ≠ v ∧ vapp f v < 64) : False := by
  obtain ⟨m, hm⟩ := hR ⟨g, hg⟩
  have hgm : g ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hnm : (⟨g, hgN⟩ : normalizer (V : Set G)) ^ 2 ^ m = 1 :=
    Subtype.ext (by simpa using hgm)
  refine false_of_pow_two_pow hf h3 hv (m := m) ?_
  rw [← map_pow, hnm, map_one]

theorem le_centralizer_of_isPGroup [Finite G]
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    {k₁ : G} (hk₁ : k₁ ∈ normalizer (V : Set G)) (hk₁τ : tau Φ ⟨k₁, hk₁⟩ = kGL)
    {R : Subgroup G} (hR : IsPGroup 2 R) (hRN : R ≤ normalizer (V : Set G))
    (hRc : ∀ r ∈ R, r * ptOf Φ (vecOf 15) * r⁻¹ = ptOf Φ (vecOf 15) ∧
      r * ptOf Φ (vecOf 52) * r⁻¹ = ptOf Φ (vecOf 52))
    (hkR : ∀ r ∈ R, k₁ * r * k₁⁻¹ ∈ R) : R ≤ centralizer (V : Set G) := by
  intro r hr
  obtain ⟨κ, -, hκ, e, he, hκe⟩ :=
    exists_c6List_of_centralizes hΦN (hRN hr) (hRc r hr).1 (hRc r hr).2
  have hτr : tau Φ ⟨r, hRN hr⟩ = κ := tau_eq_iff.2 hκ
  rcases c6List_cases e he with rfl | ⟨h3, hv⟩ | ⟨h3, hv⟩
  ·
    have hκ1 : κ = 1 := Units.ext (by rw [hκe, colMat_id6, Units.val_one])
    rw [hκ1] at hτr
    exact tau_eq_one_iff.1 hτr
  · exact (false_of_tau_order_three hR hr (hRN hr) (by rw [hτr]; exact hκe) h3 hv).elim
  ·
    exfalso
    have hr' : r * (k₁ * r * k₁⁻¹) ∈ R := mul_mem hr (hkR r hr)
    have hN' : r * (k₁ * r * k₁⁻¹) ∈ normalizer (V : Set G) :=
      mul_mem (hRN hr) (mul_mem (mul_mem hk₁ (hRN hr)) (inv_mem hk₁))
    have hk3 : (kGL : Matrix (Fin 6) (Fin 6) (ZMod 2)) ^ 3 = 1 := by
      rw [coe_kGL, pow_three, ← colMat_mul6, ← colMat_mul6, kc_order.1, colMat_id6]
    have hkinv : ((kGL⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        colMat (mul6 kc kc) := by
      have h1 : kGL⁻¹ = kGL * kGL := by
        rw [inv_eq_iff_mul_eq_one]
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, Units.val_one, ← pow_three, hk3]
      rw [h1, Units.val_mul, coe_kGL, colMat_mul6]
    have hτ' : tau Φ ⟨r * (k₁ * r * k₁⁻¹), hN'⟩ = κ * (kGL * κ * kGL⁻¹) := by
      have : (⟨r * (k₁ * r * k₁⁻¹), hN'⟩ : normalizer (V : Set G)) =
          ⟨r, hRN hr⟩ * (⟨k₁, hk₁⟩ * ⟨r, hRN hr⟩ * ⟨k₁, hk₁⟩⁻¹) := rfl
      rw [this, map_mul, map_mul, map_mul, map_inv, hτr, hk₁τ]
    refine false_of_tau_order_three (Φ := Φ) hR hr' hN' (f := c6f e) ?_ h3 hv
    rw [hτ', Units.val_mul, Units.val_mul, Units.val_mul, hκe, coe_kGL, hkinv, c6f]
    simp only [colMat_mul6, mul_assoc]

end CFSG.Quasithin.H13.U3.NLine
