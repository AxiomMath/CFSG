module

public import CFSG.Quasithin.Vol2.Ch10SecC3M

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem sc_mul (y y' : Kˣ) : sc y * sc y' = sc (y * y') := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change (y : K) • ((y' : K) • Multiplicative.toAdd X) = ((y * y' : Kˣ) : K) • _
  rw [smul_smul, Units.val_mul]

theorem sc_one : sc (1 : Kˣ) = 1 := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change ((1 : Kˣ) : K) • Multiplicative.toAdd X = Multiplicative.toAdd X
  rw [Units.val_one, one_smul]

theorem fa_one : fa (1 : K ≃+* K) = 1 := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  ext i j
  rfl

theorem tau_mul_sc (y : Kˣ) : tau K * sc y = sc y * tau K := by
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change ((y : K) • Multiplicative.toAdd X)ᵀ = (y : K) • (Multiplicative.toAdd X)ᵀ
  rw [Matrix.transpose_smul]

theorem tau_type_mul (g g' : SL K × SL K) (y y' : Kˣ) :
    rho K g * sc y * tau K * (rho K g' * sc y' * tau K) = rho K (g * g'.swap) * sc (y * y') := by
  have h1 : tau K * (rho K g' * sc y' * tau K) = rho K g'.swap * sc y' := by
    rw [← mul_assoc, ← mul_assoc, tau_mul_rho, mul_assoc (rho K g'.swap), tau_mul_sc,
      mul_assoc, mul_assoc, tau_mul_self, mul_one]
  rw [mul_assoc, h1, map_mul, ← sc_mul, mul_assoc, ← mul_assoc (sc y), sc_mul_rho]
  group

variable [CharP K 2]

theorem eq_one_of_sc_mem_img {c : Kˣ} (h : sc c ∈ img K) : c = 1 := by
  obtain ⟨⟨g, k⟩, hg⟩ := h
  have key : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (g : Matrix (Fin 2) (Fin 2) K) * X * (k : Matrix (Fin 2) (Fin 2) K)ᵀ = (c : K) • X :=
    fun X => by
      have := congrArg (fun φ : MulAut (WM K) => Multiplicative.toAdd (φ (Multiplicative.ofAdd X)))
        hg
      simpa [toAdd_rho, toAdd_sc] using this
  set gi := ((g⁻¹ : SL K) : Matrix (Fin 2) (Fin 2) K) with hgi
  have hgg : gi * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hgg' : (g : Matrix (Fin 2) (Fin 2) K) * gi = 1 := by
    rw [hgi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hk : (k : Matrix (Fin 2) (Fin 2) K)ᵀ = (c : K) • gi := by
    have h1 := key 1
    rw [Matrix.mul_one] at h1
    calc (k : Matrix (Fin 2) (Fin 2) K)ᵀ = gi * ((g : Matrix (Fin 2) (Fin 2) K) *
          (k : Matrix (Fin 2) (Fin 2) K)ᵀ) := by rw [← Matrix.mul_assoc, hgg, Matrix.one_mul]
      _ = (c : K) • gi := by rw [h1, Matrix.mul_smul, Matrix.mul_one]
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) K, Commute X (g : Matrix (Fin 2) (Fin 2) K) := by
    intro X
    have h1 := key X
    rw [hk, Matrix.mul_smul] at h1
    have h2 : (g : Matrix (Fin 2) (Fin 2) K) * X * gi = X := smul_right_injective _ hc0 h1
    calc X * (g : Matrix (Fin 2) (Fin 2) K) =
          (g : Matrix (Fin 2) (Fin 2) K) * X * gi * (g : Matrix (Fin 2) (Fin 2) K) := by rw [h2]
      _ = (g : Matrix (Fin 2) (Fin 2) K) * X := by rw [Matrix.mul_assoc _ gi, hgg, Matrix.mul_one]
  obtain ⟨l, hl⟩ := Matrix.mem_range_scalar_of_commute_single fun i j _ => hcomm _
  have hl1 : l = 1 := by
    have hdet := g.2
    rw [← hl, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    exact eq_one_of_sq_eq_one hdet
  have hg1 : (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← hl, hl1]
    simp
  have hgi1 : gi = 1 := by rw [← hgg', hg1, Matrix.one_mul]
  rw [hgi1] at hk
  have hdet := k.2
  rw [← Matrix.det_transpose, hk, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    sq] at hdet
  exact Units.ext (eq_one_of_sq_eq_one hdet)

theorem mem_img_of_mul_self {g : SL K × SL K} {y : Kˣ}
    (h : rho K g * sc y * (rho K g * sc y) = 1) : rho K g * sc y ∈ img K := by
  have e : rho K g * sc y * (rho K g * sc y) = rho K (g * g) * sc (y * y) := by
    rw [map_mul, ← sc_mul, mul_assoc, ← mul_assoc (sc y), sc_mul_rho]
    group
  rw [e] at h
  have h1 : sc (y * y) = (rho K (g * g))⁻¹ := eq_inv_of_mul_eq_one_right h
  have h2 : sc (y * y) ∈ img K := by
    rw [h1, ← map_inv]
    exact rho_mem_img _
  have hy : y * y = 1 := eq_one_of_sc_mem_img h2
  have hy1 : y = 1 := Units.ext (eq_one_of_sq_eq_one (by
    have := congrArg Units.val hy
    rwa [Units.val_mul, Units.val_one] at this))
  rw [hy1, sc_one, mul_one]
  exact rho_mem_img g

variable [Finite K]

theorem lin_form (hK : 4 ≤ Nat.card K) {x : MulAut (WM K)} (hx : x ∈ norm K)
    (hlin : IsSemilin x 1) :
    ∃ (g : SL K × SL K) (y : Kˣ), x = rho K g * sc y ∨ x = rho K g * sc y * tau K := by
  obtain ⟨g, y, σ, h | h⟩ := mem_norm_form hK hx
  · have hs : IsSemilin x (1 * (1 * σ)) := by
      rw [h]
      exact (isSemilin_rho g).mul ((isSemilin_sc y).mul (isSemilin_fa σ))
    have hσ : σ = 1 := by
      have := hs.unique hlin
      rwa [one_mul, one_mul] at this
    refine ⟨g, y, Or.inl ?_⟩
    rw [h, hσ, fa_one, mul_one]
  · have hs : IsSemilin x (1 * (1 * σ) * 1) := by
      rw [h]
      exact ((isSemilin_rho g).mul ((isSemilin_sc y).mul (isSemilin_fa σ))).mul isSemilin_tau
    have hσ : σ = 1 := by
      have := hs.unique hlin
      rwa [one_mul, one_mul, mul_one] at this
    refine ⟨g, y, Or.inr ?_⟩
    rw [h, hσ, fa_one, mul_one]

theorem card_inf_linSub_le (hK : 4 ≤ Nat.card K) {A : Subgroup (MulAut (WM K))}
    (hAN : A ≤ norm K) (hA : IsElemAbelian2 A) :
    Nat.card ↥(A ⊓ linSub K) ≤ 2 * Nat.card ↥(A ⊓ img K) := by
  classical
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hA.2 a ha
  have hτ : ∀ a ∈ A ⊓ linSub K, a ∉ img K → ∃ (g : SL K × SL K) (y : Kˣ),
      a = rho K g * sc y * tau K := by
    intro a ha hai
    obtain ⟨g, y, h | h⟩ := lin_form hK (hAN ha.1) ha.2
    · exact absurd (h ▸ mem_img_of_mul_self (h ▸ hsq a ha.1)) hai
    · exact ⟨g, y, h⟩
  by_cases hs : ∃ s ∈ A ⊓ linSub K, s ∉ img K
  · obtain ⟨s, hsA, hsi⟩ := hs
    obtain ⟨g₀, y₀, hs0⟩ := hτ s hsA hsi
    have hmul : ∀ a ∈ A ⊓ linSub K, a ∉ img K → a * s ∈ img K := by
      intro a ha hai
      obtain ⟨g, y, rfl⟩ := hτ a ha hai
      have e := tau_type_mul g g₀ y y₀
      rw [← hs0] at e
      rw [e]
      apply mem_img_of_mul_self
      rw [← e]
      exact hsq _ (A.mul_mem ha.1 hsA.1)
    let f : ↥(A ⊓ linSub K) → Bool × ↥(A ⊓ img K) := fun a =>
      if ha : (a : MulAut (WM K)) ∈ img K then (false, ⟨a, a.2.1, ha⟩)
      else (true, ⟨a * s, A.mul_mem a.2.1 hsA.1, hmul a a.2 ha⟩)
    have hf : Function.Injective f := by
      intro x y hxy
      simp only [f] at hxy
      split_ifs at hxy with hx hy hy
      · exact Subtype.ext
          (congrArg (Subtype.val : ↥(A ⊓ img K) → MulAut (WM K)) (Prod.mk.inj hxy).2)
      · exact absurd (Prod.mk.inj hxy).1 (by decide)
      · exact absurd (Prod.mk.inj hxy).1 (by decide)
      · exact Subtype.ext (mul_right_cancel (congrArg Subtype.val (Prod.mk.inj hxy).2))
    calc Nat.card ↥(A ⊓ linSub K) ≤ Nat.card (Bool × ↥(A ⊓ img K)) :=
          Nat.card_le_card_of_injective f hf
      _ = 2 * Nat.card ↥(A ⊓ img K) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  · push Not at hs
    have hle : A ⊓ linSub K ≤ A ⊓ img K := fun a ha => ⟨ha.1, hs a ha⟩
    calc Nat.card ↥(A ⊓ linSub K) ≤ Nat.card ↥(A ⊓ img K) := Subgroup.card_le_of_le hle
      _ ≤ 2 * Nat.card ↥(A ⊓ img K) := Nat.le_mul_of_pos_left _ (by norm_num)

end CFSG.Quasithin.Vol2.Ch10.C3.Om
