module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin
open scoped TensorProduct

@[expose] def nineActLin (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) (⇑σ⁻¹)

theorem permAct_mem_permCore_nine {n : ℕ} (σ : Equiv.Perm (Fin n)) {x : Fin n → ZMod 2}
    (hx : x ∈ permCore n) : permAct σ x ∈ permCore n := by
  have hs : ∑ i, x i = 0 := hx
  show ∑ i, permAct σ x i = 0
  simp only [permAct]
  rw [Equiv.sum_comp σ⁻¹ x]
  exact hs

@[expose] def nineAct (n : ℕ) (σ : Equiv.Perm (Fin n)) : permCore n →ₗ[ZMod 2] permCore n :=
  LinearMap.codRestrict (permCore n) ((nineActLin n σ).comp (permCore n).subtype)
    (fun x => permAct_mem_permCore_nine σ x.2)

theorem coe_nineAct (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : permCore n) :
    ((nineAct n σ x : permCore n) : Fin n → ZMod 2) = permAct σ x := rfl

theorem nine_add_self {M : Type} [AddCommMonoid M] [Module (ZMod 2) M] (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

section Coeff

variable {P Q : Type} [AddCommMonoid P] [Module (ZMod 2) P] [AddCommMonoid Q] [Module (ZMod 2) Q]

@[expose] noncomputable def nineCoeff (φ : P →ₗ[ZMod 2] ZMod 2) : P ⊗[ZMod 2] Q →ₗ[ZMod 2] Q :=
  (TensorProduct.lid (ZMod 2) Q).toLinearMap ∘ₗ LinearMap.rTensor Q φ

theorem nineCoeff_tmul (φ : P →ₗ[ZMod 2] ZMod 2) (a : P) (b : Q) :
    nineCoeff φ (a ⊗ₜ[ZMod 2] b) = φ a • b := by
  simp [nineCoeff, TensorProduct.lid_tmul]

theorem nine_rec {u w : P} {φ₀ φ₁ : P →ₗ[ZMod 2] ZMod 2}
    (hdec : ∀ a : P, a = φ₁ a • u + φ₀ a • w) (z : P ⊗[ZMod 2] Q) :
    z = u ⊗ₜ[ZMod 2] nineCoeff φ₁ z + w ⊗ₜ[ZMod 2] nineCoeff φ₀ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have ha := hdec a
    rw [nineCoeff_tmul, nineCoeff_tmul]
    calc a ⊗ₜ[ZMod 2] b = (φ₁ a • u + φ₀ a • w) ⊗ₜ[ZMod 2] b := by rw [← ha]
      _ = u ⊗ₜ[ZMod 2] (φ₁ a • b) + w ⊗ₜ[ZMod 2] (φ₀ a • b) := by
        simp [TensorProduct.add_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x x' hx hx' =>
    calc x + x' = (u ⊗ₜ[ZMod 2] nineCoeff φ₁ x + w ⊗ₜ[ZMod 2] nineCoeff φ₀ x) +
          (u ⊗ₜ[ZMod 2] nineCoeff φ₁ x' + w ⊗ₜ[ZMod 2] nineCoeff φ₀ x') := by
          rw [← hx, ← hx']
      _ = u ⊗ₜ[ZMod 2] nineCoeff φ₁ (x + x') + w ⊗ₜ[ZMod 2] nineCoeff φ₀ (x + x') := by
          simp only [map_add, TensorProduct.tmul_add]
          abel

theorem nine_fix_eq_zero_of_coeff {u w : P} {φ₀ φ₁ : P →ₗ[ZMod 2] ZMod 2}
    (hdec : ∀ a : P, a = φ₁ a • u + φ₀ a • w)
    {S : P →ₗ[ZMod 2] P} {τ : Q →ₗ[ZMod 2] Q}
    (hS0 : ∀ a, φ₀ (S a) = φ₀ a) (hS1 : ∀ a, φ₁ (S a) = φ₁ a + φ₀ a)
    {y : P ⊗[ZMod 2] Q} (hy : TensorProduct.map S τ y = y) (hD : nineCoeff φ₁ y = 0) :
    y = 0 := by
  have hC : ∀ z : P ⊗[ZMod 2] Q,
      nineCoeff φ₀ (TensorProduct.map S τ z) = τ (nineCoeff φ₀ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [nineCoeff_tmul, hS0, map_smul]
    | add x x' hx hx' => simp only [map_add, hx, hx']
  have hD' : ∀ z : P ⊗[ZMod 2] Q,
      nineCoeff φ₁ (TensorProduct.map S τ z) = τ (nineCoeff φ₀ z + nineCoeff φ₁ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul, nineCoeff_tmul, hS1, add_smul, map_add, map_smul]
      abel
    | add x x' hx hx' =>
      simp only [map_add, hx, hx']
      abel
  have h1 : nineCoeff φ₀ y = τ (nineCoeff φ₀ y) := by
    have := congrArg (nineCoeff φ₀) hy
    rw [hC] at this
    exact this.symm
  have h2 : τ (nineCoeff φ₀ y + nineCoeff φ₁ y) = nineCoeff φ₁ y := by
    have := congrArg (nineCoeff φ₁) hy
    rw [hD'] at this
    exact this
  rw [hD, add_zero] at h2
  have hC0 : nineCoeff φ₀ y = 0 := h1.trans h2
  calc y = u ⊗ₜ[ZMod 2] nineCoeff φ₁ y + w ⊗ₜ[ZMod 2] nineCoeff φ₀ y := nine_rec hdec y
    _ = 0 := by rw [hD, hC0, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero]

theorem nine_fix_eq_zero_cycle {u w : P} {φ₀ φ₁ : P →ₗ[ZMod 2] ZMod 2}
    (hdec : ∀ a : P, a = φ₁ a • u + φ₀ a • w)
    {S : P →ₗ[ZMod 2] P} (hS0 : ∀ a, φ₀ (S a) = φ₁ a) (hS1 : ∀ a, φ₁ (S a) = φ₁ a + φ₀ a)
    {y : P ⊗[ZMod 2] Q} (hy : TensorProduct.map S LinearMap.id y = y) : y = 0 := by
  have hC : ∀ z : P ⊗[ZMod 2] Q,
      nineCoeff φ₀ (TensorProduct.map S LinearMap.id z) = nineCoeff φ₁ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [nineCoeff_tmul, hS0]
    | add x x' hx hx' => simp only [map_add, hx, hx']
  have hD : ∀ z : P ⊗[ZMod 2] Q,
      nineCoeff φ₁ (TensorProduct.map S LinearMap.id z) =
        nineCoeff φ₀ z + nineCoeff φ₁ z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, nineCoeff_tmul, hS1, add_smul]
      abel
    | add x x' hx hx' =>
      simp only [map_add, hx, hx']
      abel
  have h1 : nineCoeff φ₀ y = nineCoeff φ₁ y := by
    have := congrArg (nineCoeff φ₀) hy
    rw [hC] at this
    exact this.symm
  have h2 : nineCoeff φ₀ y + nineCoeff φ₁ y = nineCoeff φ₁ y := by
    have := congrArg (nineCoeff φ₁) hy
    rw [hD] at this
    exact this
  have hCy : nineCoeff φ₀ y = 0 := by
    calc nineCoeff φ₀ y = nineCoeff φ₀ y + (nineCoeff φ₁ y + nineCoeff φ₁ y) := by
          rw [nine_add_self, add_zero]
      _ = (nineCoeff φ₀ y + nineCoeff φ₁ y) + nineCoeff φ₁ y := by abel
      _ = nineCoeff φ₁ y + nineCoeff φ₁ y := by rw [h2]
      _ = 0 := nine_add_self _
  have hDy : nineCoeff φ₁ y = 0 := by
    rw [← h1]
    exact hCy
  calc y = u ⊗ₜ[ZMod 2] nineCoeff φ₁ y + w ⊗ₜ[ZMod 2] nineCoeff φ₀ y := nine_rec hdec y
    _ = 0 := by rw [hDy, hCy, TensorProduct.tmul_zero, TensorProduct.tmul_zero, add_zero]

theorem nine_sq_eq_one {u w : P} {φ₀ φ₁ : P →ₗ[ZMod 2] ZMod 2}
    (hdec : ∀ a : P, a = φ₁ a • u + φ₀ a • w) (hu1 : φ₁ u = 1) (hu0 : φ₀ u = 0)
    (hw1 : φ₁ w = 0) (hw0 : φ₀ w = 1)
    {S : P →ₗ[ZMod 2] P} {τ : Q →ₗ[ZMod 2] Q}
    (h : ∀ a b, TensorProduct.map S τ (TensorProduct.map S τ (a ⊗ₜ[ZMod 2] b)) = a ⊗ₜ[ZMod 2] b)
    {b : Q} (hb : b ≠ 0) (a : P) : S (S a) = a := by
  have E1 : ∀ a' b', φ₁ (S (S a')) • τ (τ b') = φ₁ a' • b' := by
    intro a' b'
    have := congrArg (nineCoeff φ₁) (h a' b')
    simpa [nineCoeff_tmul, TensorProduct.map_tmul] using this
  have E0 : ∀ a' b', φ₀ (S (S a')) • τ (τ b') = φ₀ a' • b' := by
    intro a' b'
    have := congrArg (nineCoeff φ₀) (h a' b')
    simpa [nineCoeff_tmul, TensorProduct.map_tmul] using this
  have eu1 := E1 u b
  have eu0 := E0 u b
  have ew1 := E1 w b
  have ew0 := E0 w b
  rw [hu1, one_smul] at eu1
  rw [hu0, zero_smul] at eu0
  rw [hw1, zero_smul] at ew1
  rw [hw0, one_smul] at ew0
  have hcase : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hα1 : φ₁ (S (S u)) = 1 := by
    rcases hcase (φ₁ (S (S u))) with h0 | h1
    · rw [h0, zero_smul] at eu1
      exact absurd eu1.symm hb
    · exact h1
  have hR : τ (τ b) = b := by
    rw [hα1, one_smul] at eu1
    exact eu1
  rw [hR] at eu0 ew0 ew1
  have hβ0 : φ₀ (S (S u)) = 0 := by
    rcases hcase (φ₀ (S (S u))) with h0 | h1
    · exact h0
    · rw [h1, one_smul] at eu0
      exact absurd eu0 hb
  have hδ1 : φ₀ (S (S w)) = 1 := by
    rcases hcase (φ₀ (S (S w))) with h0 | h1
    · rw [h0, zero_smul] at ew0
      exact absurd ew0.symm hb
    · exact h1
  have hγ0 : φ₁ (S (S w)) = 0 := by
    rcases hcase (φ₁ (S (S w))) with h0 | h1
    · exact h0
    · rw [h1, one_smul] at ew1
      exact absurd ew1 hb
  have hSu : S (S u) = u := by
    calc S (S u) = φ₁ (S (S u)) • u + φ₀ (S (S u)) • w := hdec (S (S u))
      _ = u := by rw [hα1, hβ0, one_smul, zero_smul, add_zero]
  have hSw : S (S w) = w := by
    calc S (S w) = φ₁ (S (S w)) • u + φ₀ (S (S w)) • w := hdec (S (S w))
      _ = w := by rw [hγ0, hδ1, zero_smul, one_smul, zero_add]
  have ha := hdec a
  calc S (S a) = S (S (φ₁ a • u + φ₀ a • w)) := by rw [← ha]
    _ = φ₁ a • S (S u) + φ₀ a • S (S w) := by simp only [map_add, map_smul]
    _ = φ₁ a • u + φ₀ a • w := by rw [hSu, hSw]
    _ = a := ha.symm


end Coeff

theorem nine_finrank_ker_le_of_inj {X Q : Type} [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X] [AddCommMonoid Q] [Module (ZMod 2) Q]
    [Module.Finite (ZMod 2) Q]
    (t : X →ₗ[ZMod 2] X) (D : X →ₗ[ZMod 2] Q)
    (h : ∀ x, t x = x → D x = 0 → x = 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (t - LinearMap.id)) ≤ Module.finrank (ZMod 2) Q := by
  have hinj : Function.Injective (D.comp (LinearMap.ker (t - LinearMap.id)).subtype) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    have hx1 : t x.1 = x.1 := by
      have := LinearMap.mem_ker.1 x.2
      rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    exact h x.1 hx1 hx
  exact LinearMap.finrank_le_finrank_of_injective hinj

end CFSG.Quasithin.G112A2
