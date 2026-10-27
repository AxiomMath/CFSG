module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalTrace
import CFSG.Open.StatedAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open Matrix CFSG.Open

section SignVector

variable {K : Type} [Field K]

private def sgn : Fin 2 → K := ![1, -1]

private lemma sgn_zero : sgn (K := K) 0 = 1 := by simp [sgn]

private lemma sgn_sq (i : Fin 2) : sgn (K := K) i * sgn (K := K) i = 1 := by
  fin_cases i <;> simp [sgn]

private lemma sgn_mul_of_ne {i j : Fin 2} (h : i ≠ j) : sgn (K := K) i * sgn (K := K) j = -1 := by
  fin_cases i <;> fin_cases j <;> simp_all [sgn]

private lemma scalar_eq_of_smul_eq_smul {ι : Type*} [Fintype ι]
    {M : Matrix ι ι K} (hM : M ≠ 0) {c d : K} (h : c • M = d • M) : c = d := by
  have h' : (c - d) • M = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero_iff_left hM).mp h')

private lemma eq_zero_of_neg_one_mul_eq_self {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {B : K}
    (h : (-1 : K) * B = B) : B = 0 := by
  have hneg : B = -B := by
    rw [neg_one_mul] at h
    exact h.symm
  have h2B : (2 : K) * B = 0 := by
    have hsum : B + B = 0 := by
      have := congrArg (fun x => x + B) hneg
      rwa [neg_add_cancel] at this
    rwa [two_mul]
  exact (mul_eq_zero.mp h2B).resolve_left h2

end SignVector

private def IsSigned {K : Type} [Field K] {Γ : Type*} [Group Γ]
    (ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K)
    (X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (g : Γ) (σ τ : K) : Prop :=
  (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X =
      σ • (X * (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) ∧
  (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y =
      τ • (Y * (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))

private lemma IsSigned.mul {K : Type} [Field K] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K}
    {X Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} {u v : Γ} {σ τ σ' τ' : K}
    (hu : IsSigned ρ X Y u σ τ) (hv : IsSigned ρ X Y v σ' τ') :
    IsSigned ρ X Y (u * v) (σ * σ') (τ * τ') := by
  have hval : ((ρ (u * v) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    rw [map_mul, Units.val_mul]
  constructor
  · rw [hval]
    calc ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * X
        = (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) := Matrix.mul_assoc _ _ _
      _ = (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (σ' • (X * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by rw [hv.1]
      _ = σ' • ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (X * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := Matrix.mul_smul _ _ _
      _ = σ' • (((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [← Matrix.mul_assoc]
      _ = σ' • ((σ • (X * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [hu.1]
      _ = σ' • (σ • ((X * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
            rw [Matrix.smul_mul]
      _ = (σ' * σ) • ((X * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [smul_smul]
      _ = (σ * σ') • ((X * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [mul_comm σ' σ]
      _ = (σ * σ') • (X * ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
            rw [Matrix.mul_assoc]
  · rw [hval]
    calc ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * Y
        = (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y) := Matrix.mul_assoc _ _ _
      _ = (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (τ' • (Y * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by rw [hv.2]
      _ = τ' • ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (Y * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := Matrix.mul_smul _ _ _
      _ = τ' • (((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [← Matrix.mul_assoc]
      _ = τ' • ((τ • (Y * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [hu.2]
      _ = τ' • (τ • ((Y * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
            rw [Matrix.smul_mul]
      _ = (τ' * τ) • ((Y * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [smul_smul]
      _ = (τ * τ') • ((Y * (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [mul_comm τ' τ]
      _ = (τ * τ') • (Y * ((ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
            rw [Matrix.mul_assoc]

private lemma exists_sign_first {K : Type} [Field K] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K} {N : Subgroup Γ} {x : Γ}
    (hN : IsQuatType ρ N) (hx : x ∈ N) {a : Γ} (ha : a ∈ N) :
    ∃ σ : K, (σ = 1 ∨ σ = -1) ∧
      (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        σ • ((ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  rcases hN.comm_or_anticomm a ha x hx with hc | hanti
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul]
    have h := congrArg (fun g : Γ => (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
    simpa [map_mul] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [neg_one_smul]
    simpa [map_mul] using hanti

private lemma exists_sign_second {K : Type} [Field K] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K} {N : Subgroup Γ} {y : Γ}
    (hN : IsQuatType ρ N) (hy : y ∈ N) {a : Γ} (ha : a ∈ N) :
    ∃ τ : K, (τ = 1 ∨ τ = -1) ∧
      (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        τ • ((ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  rcases hN.comm_or_anticomm a ha y hy with hc | hanti
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul]
    have h := congrArg (fun g : Γ => (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hc
    simpa [map_mul] using h
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [neg_one_smul]
    simpa [map_mul] using hanti

private lemma anticomm_matrix {K : Type} [Field K] {Γ : Type*} [Group Γ]
    {ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K} {N : Subgroup Γ}
    (hN : IsQuatType ρ N) {u v : Γ} (hu : u ∈ N) (hv : v ∈ N)
    (h : ¬ u * v = v * u) :
    (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      -((ρ v : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (ρ u : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
  rcases hN.comm_or_anticomm u hu v hv with hc | hanti
  · exact absurd hc h
  · simpa [map_mul] using hanti

private lemma eq_zero_of_mul_eq_zero_left {K : Type} [Field K]
    {X A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K} (hX : X * X = 1)
    (h : X * A = 0) : A = 0 := by
  calc A = (X * X) * A := by rw [hX, Matrix.one_mul]
    _ = X * (X * A) := Matrix.mul_assoc _ _ _
    _ = 0 := by rw [h, Matrix.mul_zero]

theorem sp_mem_scalars_of_commute {K : Type} [Field K] (hK : ringChar K ≠ 2) {Γ : Type*}
    [Group Γ] [Finite Γ] (ρ : Γ →* GL (Fin 2 ⊕ Fin 2) K) (hρ : Function.Injective ρ)
    (hSp : ∀ g, ρ g ∈ StatedSp 2 K) {N : Subgroup Γ} (hN : IsQuatType ρ N) {x y : Γ}
    (hx : x ∈ N) (hy : y ∈ N) (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) :
    x ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ ∨ y ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ ∨
      x * y ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ := by
  classical
  have _ : Function.Injective ρ := hρ
  by_contra hcon
  push Not at hcon
  obtain ⟨hxZ, hyZ, hxyZ⟩ := hcon
  let X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ρ x
  let Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := ρ y
  let J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 (-1) 0
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have h4 : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hX2 : X * X = 1 := by
    change (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
    have h : (ρ (x * x) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [map_mul, Units.val_mul]
    rw [hx2, map_one, Units.val_one] at h
    exact h.symm
  have hY2 : Y * Y = 1 := by
    change (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1
    have h : (ρ (y * y) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [map_mul, Units.val_mul]
    rw [hy2, map_one, Units.val_one] at h
    exact h.symm
  have hXY : X * Y = Y * X := by
    change (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
    have h := congrArg (fun g : Γ => (ρ g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hxy
    simpa [map_mul] using h
  have hYX : Y * X = X * Y := hXY.symm
  have hJX : Xᵀ * J * X = J := by
    change (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * fromBlocks 0 1 (-1) 0 * (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 0 1 (-1) 0
    exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSp x)
  have hJY : Yᵀ * J * Y = J := by
    change (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * fromBlocks 0 1 (-1) 0 * (ρ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 0 1 (-1) 0
    exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp (hSp y)
  have hJt : Jᵀ = -J := by
    change (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ =
      -fromBlocks 0 1 (-1) 0
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply]
  have hJne : J ≠ 0 := by
    intro h
    have h1 : J (Sum.inl 0) (Sum.inr 0) = 1 := by
      change (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        (Sum.inl 0) (Sum.inr 0) = 1
      simp [Matrix.fromBlocks_apply₁₂]
    rw [h] at h1
    exact zero_ne_one h1
  have hXY2 : (X * Y) * (X * Y) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Y X Y, hYX, Matrix.mul_assoc X Y Y, hY2, Matrix.mul_one, hX2]
  have hYX2 : (Y * X) * (Y * X) = 1 := by rw [hYX, hXY2]
  let sx : N → K := fun a => Classical.choose (exists_sign_first (K := K) (Γ := Γ) (ρ := ρ) (N := N) (x := x) (a := (a : Γ)) hN hx a.2)
  let sy : N → K := fun a => Classical.choose (exists_sign_second (K := K) (Γ := Γ) (ρ := ρ) (N := N) (y := y) (a := (a : Γ)) hN hy a.2)
  have sx_spec : ∀ a : N, (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X =
      sx a • (X * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := fun a =>
    (Classical.choose_spec (exists_sign_first (K := K) (Γ := Γ) (ρ := ρ) (N := N) (x := x) (a := (a : Γ)) hN hx a.2)).2
  have sy_spec : ∀ a : N, (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y =
      sy a • (Y * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := fun a =>
    (Classical.choose_spec (exists_sign_second (K := K) (Γ := Γ) (ρ := ρ) (N := N) (y := y) (a := (a : Γ)) hN hy a.2)).2
  have sx_pm : ∀ a : N, sx a = 1 ∨ sx a = -1 := fun a =>
    (Classical.choose_spec (exists_sign_first (K := K) (Γ := Γ) (ρ := ρ) (N := N) (x := x) (a := (a : Γ)) hN hx a.2)).1
  have sy_pm : ∀ a : N, sy a = 1 ∨ sy a = -1 := fun a =>
    (Classical.choose_spec (exists_sign_second (K := K) (Γ := Γ) (ρ := ρ) (N := N) (y := y) (a := (a : Γ)) hN hy a.2)).1
  have hMx : ∀ a : N, X * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 := by
    intro a h
    exact Units.ne_zero (ρ (a : Γ)) (eq_zero_of_mul_eq_zero_left hX2 h)
  have hMy : ∀ a : N, Y * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 := by
    intro a h
    exact Units.ne_zero (ρ (a : Γ)) (eq_zero_of_mul_eq_zero_left hY2 h)
  have hMxy : ∀ a : N, (X * Y) * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 := by
    intro a h
    exact Units.ne_zero (ρ (a : Γ)) (eq_zero_of_mul_eq_zero_left hXY2 h)
  have sx_mul : ∀ a b : N, sx (a * b) = sx a * sx b := by
    intro a b
    have hM : X * (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 :=
      hMx (a * b)
    refine scalar_eq_of_smul_eq_smul hM ?_
    have hab : (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
    have h2 : (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X =
        (sx a * sx b) • (X *
          (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
      rw [hab]
      calc ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * X
          = (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) :=
              Matrix.mul_assoc _ _ _
        _ = (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (sx b • (X * (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [sx_spec b]
        _ = sx b • ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (X * (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :=
              Matrix.mul_smul _ _ _
        _ = sx b • (((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [← Matrix.mul_assoc]
        _ = sx b • ((sx a •
              (X * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [sx_spec a]
        _ = sx b • (sx a • ((X *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [Matrix.smul_mul]
        _ = (sx b * sx a) • ((X *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [smul_smul]
        _ = (sx a * sx b) • ((X *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [mul_comm (sx b) (sx a)]
        _ = (sx a * sx b) • (X * ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [Matrix.mul_assoc]
    exact (sx_spec (a * b)).symm.trans h2
  have sy_mul : ∀ a b : N, sy (a * b) = sy a * sy b := by
    intro a b
    have hM : Y * (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 0 :=
      hMy (a * b)
    refine scalar_eq_of_smul_eq_smul hM ?_
    have hab : (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
          (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Subgroup.coe_mul, map_mul, Units.val_mul]
    have h2 : (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y =
        (sy a * sy b) • (Y *
          (ρ ((a * b : N) : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
      rw [hab]
      calc ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * Y
          = (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y) :=
              Matrix.mul_assoc _ _ _
        _ = (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (sy b • (Y * (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [sy_spec b]
        _ = sy b • ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (Y * (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) :=
              Matrix.mul_smul _ _ _
        _ = sy b • (((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [← Matrix.mul_assoc]
        _ = sy b • ((sy a •
              (Y * (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [sy_spec a]
        _ = sy b • (sy a • ((Y *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [Matrix.smul_mul]
        _ = (sy b * sy a) • ((Y *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [smul_smul]
        _ = (sy a * sy b) • ((Y *
              (ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [mul_comm (sy b) (sy a)]
        _ = (sy a * sy b) • (Y * ((ρ (a : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (ρ (b : Γ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by
              rw [Matrix.mul_assoc]
    exact (sy_spec (a * b)).symm.trans h2
  have hx_not_comm : ∃ a : Γ, a ∈ N ∧ ¬ a * x = x * a := by
    by_contra h
    push Not at h
    exact hxZ (hN.mem_of_comm x hx fun z hz => (h z hz).symm)
  obtain ⟨a, haN, ha_not_comm⟩ := hx_not_comm
  have haXanti : (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X =
      -(X * (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    have h := anticomm_matrix hN haN hx ha_not_comm
    simpa [X] using h
  have hy_not_comm : ∃ b : Γ, b ∈ N ∧ ¬ b * y = y * b := by
    by_contra h
    push Not at h
    exact hyZ (hN.mem_of_comm y hy fun z hz => (h z hz).symm)
  obtain ⟨b, hbN, hb_not_comm⟩ := hy_not_comm
  have hbYanti : (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y =
      -(Y * (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    have h := anticomm_matrix hN hbN hy hb_not_comm
    simpa [Y] using h
  have hxyN : x * y ∈ N := N.mul_mem hx hy
  have hxy_not_comm : ∃ c : Γ, c ∈ N ∧ ¬ c * (x * y) = (x * y) * c := by
    by_contra h
    push Not at h
    exact hxyZ (hN.mem_of_comm (x * y) hxyN fun z hz => (h z hz).symm)
  obtain ⟨c, hcN, hc_not_comm⟩ := hxy_not_comm
  have hcZanti : (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (X * Y) =
      -((X * Y) * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
    have h := anticomm_matrix hN hcN hxyN hc_not_comm
    simpa [X, Y, map_mul] using h
  have hAsx : sx ⟨a, haN⟩ = -1 := by
    refine scalar_eq_of_smul_eq_smul (hMx ⟨a, haN⟩) ?_
    calc sx ⟨a, haN⟩ • (X * (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        = (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X := (sx_spec ⟨a, haN⟩).symm
      _ = -(X * (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := haXanti
      _ = (-1 : K) • (X * (ρ a : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [neg_one_smul]
  have hBsy : sy ⟨b, hbN⟩ = -1 := by
    refine scalar_eq_of_smul_eq_smul (hMy ⟨b, hbN⟩) ?_
    calc sy ⟨b, hbN⟩ • (Y * (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        = (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y := (sy_spec ⟨b, hbN⟩).symm
      _ = -(Y * (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := hbYanti
      _ = (-1 : K) • (Y * (ρ b : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
            rw [neg_one_smul]
  let A : N := ⟨a, haN⟩
  let B : N := ⟨b, hbN⟩
  let C : N := ⟨c, hcN⟩
  have hA_sx : sx A = -1 := hAsx
  have hA_sy : sy A = 1 ∨ sy A = -1 := sy_pm A
  have hB_sx : sx B = 1 ∨ sx B = -1 := sx_pm B
  have hB_sy : sy B = -1 := hBsy
  have hC_prod : sx C * sy C = -1 := by
    refine scalar_eq_of_smul_eq_smul (hMxy C) ?_
    have h1 : (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (X * Y) =
        (sx C * sy C) • ((X * Y) *
          (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
      calc (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (X * Y)
          = ((ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) * Y :=
              (Matrix.mul_assoc _ _ _).symm
        _ = (sx C • (X * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) * Y := by
              rw [sx_spec C]
        _ = sx C • ((X * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * Y) :=
              Matrix.smul_mul _ _ _
        _ = sx C • (X * ((ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y)) := by
              rw [Matrix.mul_assoc]
        _ = sx C • (X * (sy C •
              (Y * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))) := by rw [sy_spec C]
        _ = sx C • (sy C • (X *
              (Y * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)))) := by
              rw [Matrix.mul_smul]
        _ = (sx C * sy C) • (X *
              (Y * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) := by rw [smul_smul]
        _ = (sx C * sy C) • ((X * Y) *
              (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [Matrix.mul_assoc]
    calc (sx C * sy C) • ((X * Y) *
          (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
        = (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (X * Y) := h1.symm
      _ = -((X * Y) * (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := hcZanti
      _ = (-1 : K) • ((X * Y) *
            (ρ c : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [neg_one_smul]
  have hone : IsSigned ρ X Y (1 : Γ) 1 1 := by
    constructor <;> simp [X, Y]
  have hA_signed : IsSigned ρ X Y a (-1) (sy A) := by
    constructor
    · simpa [IsSigned, X] using haXanti
    · exact sy_spec A
  have hB_signed : IsSigned ρ X Y b (sx B) (-1) := by
    constructor
    · exact sx_spec B
    · simpa [IsSigned, Y] using hbYanti
  have hC_signed : IsSigned ρ X Y c (sx C) (sy C) := ⟨sx_spec C, sy_spec C⟩
  have hExists : ∀ q : Fin 2 × Fin 2, ∃ g : Γ, g ∈ N ∧ IsSigned ρ X Y g (sgn (K := K) q.1) (sgn (K := K) q.2) := by
    rcases hA_sy with hAa | hAa
    · rcases hB_sx with hBb | hBb
      ·
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j
        · exact ⟨1, N.one_mem, by simpa [sgn] using hone⟩
        · refine ⟨b, hbN, ?_⟩
          simpa [sgn, hBb, hB_sy] using hB_signed
        · refine ⟨a, haN, ?_⟩
          simpa [sgn, hAa, hA_sx] using hA_signed
        · refine ⟨a * b, N.mul_mem haN hbN, ?_⟩
          have h := hA_signed.mul hB_signed
          simpa [sgn, hAa, hA_sx, hBb, hB_sy] using h
      ·
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j
        · exact ⟨1, N.one_mem, by simpa [sgn] using hone⟩
        · refine ⟨a * b, N.mul_mem haN hbN, ?_⟩
          have h := hA_signed.mul hB_signed
          simpa [sgn, hAa, hA_sx, hBb, hB_sy] using h
        · refine ⟨a, haN, ?_⟩
          simpa [sgn, hAa, hA_sx] using hA_signed
        · refine ⟨b, hbN, ?_⟩
          simpa [sgn, hBb, hB_sy] using hB_signed
    · rcases hB_sx with hBb | hBb
      ·
        rintro ⟨i, j⟩
        fin_cases i <;> fin_cases j
        · exact ⟨1, N.one_mem, by simpa [sgn] using hone⟩
        · refine ⟨b, hbN, ?_⟩
          simpa [sgn, hBb, hB_sy] using hB_signed
        · refine ⟨a * b, N.mul_mem haN hbN, ?_⟩
          have h := hA_signed.mul hB_signed
          simpa [sgn, hAa, hA_sx, hBb, hB_sy] using h
        · refine ⟨a, haN, ?_⟩
          simpa [sgn, hAa, hA_sx] using hA_signed
      ·
        rcases sx_pm C with hCc | hCc
        · have hCd : sy C = -1 := by simpa [hCc] using hC_prod
          rintro ⟨i, j⟩
          fin_cases i <;> fin_cases j
          · exact ⟨1, N.one_mem, by simpa [sgn] using hone⟩
          · refine ⟨c, hcN, ?_⟩
            simpa [sgn, hCc, hCd] using hC_signed
          · refine ⟨a * c, N.mul_mem haN hcN, ?_⟩
            have h := hA_signed.mul hC_signed
            simpa [sgn, hAa, hA_sx, hCc, hCd] using h
          · refine ⟨a, haN, ?_⟩
            simpa [sgn, hAa, hA_sx] using hA_signed
        · have hCd : sy C = 1 := by simpa [hCc] using hC_prod
          rintro ⟨i, j⟩
          fin_cases i <;> fin_cases j
          · exact ⟨1, N.one_mem, by simpa [sgn] using hone⟩
          · refine ⟨a * c, N.mul_mem haN hcN, ?_⟩
            have h := hA_signed.mul hC_signed
            simpa [sgn, hAa, hA_sx, hCc, hCd] using h
          · refine ⟨c, hcN, ?_⟩
            simpa [sgn, hCc, hCd] using hC_signed
          · refine ⟨a, haN, ?_⟩
            simpa [sgn, hAa, hA_sx] using hA_signed
  choose e heN heSign using hExists
  let P : Fin 2 → Fin 2 → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    fun i j => (4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))
  have hP_unfold : ∀ i j, P i j =
      (4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y)) := fun i j => rfl
  have hP00 : P 0 0 = (4 : K)⁻¹ • ((1 + X) * (1 + Y)) := by
    rw [hP_unfold, sgn_zero, one_smul, one_smul]
  have hP_X : ∀ i j, X * P i j = sgn (K := K) i • P i j := by
    intro i j
    have h1 : X * (1 + sgn (K := K) i • X) = sgn (K := K) i • (1 + sgn (K := K) i • X) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hX2,
        smul_add, smul_smul, sgn_sq, one_smul, add_comm]
    calc X * P i j
        = X * ((4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := rfl
      _ = (4 : K)⁻¹ • (X * ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := Matrix.mul_smul _ _ _
      _ = (4 : K)⁻¹ • ((X * (1 + sgn (K := K) i • X)) * (1 + sgn (K := K) j • Y)) := by rw [Matrix.mul_assoc]
      _ = (4 : K)⁻¹ • ((sgn (K := K) i • (1 + sgn (K := K) i • X)) * (1 + sgn (K := K) j • Y)) := by rw [h1]
      _ = (4 : K)⁻¹ • (sgn (K := K) i • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := by rw [Matrix.smul_mul]
      _ = sgn (K := K) i • ((4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := by
            rw [smul_smul, smul_smul, mul_comm]
      _ = sgn (K := K) i • P i j := rfl
  have hP_Y : ∀ i j, Y * P i j = sgn (K := K) j • P i j := by
    intro i j
    have hYj : Y * (1 + sgn (K := K) j • Y) = sgn (K := K) j • (1 + sgn (K := K) j • Y) := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hY2,
        smul_add, smul_smul, sgn_sq, one_smul, add_comm]
    have hYX' : Y * (1 + sgn (K := K) i • X) = (1 + sgn (K := K) i • X) * Y := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
        Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hYX]
    calc Y * P i j
        = Y * ((4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := rfl
      _ = (4 : K)⁻¹ • (Y * ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := Matrix.mul_smul _ _ _
      _ = (4 : K)⁻¹ • ((Y * (1 + sgn (K := K) i • X)) * (1 + sgn (K := K) j • Y)) := by rw [Matrix.mul_assoc]
      _ = (4 : K)⁻¹ • (((1 + sgn (K := K) i • X) * Y) * (1 + sgn (K := K) j • Y)) := by rw [hYX']
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (Y * (1 + sgn (K := K) j • Y))) := by rw [Matrix.mul_assoc]
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (sgn (K := K) j • (1 + sgn (K := K) j • Y))) := by rw [hYj]
      _ = (4 : K)⁻¹ • (sgn (K := K) j • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := by rw [Matrix.mul_smul]
      _ = sgn (K := K) j • ((4 : K)⁻¹ • ((1 + sgn (K := K) i • X) * (1 + sgn (K := K) j • Y))) := by
            rw [smul_smul, smul_smul, mul_comm]
      _ = sgn (K := K) j • P i j := rfl
  have hsumX : (∑ i : Fin 2,
      (1 + sgn (K := K) i • X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = (2 : K) • 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [sgn]
    rw [two_smul]
  have hsumY : (∑ j : Fin 2,
      (1 + sgn (K := K) j • Y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = (2 : K) • 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, Fin.sum_univ_two, Fin.sum_univ_two]
    simp [sgn]
    rw [two_smul]
  have hsum : (∑ q : Fin 2 × Fin 2, P q.1 q.2) = 1 := by
    rw [← Finset.smul_sum]
    have hprod : (∑ q : Fin 2 × Fin 2,
        (1 + sgn (K := K) q.1 • X) * (1 + sgn (K := K) q.2 • Y)) =
        (∑ i : Fin 2, (1 + sgn (K := K) i • X)) * (∑ j : Fin 2, (1 + sgn (K := K) j • Y)) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    rw [hprod, hsumX, hsumY]
    have h22 : (2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((2 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) =
        (4 : K) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
      norm_num
    rw [h22, smul_smul, inv_mul_cancel₀ h4, one_smul]
  have hconj : ∀ q : Fin 2 × Fin 2, P q.1 q.2 =
      (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * P 0 0 *
        ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
    intro q
    have hfacX : (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + X) =
        (1 + sgn (K := K) q.1 • X) * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      calc (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + X)
          = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
              (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X := by
              rw [Matrix.mul_add, Matrix.mul_one]
        _ = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
              sgn (K := K) q.1 • (X * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [(heSign q).1]
        _ = (1 + sgn (K := K) q.1 • X) *
              (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
              rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    have hfacY : (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + Y) =
        (1 + sgn (K := K) q.2 • Y) * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
      calc (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + Y)
          = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
              (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y := by
              rw [Matrix.mul_add, Matrix.mul_one]
        _ = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) +
              sgn (K := K) q.2 • (Y * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              rw [(heSign q).2]
        _ = (1 + sgn (K := K) q.2 • Y) *
              (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
              rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul]
    have hcancel : (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      simp
    have hcancelB : ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      simp
    have hfacB : (1 + Y) * ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + sgn (K := K) q.2 • Y) := by
      calc (1 + Y) * ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          = ((((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) * (1 + Y)) *
              ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
              rw [hcancelB, Matrix.one_mul]
        _ = ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + Y)) *
              ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
              simp only [Matrix.mul_assoc]
        _ = ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((1 + sgn (K := K) q.2 • Y) * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by rw [hfacY]
        _ = ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + sgn (K := K) q.2 • Y) *
              ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
              ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              simp only [Matrix.mul_assoc]
        _ = ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + sgn (K := K) q.2 • Y) := by
              rw [hcancel, Matrix.mul_one]
    have hconjM : (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((1 + X) * (1 + Y)) * ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        (1 + sgn (K := K) q.1 • X) * (1 + sgn (K := K) q.2 • Y) := by
      calc (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * ((1 + X) * (1 + Y)) *
            ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          = ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * (1 + X)) *
              ((1 + Y) * ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by
              simp only [Matrix.mul_assoc]
        _ = ((1 + sgn (K := K) q.1 • X) * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
              (((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
                (1 + sgn (K := K) q.2 • Y)) := by rw [hfacX, hfacB]
        _ = (1 + sgn (K := K) q.1 • X) *
              (((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
                ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *
                (1 + sgn (K := K) q.2 • Y)) := by simp only [Matrix.mul_assoc]
        _ = (1 + sgn (K := K) q.1 • X) * (1 + sgn (K := K) q.2 • Y) := by rw [hcancel, Matrix.one_mul]
    calc P q.1 q.2
        = (4 : K)⁻¹ • ((1 + sgn (K := K) q.1 • X) * (1 + sgn (K := K) q.2 • Y)) := rfl
      _ = (4 : K)⁻¹ • ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((1 + X) * (1 + Y)) *
            ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) := by rw [hconjM]
      _ = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            ((4 : K)⁻¹ • ((1 + X) * (1 + Y))) *
            ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * P 0 0 *
            ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by rw [hP00]
  have hP00_ne : P 0 0 ≠ 0 := by
    intro h0
    have hzero : ∀ q : Fin 2 × Fin 2, P q.1 q.2 = 0 := by
      intro q
      rw [hconj q, h0, Matrix.mul_zero, Matrix.zero_mul]
    have hsum0 : (∑ q : Fin 2 × Fin 2, P q.1 q.2) = 0 := by
      rw [Finset.sum_eq_zero]
      intro q _
      exact hzero q
    rw [hsum] at hsum0
    exact one_ne_zero hsum0
  obtain ⟨v0, hv0⟩ : ∃ v0 : Fin 2 ⊕ Fin 2 → K, P 0 0 *ᵥ v0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hP00_ne
    ext i j
    have hcol := h (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at hcol
    have := congrFun hcol i
    simpa using this
  let v : Fin 2 ⊕ Fin 2 → K := P 0 0 *ᵥ v0
  have hv : v ≠ 0 := hv0
  have hvX : X *ᵥ v = v := by
    change X *ᵥ (P 0 0 *ᵥ v0) = P 0 0 *ᵥ v0
    calc X *ᵥ (P 0 0 *ᵥ v0) = (X * P 0 0) *ᵥ v0 :=
          Matrix.mulVec_mulVec v0 X (P 0 0)
      _ = (sgn (K := K) 0 • P 0 0) *ᵥ v0 := by rw [hP_X 0 0]
      _ = sgn (K := K) 0 • (P 0 0 *ᵥ v0) := Matrix.smul_mulVec _ _ _
      _ = P 0 0 *ᵥ v0 := by rw [sgn_zero, one_smul]
  have hvY : Y *ᵥ v = v := by
    change Y *ᵥ (P 0 0 *ᵥ v0) = P 0 0 *ᵥ v0
    calc Y *ᵥ (P 0 0 *ᵥ v0) = (Y * P 0 0) *ᵥ v0 :=
          Matrix.mulVec_mulVec v0 Y (P 0 0)
      _ = (sgn (K := K) 0 • P 0 0) *ᵥ v0 := by rw [hP_Y 0 0]
      _ = sgn (K := K) 0 • (P 0 0 *ᵥ v0) := Matrix.smul_mulVec _ _ _
      _ = P 0 0 *ᵥ v0 := by rw [sgn_zero, one_smul]
  let u : Fin 2 × Fin 2 → (Fin 2 ⊕ Fin 2 → K) :=
    fun q => (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v
  have hu_ne : ∀ q, u q ≠ 0 := by
    intro q h
    apply hv
    have hc : ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      simp
    calc v = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v :=
          (Matrix.one_mulVec v).symm
      _ = (((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
            (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) *ᵥ v :=
          congrArg (fun M => M *ᵥ v) hc.symm
      _ = ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
            ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) :=
          (Matrix.mulVec_mulVec v ((ρ (e q))⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
            (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)).symm
      _ = 0 := by
            rw [show (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = 0
              from h, Matrix.mulVec_zero]
  have huX : ∀ q, X *ᵥ u q = sgn (K := K) q.1 • u q := by
    intro q
    have h' : X * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        sgn (K := K) q.1 • ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * X) := by
      have h := congrArg (fun M => sgn (K := K) q.1 • M) (heSign q).1
      rw [smul_smul, sgn_sq, one_smul] at h
      exact h.symm
    change X *ᵥ ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      sgn (K := K) q.1 • ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, h', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hvX]
  have huY : ∀ q, Y *ᵥ u q = sgn (K := K) q.2 • u q := by
    intro q
    have h' : Y * (ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        sgn (K := K) q.2 • ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * Y) := by
      have h := congrArg (fun M => sgn (K := K) q.2 • M) (heSign q).2
      rw [smul_smul, sgn_sq, one_smul] at h
      exact h.symm
    change Y *ᵥ ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      sgn (K := K) q.2 • ((ρ (e q) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v)
    rw [Matrix.mulVec_mulVec, h', Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hvY]
  have hPu : ∀ q r, P q.1 q.2 *ᵥ u r = if q = r then u r else 0 := by
    intro q r
    have hXfac : (1 + sgn (K := K) q.1 • X) *ᵥ u r =
        (1 + sgn (K := K) q.1 * sgn (K := K) r.1) • u r := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, huX r, smul_smul]
      rw [add_smul, one_smul]
    have hYfac : (1 + sgn (K := K) q.2 • Y) *ᵥ u r =
        (1 + sgn (K := K) q.2 * sgn (K := K) r.2) • u r := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, huY r, smul_smul]
      rw [add_smul, one_smul]
    have hcoef : (4 : K)⁻¹ * (1 + sgn (K := K) q.1 * sgn (K := K) r.1) * (1 + sgn (K := K) q.2 * sgn (K := K) r.2) =
        if q = r then 1 else 0 := by
      by_cases hqr : q = r
      · subst hqr
        rw [if_pos rfl, sgn_sq q.1, sgn_sq q.2]
        have htwo : (1 : K) + 1 = 2 := by norm_num
        rw [htwo]
        calc (4 : K)⁻¹ * 2 * 2 = (4 : K)⁻¹ * (2 * 2) := by rw [mul_assoc]
          _ = (4 : K)⁻¹ * 4 := by rw [show (2 : K) * 2 = 4 by norm_num]
          _ = 1 := inv_mul_cancel₀ h4
      · rw [if_neg hqr]
        have hne : q.1 ≠ r.1 ∨ q.2 ≠ r.2 := by
          by_contra h
          push Not at h
          exact hqr (Prod.ext h.1 h.2)
        rcases hne with h | h
        · rw [sgn_mul_of_ne h]
          ring
        · rw [sgn_mul_of_ne h]
          ring
    calc P q.1 q.2 *ᵥ u r
        = ((4 : K)⁻¹ • ((1 + sgn (K := K) q.1 • X) * (1 + sgn (K := K) q.2 • Y))) *ᵥ u r := rfl
      _ = (4 : K)⁻¹ • (((1 + sgn (K := K) q.1 • X) *
            (1 + sgn (K := K) q.2 • Y)) *ᵥ u r) :=
            Matrix.smul_mulVec (4 : K)⁻¹ _ (u r)
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) q.1 • X) *ᵥ
            ((1 + sgn (K := K) q.2 • Y) *ᵥ u r)) :=
            congrArg (fun z => (4 : K)⁻¹ • z)
              (Matrix.mulVec_mulVec (u r) (1 + sgn (K := K) q.1 • X)
                (1 + sgn (K := K) q.2 • Y)).symm
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) q.1 • X) *ᵥ
            ((1 + sgn (K := K) q.2 * sgn (K := K) r.2) • u r)) :=
            congrArg (fun z => (4 : K)⁻¹ • ((1 + sgn (K := K) q.1 • X) *ᵥ z)) hYfac
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) q.2 * sgn (K := K) r.2) •
            ((1 + sgn (K := K) q.1 • X) *ᵥ u r)) :=
            congrArg (fun z => (4 : K)⁻¹ • z)
              (Matrix.mulVec_smul (1 + sgn (K := K) q.1 • X)
                (1 + sgn (K := K) q.2 * sgn (K := K) r.2) (u r))
      _ = (4 : K)⁻¹ • ((1 + sgn (K := K) q.2 * sgn (K := K) r.2) •
            ((1 + sgn (K := K) q.1 * sgn (K := K) r.1) • u r)) :=
            congrArg (fun z => (4 : K)⁻¹ •
              ((1 + sgn (K := K) q.2 * sgn (K := K) r.2) • z)) hXfac
      _ = ((4 : K)⁻¹ * (1 + sgn (K := K) q.1 * sgn (K := K) r.1) *
            (1 + sgn (K := K) q.2 * sgn (K := K) r.2)) • u r := by
            rw [smul_smul, smul_smul]; ring_nf
      _ = (if q = r then (1 : K) else 0) • u r := by rw [hcoef]
      _ = if q = r then u r else 0 := by
            by_cases hqr : q = r <;> simp [hqr]
  have hlin : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have hcalc : P q.1 q.2 *ᵥ (∑ r : Fin 2 × Fin 2, g r • u r) = g q • u q := by
      rw [Matrix.mulVec_sum]
      calc (∑ r : Fin 2 × Fin 2, P q.1 q.2 *ᵥ (g r • u r))
          = ∑ r : Fin 2 × Fin 2, g r • (P q.1 q.2 *ᵥ u r) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              rw [Matrix.mulVec_smul]
        _ = ∑ r : Fin 2 × Fin 2, g r • (if q = r then u r else 0) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              rw [hPu q r]
        _ = g q • u q := by
              rw [Finset.sum_eq_single q]
              · simp
              · intro r _ hr
                rw [if_neg (Ne.symm hr), smul_zero]
              · intro hq
                exact absurd (Finset.mem_univ q) hq
    have h0 : P q.1 q.2 *ᵥ (∑ r : Fin 2 × Fin 2, g r • u r) = 0 := by
      rw [hg, Matrix.mulVec_zero]
    rw [hcalc] at h0
    exact (smul_eq_zero_iff_left (hu_ne q)).mp h0
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    refine LinearIndependent.span_eq_top_of_card_eq_finrank hlin ?_
    rw [Module.finrank_fintype_fun_eq_card K]
    simp [Fintype.card_prod]
  have hpres : ∀ (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K), Aᵀ * J * A = J →
      A * A = 1 → ∀ v w : Fin 2 ⊕ Fin 2 → K,
        (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ (J *ᵥ w) := by
    intro A hA hA2 v w
    have hJA : J * A = Aᵀ * J := by
      have h := congrArg (fun M => M * A) hA
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hA2, Matrix.mul_one] at h
      exact h.symm
    calc (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w))
        = (A *ᵥ v) ⬝ᵥ ((J * A) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = (A *ᵥ v) ⬝ᵥ ((Aᵀ * J) *ᵥ w) := by rw [hJA]
      _ = (A *ᵥ v) ⬝ᵥ (Aᵀ *ᵥ (J *ᵥ w)) := by rw [Matrix.mulVec_mulVec]
      _ = ((A *ᵥ v) ᵥ* Aᵀ) ⬝ᵥ (J *ᵥ w) :=
            Matrix.dotProduct_mulVec (A *ᵥ v) Aᵀ (J *ᵥ w)
      _ = (A *ᵥ (A *ᵥ v)) ⬝ᵥ (J *ᵥ w) := by rw [Matrix.vecMul_transpose]
      _ = ((A * A) *ᵥ v) ⬝ᵥ (J *ᵥ w) := by rw [Matrix.mulVec_mulVec]
      _ = v ⬝ᵥ (J *ᵥ w) := by rw [hA2, Matrix.one_mulVec]
  have hBorth : ∀ p q : Fin 2 × Fin 2, p ≠ q → u p ⬝ᵥ (J *ᵥ u q) = 0 := by
    intro p q hpq
    by_cases hp : p.1 = q.1
    · have hq : p.2 ≠ q.2 := fun h => hpq (Prod.ext hp h)
      have h := hpres Y hJY hY2 (u p) (u q)
      rw [huY p, huY q, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul,
        smul_eq_mul] at h
      rw [sgn_mul_of_ne hq] at h
      exact eq_zero_of_neg_one_mul_eq_self h2 h
    · have h := hpres X hJX hX2 (u p) (u q)
      rw [huX p, huX q, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul,
        smul_eq_mul] at h
      rw [sgn_mul_of_ne hp] at h
      exact eq_zero_of_neg_one_mul_eq_self h2 h
  have hBself : ∀ p : Fin 2 × Fin 2, u p ⬝ᵥ (J *ᵥ u p) = 0 := by
    intro p
    have h := Matrix.dotProduct_transpose_mulVec J (u p) (u p)
    rw [hJt, Matrix.neg_mulVec, dotProduct_neg] at h
    exact eq_zero_of_neg_one_mul_eq_self h2 (by rw [neg_one_mul]; exact h)
  have hz : ∀ q : Fin 2 × Fin 2, J *ᵥ u q = 0 := by
    intro q
    refine dotProduct_eq (J *ᵥ u q) 0 ?_
    intro w
    rw [zero_dotProduct]
    have hw : w ∈ Submodule.span K (Set.range u) := by
      rw [hspan]
      exact Submodule.mem_top
    have hspan0 : w ⬝ᵥ (J *ᵥ u q) = 0 := by
      refine Submodule.span_induction (p := fun x _ => x ⬝ᵥ (J *ᵥ u q) = 0) ?_ ?_ ?_ ?_ hw
      · rintro x ⟨r, rfl⟩
        by_cases hr : r = q
        · subst hr
          exact hBself r
        · exact hBorth r q hr
      · rw [zero_dotProduct]
      · intro a b _ _ ha hb
        rw [add_dotProduct, ha, hb, add_zero]
      · intro c a _ ha
        rw [smul_dotProduct, ha, smul_zero]
    rwa [dotProduct_comm]
  have hJmul : ∀ w : Fin 2 ⊕ Fin 2 → K, J *ᵥ w = 0 := by
    intro w
    have hw : w ∈ Submodule.span K (Set.range u) := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ => J *ᵥ x = 0) ?_ ?_ ?_ ?_ hw
    · rintro x ⟨q, rfl⟩
      exact hz q
    · rw [Matrix.mulVec_zero]
    · intro a b _ _ ha hb
      rw [Matrix.mulVec_add, ha, hb, add_zero]
    · intro c a _ ha
      rw [Matrix.mulVec_smul, ha, smul_zero]
  have hJzero : J = 0 := by
    refine Matrix.ext_of_mulVec_single ?_
    intro j
    rw [hJmul, Matrix.zero_mulVec]
  exact hJne hJzero

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
