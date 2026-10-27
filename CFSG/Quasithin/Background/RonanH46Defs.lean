module

public import CFSG.Quasithin.Background.HL3NineModel
public import CFSG.Quasithin.Background.RonanH44Perf

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def LW (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  perfectCore ((stabW K).map (rho hK))

@[expose] noncomputable def LZ (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  perfectCore ((stabZ K).map (rho hK))

theorem mem_LW {hK : Nat.card K = (2 ^ n) ^ 2} {g : MulAut (HMod n K)} (hg : g ∈ LW hK) :
    ∃ g₀ ∈ perfW K, rho hK g₀ = g := by
  have : g ∈ (perfectCore (stabW K)).map (rho hK) := by
    rw [map_perfectCore]
    exact hg
  obtain ⟨g₀, hg₀, rfl⟩ := this
  exact ⟨g₀, perfectCore_stabW_le hg₀, rfl⟩

theorem mem_LZ {hK : Nat.card K = (2 ^ n) ^ 2} {g : MulAut (HMod n K)} (hg : g ∈ LZ hK) :
    ∃ g₀ ∈ perfZ K, rho hK g₀ = g := by
  have : g ∈ (perfectCore (stabZ K)).map (rho hK) := by
    rw [map_perfectCore]
    exact hg
  obtain ⟨g₀, hg₀, rfl⟩ := this
  exact ⟨g₀, perfectCore_stabZ_le hg₀, rfl⟩

theorem rho_embW_mem_LW {hK : Nat.card K = (2 ^ n) ^ 2} (h4 : 4 ≤ Nat.card K) (A : SL(2, K)) :
    rho hK (embW A) ∈ LW hK := by
  unfold LW
  rw [← map_perfectCore]
  exact ⟨embW A, embW_mem_perfectCore h4 A, rfl⟩

theorem rho_embZ_mem_LZ {hK : Nat.card K = (2 ^ n) ^ 2} (h4 : 4 ≤ Nat.card K) (A : SL(2, K)) :
    rho hK (embZ A) ∈ LZ hK := by
  unfold LZ
  rw [← map_perfectCore]
  exact ⟨embZ A, embZ_mem_perfectCore h4 A, rfl⟩

@[expose] def blkZ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 0 0 = 0 ∧ mat X 0 1 = 0 ∧ mat X 0 2 = 0}
  one_mem' := by simp [mat_one]
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    simp [mat_mul, hX.1, hX.2.1, hX.2.2, hY.1, hY.2.1, hY.2.2]
  inv_mem' {X} hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    simp [mat_inv, hX.1, hX.2.1, hX.2.2]

@[expose] def V2z (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 1 1 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0}
  one_mem' := by simp [mat_one]
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    simp [mat_mul, hX.1, hX.2.1, hX.2.2, hY.1, hY.2.1, hY.2.2]
  inv_mem' {X} hX := by
    simp only [Set.mem_setOf_eq] at hX ⊢
    simp [mat_inv, hX.1, hX.2.1, hX.2.2]

theorem mem_V2z {X : HMod n K} : X ∈ V2z n K ↔ mat X 1 1 = 0 ∧ mat X 1 2 = 0 ∧ mat X 2 2 = 0 :=
  Iff.rfl

section Vocab

@[expose] def InducesOnR {V : Type*} [CommGroup V] (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    (A : Type*) [CommGroup A] (Γ : Subgroup (MulAut A)) : Prop :=
  Z ≤ U ∧ (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) ∧ (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) ∧
  ∃ β : ↥U →* A, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
    (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))

@[expose] def IsActsInvR {A : Type*} [Group A] (acts : Set (A → A)) (U : Subgroup A) : Prop :=
  ∀ f ∈ acts, ∀ u ∈ U, f u ∈ U

@[expose] def IsChiefFactorUnderR {A : Type*} [Group A] (acts : Set (A → A)) (X Y : Subgroup A) :
    Prop :=
  X < Y ∧ IsActsInvR acts X ∧ IsActsInvR acts Y ∧
    ∀ W : Subgroup A, X ≤ W → W ≤ Y → IsActsInvR acts W → W = X ∨ W = Y

@[expose] def actsOnModuleR {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) : Set (V → V) :=
  {f | ∃ y ∈ Y, f = fun v => y v}

@[expose] def commOnR {V : Type*} [CommGroup V] (W : Subgroup V) (A : Subgroup (MulAut V)) :
    Subgroup V :=
  Subgroup.closure {u | ∃ a ∈ A, ∃ w ∈ W, u = a w * w⁻¹}

@[expose] def natHomR (d : ℕ) (K : Type*) [Field K] :
    GL (Fin d) K →* MulAut (Multiplicative (Fin d → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd
        ((g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      invFun := fun v => Multiplicative.ofAdd
        (((g⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v))
      left_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_mulVec]
      map_mul' := fun v w => by
        apply Multiplicative.toAdd.injective
        simp [Matrix.mulVec_add] }
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [Matrix.mulVec_mulVec]

@[expose] def natSubR (d : ℕ) (K : Type*) [Field K] (S : Subgroup (GL (Fin d) K)) :
    Subgroup (MulAut (Multiplicative (Fin d → K))) :=
  S.map (natHomR d K)

@[expose] def StatedSLR (n : ℕ) (K : Type) [Field K] : Subgroup (GL (Fin n) K) :=
  Subgroup.closure {A | (A : Matrix (Fin n) (Fin n) K).det = 1}

end Vocab

theorem natHomR_apply {d : ℕ} {K : Type*} [Field K] (g : GL (Fin d) K)
    (v : Multiplicative (Fin d → K)) :
    Multiplicative.toAdd (natHomR d K g v) =
      (g : Matrix (Fin d) (Fin d) K).mulVec (Multiplicative.toAdd v) := rfl

theorem mem_StatedSLR {n : ℕ} {K : Type} [Field K] {A : GL (Fin n) K} :
    A ∈ StatedSLR n K ↔ (A : Matrix (Fin n) (Fin n) K).det = 1 := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => simp
    | mul x y _ _ hx hy =>
      rw [Units.val_mul, Matrix.det_mul, hx, hy, mul_one]
    | inv x _ hx =>
      have h : ((x⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (x : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 := congrArg Matrix.det h
      rw [Matrix.det_mul, hx, mul_one, Matrix.det_one] at h2
      exact h2
  · intro h
    exact Subgroup.subset_closure h

end CFSG.Quasithin.RonanH46
