module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsModel
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailSupp
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic

public section

open Polynomial Module Multiplicative Matrix

namespace CFSG.StandardType

namespace OrthNs

open CFSG.Assembly SpNS NbrOrth SpCoord

section Zeta

variable {L : Type} [Field L] {M : Type} [AddCommGroup M]

theorem eq_zero_of_add_of_mul {ζ : L} (hζ : ζ ≠ 1) {D : L → M}
    (hadd : ∀ u v, D (u + v) = D u + D v) (hζD : ∀ u, D (ζ * u) = D u) (v : L) : D v = 0 := by
  have h0 : D 0 = 0 := by simpa using hadd 0 0
  have hζ1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζ
  have hv : v = ζ * ((ζ - 1)⁻¹ * v) + -((ζ - 1)⁻¹ * v) := by
    rw [← sub_eq_add_neg, ← sub_one_mul, ← mul_assoc, mul_inv_cancel₀ hζ1, one_mul]
  rw [hv, hadd, hζD, ← hadd, add_neg_cancel, h0]

end Zeta

section Quad

variable {K : Type} [Field K] {L : Type} [AddCommGroup L] [Module K L] {V : Type}
  [AddCommGroup V] [Module K V] {s : ℕ} {κ : Type} {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V}
  {QF : QuadraticForm K V} {β : LinearMap.BilinForm K L}

theorem quad_frame_eq
    (hdec : ∀ d d' w w', QuadraticMap.polarBilin QF (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin QF (Φ (0, w)) (Φ (0, w')))
    (d : Fin s → L) (w : κ → K) :
    QF (Φ (d, w)) = ∑ i, QF (Φ (Pi.single i (d i), 0)) + QF (Φ (0, w)) := by
  classical
  have key : ∀ T : Finset (Fin s), QF (Φ (T.piecewise d 0, w)) =
      ∑ i ∈ T, QF (Φ (Pi.single i (d i), 0)) + QF (Φ (0, w)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih =>
      have e : ((insert a T).piecewise d 0, w) =
          (Pi.single a (d a), (0 : κ → K)) + (T.piecewise d 0, w) := by
        refine Prod.ext ?_ (by simp)
        funext j
        by_cases hj : j = a
        · subst hj
          simp [Finset.piecewise, ha]
        · simp [Finset.piecewise, hj]
      have h0 : ∑ l, β ((Pi.single a (d a) : Fin s → L) l) (T.piecewise d 0 l) = 0 := by
        rw [Finset.sum_eq_single a]
        · simp [Finset.piecewise, ha]
        · intro j _ hj
          simp [Pi.single_eq_of_ne hj]
        · intro h
          exact absurd (Finset.mem_univ a) h
      have h00 : Φ (0, (0 : κ → K)) = 0 := by rw [Prod.mk_zero_zero, map_zero]
      rw [e, map_add, QuadraticMap.map_add (⇑QF), ← QuadraticMap.polarBilin_apply_apply, hdec, ih,
        Finset.sum_insert ha, h0, h00, LinearMap.map_zero₂]
      ring
  have := key Finset.univ
  rwa [Finset.piecewise_univ] at this

theorem quad_mono
    (hdec : ∀ d d' w w', QuadraticMap.polarBilin QF (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin QF (Φ (0, w)) (Φ (0, w')))
    (π : Equiv.Perm (Fin s)) {T : Fin s → (L ≃ₗ[K] L)}
    (hT : ∀ i u, QF (Φ (Pi.single i (T i u), 0)) = QF (Φ (Pi.single (π i) u, 0)))
    (x : (Fin s → L) × (κ → K)) : QF (Φ (monoEquiv π T x)) = QF (Φ x) := by
  obtain ⟨d, w⟩ := x
  rw [monoEquiv_apply, quad_frame_eq hdec (fun i => T i (d (π i))) w, quad_frame_eq hdec d w]
  congr 1
  simp only [hT]
  exact Equiv.sum_comp π (fun i => QF (Φ (Pi.single i (d i), 0)))

theorem quad_single_add
    (hdec : ∀ d d' w w', QuadraticMap.polarBilin QF (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + QuadraticMap.polarBilin QF (Φ (0, w)) (Φ (0, w')))
    (i : Fin s) (u v : L) :
    QF (Φ ((Pi.single i (u + v) : Fin s → L), 0)) =
      QF (Φ ((Pi.single i u : Fin s → L), 0)) + QF (Φ ((Pi.single i v : Fin s → L), 0)) +
        β u v := by
  classical
  have e : ((Pi.single i (u + v) : Fin s → L), (0 : κ → K)) =
      ((Pi.single i u : Fin s → L), (0 : κ → K)) + ((Pi.single i v : Fin s → L), 0) := by
    refine Prod.ext ?_ (by simp)
    rw [Prod.fst_add, Pi.single_add]
  have h0 : ∑ l, β ((Pi.single i u : Fin s → L) l) ((Pi.single i v : Fin s → L) l) = β u v := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h00 : Φ (0, (0 : κ → K)) = 0 := by rw [Prod.mk_zero_zero, map_zero]
  rw [e, map_add, QuadraticMap.map_add (⇑QF), ← QuadraticMap.polarBilin_apply_apply, hdec, h0, h00,
    LinearMap.map_zero₂, add_zero]

end Quad

section FrameGL

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : Type}
  [AddCommGroup X] [Module K X] (Φ : X ≃ₗ[K] (ι → K))

@[expose] noncomputable def frameGL (M : X ≃ₗ[K] X) : GL ι K :=
  Matrix.GeneralLinearGroup.toLin.symm (frameUnit Φ M)

theorem frameGL_mulVec (M : X ≃ₗ[K] X) (x : X) :
    ((frameGL Φ M : GL ι K) : Matrix ι ι K) *ᵥ Φ x = Φ (M x) := by
  have h := Matrix.GeneralLinearGroup.coe_toLin (frameGL Φ M)
  have hA : Matrix.GeneralLinearGroup.toLin (frameGL Φ M) = frameUnit Φ M :=
    MulEquiv.apply_symm_apply _ _
  rw [hA] at h
  have h2 := congrArg (fun F : (ι → K) →ₗ[K] (ι → K) => F (Φ x)) h
  rw [frameUnit_apply, Matrix.mulVecLin_apply] at h2
  exact h2.symm

theorem frameGL_mul (M N : X ≃ₗ[K] X) : frameGL Φ M * frameGL Φ N = frameGL Φ (N.trans M) := by
  rw [frameGL, frameGL, frameGL, ← map_mul, frameUnit_mul]

theorem frameGL_conj {M N N' : X ≃ₗ[K] X} (h : ∀ x, M (N x) = N' (M x)) :
    frameGL Φ M * frameGL Φ N * (frameGL Φ M)⁻¹ = frameGL Φ N' := by
  rw [frameGL, frameGL, frameGL, ← map_mul, ← map_inv, ← map_mul, frameUnit_conj Φ h]

theorem frameGL_mem_orth {Q : (ι → K) → K} {M : X ≃ₗ[K] X} (hM : ∀ x, Q (Φ (M x)) = Q (Φ x)) :
    frameGL Φ M ∈ LargeEvenOrthGroup Q :=
  TableBSymp.mem_orthGroup_of_isometry fun v => by
    obtain ⟨x, rfl⟩ := Φ.surjective v
    rw [frameGL_mulVec]
    exact hM x

end FrameGL

section TorConj

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}
  {p : ℕ} [NeZero p] {ζ : L} (hζ : ζ ^ p = 1)

include hζ in
theorem monoEquiv_torEquiv_sgn {σ : L ≃ₗ[K] L} (hσζ : ∀ u, σ (ζ * u) = ζ ^ (p - 1) * σ u)
    (P : Fin s → Prop) [DecidablePred P] (f : Fin s → Multiplicative (ZMod p))
    (x : (Fin s → L) × (κ → K)) :
    monoEquiv 1 (fun i => if P i then σ else LinearEquiv.refl K L) (torEquiv (K := K) hζ f x) =
      torEquiv hζ (fun i => if P i then (f i)⁻¹ else f i)
        (monoEquiv 1 (fun i => if P i then σ else LinearEquiv.refl K L) x) := by
  obtain ⟨d, w⟩ := x
  simp only [monoEquiv_apply, torEquiv_apply, Equiv.Perm.one_apply]
  refine Prod.ext (funext fun j => ?_) rfl
  by_cases hj : P j
  · simp only [hj, ↓reduceIte, toAdd_inv]
    have hσpow : ∀ (m : ℕ) (u : L), σ (ζ ^ m * u) = ζ ^ ((p - 1) * m) * σ u := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro u
        rw [pow_succ, mul_assoc, ih, hσζ, ← mul_assoc, ← pow_add, Nat.mul_succ]
    rw [hσpow]
    congr 1
    have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have h1 : ζ ^ ((p - 1) * (toAdd (f j)).val) * ζ ^ (toAdd (f j)).val = 1 := by
      have e : (p - 1) * (toAdd (f j)).val + (toAdd (f j)).val = p * (toAdd (f j)).val := by
        rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hpos)]
      rw [← pow_add, e, pow_mul, hζ, one_pow]
    have h2 : ζ ^ (-toAdd (f j)).val * ζ ^ (toAdd (f j)).val = 1 := by
      rw [← CoordSL.pow_val_add hζ, neg_add_cancel, ZMod.val_zero, pow_zero]
    exact mul_right_cancel₀ (root_pow_ne_zero hζ _) (h1.trans h2.symm)
  · simp only [hj, ↓reduceIte, LinearEquiv.refl_apply]

theorem monoEquiv_torEquiv_perm (π : Equiv.Perm (Fin s)) (f : Fin s → Multiplicative (ZMod p))
    (x : (Fin s → L) × (κ → K)) :
    monoEquiv π⁻¹ (fun _ => LinearEquiv.refl K L) (torEquiv (K := K) hζ f x) =
      torEquiv hζ (f ∘ ⇑π⁻¹) (monoEquiv π⁻¹ (fun _ => LinearEquiv.refl K L) x) := by
  obtain ⟨d, w⟩ := x
  simp only [monoEquiv_apply, torEquiv_apply, LinearEquiv.refl_apply, Function.comp_apply]

end TorConj

end OrthNs

end CFSG.StandardType

end
