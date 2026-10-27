module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace CoordSL

section Galois

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem finite_adjoinRoot : Finite (AdjoinRoot g) :=
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  Module.finite_of_finite K

theorem exists_galExp_of_aeval [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
    (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {a b : ZMod p} (hb : b ≠ 0)
    (h : aeval (AdjoinRoot.root g ^ a.val) (minpoly K (AdjoinRoot.root g ^ b.val)) = 0) :
    ∃ u : (ZMod p)ˣ, u ∈ galExp g hζ ∧ a = u * b := by
  have : Finite (AdjoinRoot g) := finite_adjoinRoot
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  have hint : IsIntegral K (ζ ^ b.val) := Algebra.IsIntegral.isIntegral _
  have heq : minpoly K (ζ ^ b.val) = minpoly K (ζ ^ a.val) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) (E := AdjoinRoot g)).mp heq.symm
  replace hσ : σ (ζ ^ b.val) = ζ ^ a.val := hσ
  set v : (ZMod p)ˣ := (Units.mk0 b hb)⁻¹ with hv
  have hbv : b * (v : ZMod p) = 1 := by
    rw [hv, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hb]
  have hζv : (ζ ^ b.val) ^ (v : ZMod p).val = ζ := by
    rw [pow_val_pow_val hζ, hbv, pow_val_one hζ]
  have hσζ : σ ζ = ζ ^ (a * (v : ZMod p)).val := by
    conv_lhs => rw [← hζv]
    rw [map_pow, hσ, pow_val_pow_val hζ]
  have hav : a * (v : ZMod p) ≠ 0 := by
    intro h0
    rw [h0, ZMod.val_zero, pow_zero, ← map_one σ] at hσζ
    have h1 : ζ = 1 := σ.injective hσζ
    exact (Fact.out : p.Prime).one_lt.ne' ((hprim.eq_orderOf).trans (by rw [h1, orderOf_one]))
  refine ⟨Units.mk0 _ hav, ⟨σ, by rw [Units.val_mk0, hσζ]⟩, ?_⟩
  rw [Units.val_mk0, mul_assoc, mul_comm (v : ZMod p) b, hbv, mul_one]

variable {M : Type*} [AddCommGroup M] [Module K M]

omit [Finite K] in
theorem map_aeval_mul {f : AdjoinRoot g →ₗ[K] AdjoinRoot g} {x₀ y₀ : AdjoinRoot g}
    (hf : ∀ x, f (x₀ * x) = y₀ * f x) (Q : K[X]) (x : AdjoinRoot g) :
    f (aeval x₀ Q * x) = aeval y₀ Q * f x := by
  have hpow : ∀ (k : ℕ) (x : AdjoinRoot g), f (x₀ ^ k * x) = y₀ ^ k * f x := by
    intro k
    induction k with
    | zero => intro x; rw [pow_zero, pow_zero, one_mul, one_mul]
    | succ k ih => intro x; rw [pow_succ, mul_assoc, ih, hf, pow_succ, mul_assoc]
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => rw [map_add, map_add, add_mul, add_mul, map_add, hP, hQ]
  | monomial k c =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, mul_assoc, ← Algebra.smul_def,
      ← Algebra.smul_def, map_smul, hpow]

variable [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
include hζ hprim

theorem eq_zero_of_intertwine {a b : ZMod p} (hb : b ≠ 0)
    (hab : ∀ u ∈ galExp g hζ, a ≠ u * b) {f : AdjoinRoot g →ₗ[K] AdjoinRoot g}
    (hf : ∀ x, f (AdjoinRoot.root g ^ b.val * x) = AdjoinRoot.root g ^ a.val * f x) :
    f = 0 := by
  have : Finite (AdjoinRoot g) := finite_adjoinRoot
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have hint : IsIntegral K (AdjoinRoot.root g ^ b.val) := Algebra.IsIntegral.isIntegral _
  have hne : aeval (AdjoinRoot.root g ^ a.val) (minpoly K (AdjoinRoot.root g ^ b.val)) ≠ 0 := by
    intro h0
    obtain ⟨u, hu, hau⟩ := exists_galExp_of_aeval hζ hprim hb h0
    exact hab u hu hau
  ext x
  have h1 := map_aeval_mul hf (minpoly K (AdjoinRoot.root g ^ b.val)) x
  rw [minpoly.aeval, zero_mul, map_zero] at h1
  rw [LinearMap.zero_apply]
  exact (mul_eq_zero.mp h1.symm).resolve_left hne

omit [Finite K] hprim in
theorem mul_eq_of_intertwine {b : ZMod p} (hb : b ≠ 0) {f : AdjoinRoot g →ₗ[K] AdjoinRoot g}
    (hf : ∀ x, f (AdjoinRoot.root g ^ b.val * x) = AdjoinRoot.root g ^ b.val * f x)
    (x : AdjoinRoot g) : f x = x * f 1 := by
  set ζ := AdjoinRoot.root g with hζdef
  set v : (ZMod p)ˣ := (Units.mk0 b hb)⁻¹ with hv
  have hbv : b * (v : ZMod p) = 1 := by
    rw [hv, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hb]
  have hζv : aeval (ζ ^ b.val) (X ^ (v : ZMod p).val : K[X]) = ζ := by
    rw [aeval_X_pow, pow_val_pow_val hζ, hbv, pow_val_one hζ]
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective x
  have hQ : AdjoinRoot.mk g Q = aeval (ζ ^ b.val) (Q.comp (X ^ (v : ZMod p).val)) := by
    rw [aeval_comp, hζv, AdjoinRoot.aeval_eq]
  have h1 := map_aeval_mul hf (Q.comp (X ^ (v : ZMod p).val)) 1
  rw [mul_one, ← hQ] at h1
  exact h1

end Galois

section FrameForm

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] {n s r : ℕ}
  (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)

@[expose] noncomputable def frameForm (u : Matrix (Fin n) (Fin n) K) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
  (frameCoords g ε).symm.toLinearMap ∘ₗ Matrix.toLin' u ∘ₗ (frameCoords g ε).toLinearMap

theorem frameCoords_frameForm (u : Matrix (Fin n) (Fin n) K)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameCoords g ε (frameForm g ε u x) = u *ᵥ frameCoords g ε x := by
  simp [frameForm, Matrix.toLin'_apply]

theorem frameForm_apply (u : Matrix (Fin n) (Fin n) K)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameForm g ε u x = (frameCoords g ε).symm (u *ᵥ frameCoords g ε x) := by
  simp [frameForm, Matrix.toLin'_apply]

theorem frameForm_mul (u v : Matrix (Fin n) (Fin n) K) :
    frameForm g ε (u * v) = frameForm g ε u ∘ₗ frameForm g ε v := by
  refine LinearMap.ext fun x => ?_
  simp only [frameForm_apply, LinearMap.comp_apply, LinearEquiv.apply_symm_apply,
    Matrix.mulVec_mulVec]

theorem frameForm_one : frameForm g ε (1 : Matrix (Fin n) (Fin n) K) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp [frameForm_apply]

theorem frameForm_injective : Function.Injective (frameForm g ε) := by
  intro u v h
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun w => ?_
  obtain ⟨x, rfl⟩ := (frameCoords g ε).surjective w
  have h1 := congrArg (fun φ => frameCoords g ε (φ x)) h
  simp only [frameCoords_frameForm] at h1
  simpa [Matrix.toLin'_apply] using h1

@[expose] noncomputable def torusAct (k : Fin s → ℕ) (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    (Fin s → AdjoinRoot g) × (Fin r → K) :=
  (fun i => AdjoinRoot.root g ^ k i * x.1 i, x.2)

theorem frameForm_nsMat (k : Fin s → ℕ) (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameForm g ε (SLNS.nsMat ε (rootMat g) k) x = torusAct g k x := by
  rw [frameForm_apply, nsMat_mulVec_frameCoords, LinearEquiv.symm_apply_apply]
  rfl

theorem frameForm_torusAct_comm {u : Matrix (Fin n) (Fin n) K} {k : Fin s → ℕ}
    (hu : u * SLNS.nsMat ε (rootMat g) k = SLNS.nsMat ε (rootMat g) k * u)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameForm g ε u (torusAct g k x) = torusAct g k (frameForm g ε u x) := by
  have h := congrArg (fun v => frameForm g ε v x) hu
  simp only [frameForm_mul, LinearMap.comp_apply] at h
  rwa [frameForm_nsMat, frameForm_nsMat] at h

end FrameForm

section Block

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {s r p : ℕ}
  [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1)

@[expose] def Aligned (β : Fin s → ZMod p) : Prop :=
  ∀ i j, β j ≠ 0 → ∀ u ∈ galExp g hζ, β i = u * β j → β i = β j

variable {hζ} (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p)
include hprim

omit [Finite K] in
theorem root_pow_val_ne_one {b : ZMod p} (hb : b ≠ 0) : AdjoinRoot.root g ^ b.val ≠ 1 := by
  rw [Ne, hprim.pow_eq_one_iff_dvd]
  intro h
  exact hb (by rw [← ZMod.natCast_zmod_val b, (ZMod.natCast_eq_zero_iff _ _).mpr h])

omit [Finite K] in
theorem torusAct_eq_self_iff {β : Fin s → ZMod p} {x : (Fin s → AdjoinRoot g) × (Fin r → K)} :
    torusAct g (fun i => (β i).val) x = x ↔ ∀ i, β i ≠ 0 → x.1 i = 0 := by
  constructor
  · intro h i hi
    have h1 := congrFun (congrArg Prod.fst h) i
    change AdjoinRoot.root g ^ (β i).val * x.1 i = x.1 i at h1
    have h2 : (AdjoinRoot.root g ^ (β i).val - 1) * x.1 i = 0 := by rw [sub_mul, h1, one_mul,
      sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr (root_pow_val_ne_one hprim hi))
  · intro h
    refine Prod.ext (funext fun i => ?_) rfl
    change AdjoinRoot.root g ^ (β i).val * x.1 i = x.1 i
    by_cases hi : β i = 0
    · rw [hi, ZMod.val_zero, pow_zero, one_mul]
    · rw [h i hi, mul_zero]

theorem apply_single_of_comm {β : Fin s → ZMod p} (hal : Aligned hζ β)
    {φ : ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K))}
    (hφ : ∀ x, φ (torusAct g (fun i => (β i).val) x) = torusAct g (fun i => (β i).val) (φ x))
    {j : Fin s} (hj : β j ≠ 0) (x : AdjoinRoot g) :
    φ (Pi.single j x, 0) =
      (fun i => if β i = β j then x * (φ (Pi.single j 1, 0)).1 i else 0, 0) := by
  set ζ := AdjoinRoot.root g with hζdef
  have hT : ∀ y : AdjoinRoot g, torusAct g (fun i => (β i).val)
      ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K)) =
        (Pi.single j (ζ ^ (β j).val * y), 0) := by
    intro y
    refine Prod.ext (funext fun k => ?_) rfl
    change ζ ^ (β k).val * (Pi.single j y : Fin s → AdjoinRoot g) k = _
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  set e : AdjoinRoot g →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
    LinearMap.inl K _ _ ∘ₗ LinearMap.single K (fun _ => AdjoinRoot g) j with he
  have heapp : ∀ y, e y = ((Pi.single j y : Fin s → AdjoinRoot g), (0 : Fin r → K)) := fun y => rfl
  have hcomm : ∀ y, φ (e (ζ ^ (β j).val * y)) = torusAct g (fun i => (β i).val) (φ (e y)) := by
    intro y
    rw [heapp, heapp, ← hT, hφ]
  refine Prod.ext (funext fun i => ?_) ?_
  · set f : AdjoinRoot g →ₗ[K] AdjoinRoot g :=
      LinearMap.proj i ∘ₗ LinearMap.fst K _ _ ∘ₗ φ ∘ₗ e with hf
    have hfapp : ∀ y, f y = (φ (e y)).1 i := fun y => rfl
    have hfint : ∀ y, f (ζ ^ (β j).val * y) = ζ ^ (β i).val * f y := by
      intro y
      rw [hfapp, hfapp, hcomm]
      rfl
    show (φ (e x)).1 i = if β i = β j then x * (φ (Pi.single j 1, 0)).1 i else 0
    by_cases hij : β i = β j
    · simp only [hij, ↓reduceIte]
      rw [← heapp, ← hfapp, ← hfapp]
      rw [hij] at hfint
      exact mul_eq_of_intertwine hζ hj hfint x
    · simp only [hij, ↓reduceIte]
      rw [← hfapp]
      have hab : ∀ u ∈ galExp g hζ, β i ≠ u * β j := fun u hu h => hij (hal i j hj u hu h)
      rw [eq_zero_of_intertwine hζ hprim hj hab hfint, LinearMap.zero_apply]
  · set h : AdjoinRoot g →ₗ[K] (Fin r → K) := LinearMap.snd K _ _ ∘ₗ φ ∘ₗ e with hh
    have hhapp : ∀ y, h y = (φ (e y)).2 := fun y => rfl
    have hhint : ∀ y, h (ζ ^ (β j).val * y) = h y := by
      intro y
      rw [hhapp, hhapp, hcomm]
      rfl
    change (φ (e x)).2 = 0
    have hne : ζ ^ (β j).val - 1 ≠ 0 := sub_ne_zero.mpr (root_pow_val_ne_one hprim hj)
    have h1 : x = (ζ ^ (β j).val - 1) * ((ζ ^ (β j).val - 1)⁻¹ * x) := by
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    rw [← hhapp, h1, sub_mul, one_mul, map_sub, hhint, sub_self]

end Block

section Theta

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] {n s r : ℕ}
  (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)

@[expose] noncomputable def blockAct (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) →ₗ[K] ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
  LinearMap.prodMap ((Matrix.toLin' M).restrictScalars K) LinearMap.id

theorem blockAct_apply (M : Matrix (Fin s) (Fin s) (AdjoinRoot g))
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    blockAct (r := r) g M x = (M *ᵥ x.1, x.2) := by
  simp [blockAct, Matrix.toLin'_apply]

@[expose] noncomputable def thetaMat (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) :
    Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' ((frameCoords g ε).toLinearMap ∘ₗ blockAct g M ∘ₗ
    (frameCoords g ε).symm.toLinearMap)

theorem frameForm_thetaMat (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) :
    frameForm g ε (thetaMat g ε M) = blockAct g M := by
  refine LinearMap.ext fun x => ?_
  rw [frameForm_apply, thetaMat, LinearMap.toMatrix'_mulVec]
  simp

theorem thetaMat_mul (M N : Matrix (Fin s) (Fin s) (AdjoinRoot g)) :
    thetaMat g ε (M * N) = thetaMat g ε M * thetaMat g ε N := by
  apply frameForm_injective g ε
  rw [frameForm_mul, frameForm_thetaMat, frameForm_thetaMat, frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  simp [blockAct_apply, Matrix.mulVec_mulVec]

theorem thetaMat_one : thetaMat g ε (1 : Matrix (Fin s) (Fin s) (AdjoinRoot g)) = 1 := by
  apply frameForm_injective g ε
  rw [frameForm_thetaMat, frameForm_one]
  refine LinearMap.ext fun x => ?_
  simp [blockAct_apply]

theorem det_thetaMat (M : Matrix (Fin s) (Fin s) (AdjoinRoot g)) :
    (thetaMat g ε M).det = Algebra.norm K M.det := by
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  rw [thetaMat, LinearMap.det_toMatrix', LinearMap.det_conj, blockAct, LinearMap.det_prodMap,
    LinearMap.det_id, mul_one, LinearMap.det_restrictScalars, LinearMap.det_toLin']

@[expose] noncomputable def theta :
    Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g) →* Matrix.SpecialLinearGroup (Fin n) K where
  toFun M := ⟨thetaMat g ε M, by rw [det_thetaMat, M.2, map_one]⟩
  map_one' := Subtype.ext (thetaMat_one g ε)
  map_mul' M N := Subtype.ext (thetaMat_mul g ε M N)

theorem coe_theta (M : Matrix.SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
    (theta g ε M : Matrix (Fin n) (Fin n) K) = thetaMat g ε M :=
  rfl

theorem theta_injective : Function.Injective (theta g ε) := by
  intro M N h
  have h1 := congrArg
    (fun u : Matrix.SpecialLinearGroup (Fin n) K => frameForm g ε (u : Matrix (Fin n) (Fin n) K)) h
  simp only [coe_theta, frameForm_thetaMat] at h1
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  have h2 := congrArg (fun φ => (φ (y, (0 : Fin r → K))).1) h1
  simpa [blockAct_apply, Matrix.toLin'_apply] using h2

theorem thetaMat_diagonal (k : Fin s → ℕ) :
    thetaMat g ε (Matrix.diagonal fun i => AdjoinRoot.root g ^ k i) =
      SLNS.nsMat ε (rootMat g) k := by
  apply frameForm_injective g ε
  rw [frameForm_thetaMat]
  refine LinearMap.ext fun x => ?_
  rw [frameForm_nsMat, blockAct_apply]
  refine Prod.ext (funext fun i => ?_) rfl
  simp [Matrix.mulVec_diagonal, torusAct]

end Theta

end CoordSL

end CFSG.StandardType
