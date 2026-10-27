module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS21.DFT

open Matrix

variable {K : Type} [Field K]

@[expose] def permMat3 : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def dftMat (ω : K) : Matrix (Fin 3) (Fin 3) K := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

@[expose] def dftInvMat (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2]

theorem dftMat_mul_dftInvMat (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    dftMat ω * dftInvMat ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dftMat, dftInvMat, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem dftInvMat_mul_dftMat (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    dftInvMat ω * dftMat ω = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dftMat, dftInvMat, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem dftMat_mul_permMat3 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    dftMat ω * permMat3 = diagonal ![1, ω, ω ^ 2] * dftMat ω := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dftMat, permMat3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> grind

theorem permMat3_mul_diagonal (d : Fin 3 → K) :
    permMat3 * diagonal d = diagonal ![d 2, d 0, d 1] * permMat3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [permMat3, Matrix.mul_apply, Matrix.diagonal_apply]

theorem permMat3_pow_three : (permMat3 : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [permMat3, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]

theorem det_dftMat (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : (dftMat ω).det = 1 := by
  rw [det_fin_three]
  simp [dftMat]
  grind

theorem det_permMat3 : (permMat3 : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [det_fin_three]
  simp [permMat3]

theorem diagonal_const_mul_comm (a : K) (M : Matrix (Fin 3) (Fin 3) K) :
    diagonal (fun _ => a) * M = M * diagonal (fun _ => a) := by
  ext i j
  simp [diagonal_mul, mul_diagonal, mul_comm]

@[expose] def permGL3 : GL (Fin 3) K :=
  ⟨permMat3, permMat3 ^ 2, by rw [← pow_succ', permMat3_pow_three],
    by rw [← pow_succ, permMat3_pow_three]⟩

theorem coe_permGL3 : ((permGL3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMat3 := rfl

theorem permGL3_pow_three : (permGL3 : GL (Fin 3) K) ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_permGL3, permMat3_pow_three, Units.val_one])

@[expose] def dftGL (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : GL (Fin 3) K :=
  ⟨dftMat ω, dftInvMat ω, dftMat_mul_dftInvMat h2 hω, dftInvMat_mul_dftMat h2 hω⟩

theorem coe_dftGL (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    (dftGL h2 hω : Matrix (Fin 3) (Fin 3) K) = dftMat ω := rfl

theorem sq_add_add_one_eq_zero {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) :
    (ω : K) ^ 2 + ω + 1 = 0 := by
  have h3' : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have h1' : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => h1 (Units.ext h)
  have : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination h3'
  exact (mul_eq_zero.mp this).resolve_left h1'

@[expose] def expHom {m : ℕ} [NeZero m] (ζ : Kˣ) (hζ : ζ ^ m = 1) :
    Multiplicative (ZMod m) →* Kˣ where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem expHom_apply {m : ℕ} [NeZero m] (ζ : Kˣ) (hζ : ζ ^ m = 1) (a : ZMod m) :
    expHom ζ hζ (.ofAdd a) = ζ ^ a.val := rfl

theorem expHom_injective {m : ℕ} [NeZero m] {ζ : Kˣ} (hζ : ζ ^ m = 1) (h : orderOf ζ = m) :
    Function.Injective (expHom ζ hζ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker] at ha
  change ζ ^ (Multiplicative.toAdd a).val = 1 at ha
  have hdvd := orderOf_dvd_of_pow_eq_one ha
  rw [h] at hdvd
  have h0 : (Multiplicative.toAdd a).val = 0 :=
    Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt (Multiplicative.toAdd a))
  rw [ZMod.val_eq_zero] at h0
  rw [Subgroup.mem_bot]
  exact h0

@[expose] def rot3 {R : Type} [AddCommGroup R] : (Fin 3 → R) →+ (Fin 3 → R) where
  toFun v := ![v 2, v 0, v 1]
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' v w := by funext i; fin_cases i <;> rfl

theorem rot3_apply_zero {R : Type} [AddCommGroup R] (v : Fin 3 → R) : rot3 v 0 = v 2 := rfl

theorem rot3_apply_one {R : Type} [AddCommGroup R] (v : Fin 3 → R) : rot3 v 1 = v 0 := rfl

theorem rot3_apply_two {R : Type} [AddCommGroup R] (v : Fin 3 → R) : rot3 v 2 = v 1 := rfl

theorem rot3_norm {m : ℕ} (v : Fin 3 → ZMod m) (hv : v + rot3 v + rot3 (rot3 v) = 0) :
    v = rot3 ![0, -v 1, v 0] - ![0, -v 1, v 0] := by
  have h0 : v 0 + v 2 + v 1 = 0 := by
    have := congrFun hv 0
    simp only [Pi.add_apply, rot3_apply_zero, rot3_apply_two, Pi.zero_apply] at this
    exact this
  funext i
  fin_cases i
  · show v 0 = v 0 - 0
    rw [sub_zero]
  · show v 1 = 0 - -v 1
    rw [zero_sub, neg_neg]
  · show v 2 = -v 1 - v 0
    linear_combination h0

theorem rot3_fixed {R : Type} [AddCommGroup R] {c : Fin 3 → R} (hc : rot3 c = c) :
    c = fun _ => c 0 := by
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [rot3_apply_zero, rot3_apply_one] at h0 h1
  funext i
  fin_cases i
  · rfl
  · exact h1.symm
  · exact h0

theorem rot3_ne {R : Type} [AddCommGroup R] [Nontrivial R] :
    ∃ v : Fin 3 → R, rot3 v ≠ v := by
  obtain ⟨a, ha⟩ := exists_ne (0 : R)
  refine ⟨![a, 0, 0], fun h => ha ?_⟩
  have := congrFun h 1
  exact this

@[expose] def powVec {m : ℕ} [NeZero m] (ζ : Kˣ) (hζ : ζ ^ m = 1) :
    Multiplicative (Fin 3 → ZMod m) →* (Fin 3 → Kˣ) where
  toFun v i := expHom ζ hζ (.ofAdd (Multiplicative.toAdd v i))
  map_one' := by funext i; simp
  map_mul' v w := by
    funext i
    simp only [toAdd_mul, Pi.add_apply, ofAdd_add, map_mul, Pi.mul_apply]

theorem powVec_apply {m : ℕ} [NeZero m] (ζ : Kˣ) (hζ : ζ ^ m = 1) (v : Fin 3 → ZMod m)
    (i : Fin 3) : powVec ζ hζ (.ofAdd v) i = ζ ^ (v i).val := rfl

theorem powVec_injective {m : ℕ} [NeZero m] {ζ : Kˣ} (hζ : ζ ^ m = 1) (h : orderOf ζ = m) :
    Function.Injective (powVec ζ hζ) := by
  intro v w hvw
  apply Multiplicative.toAdd.injective
  funext i
  have := congrFun hvw i
  exact Multiplicative.ofAdd.injective (expHom_injective hζ h this)

theorem permGL3_mul_diagGL (t : Fin 3 → Kˣ) :
    permGL3 * TauCeti.diagGL t = TauCeti.diagGL ![t 2, t 0, t 1] * permGL3 := by
  apply Units.ext
  simp only [Units.val_mul, coe_permGL3, TauCeti.diagGL_coe]
  rw [permMat3_mul_diagonal]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem dftGL_mul_diagGL_const (h2 : (2 : K) = 0) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (a : Kˣ) :
    dftGL h2 hω * TauCeti.diagGL (fun _ => a) = TauCeti.diagGL (fun _ => a) * dftGL h2 hω := by
  apply Units.ext
  simp only [Units.val_mul, coe_dftGL, TauCeti.diagGL_coe]
  exact (diagonal_const_mul_comm _ _).symm

theorem dftGL_mul_permGL3 (h2 : (2 : K) = 0) {ω : Kˣ} (hω : (ω : K) ^ 2 + ω + 1 = 0) :
    dftGL h2 hω * permGL3 = TauCeti.diagGL ![1, ω, ω ^ 2] * dftGL h2 hω := by
  apply Units.ext
  simp only [Units.val_mul, coe_dftGL, coe_permGL3, TauCeti.diagGL_coe]
  rw [dftMat_mul_permMat3 hω]
  congr 2
  funext i
  fin_cases i <;> simp

section Tau3

variable {ω : Kˣ} (hω3 : ω ^ 3 = 1)

@[expose] def tau3 : Multiplicative (Fin 3 → ZMod 3) →* GL (Fin 3) K :=
  TauCeti.diagGL.comp (powVec ω hω3)

theorem tau3_apply (v : Fin 3 → ZMod 3) :
    tau3 hω3 (.ofAdd v) = TauCeti.diagGL fun i => ω ^ (v i).val := rfl

theorem tau3_injective (h : orderOf ω = 3) : Function.Injective (tau3 hω3) :=
  TauCeti.diagGL_injective.comp (powVec_injective hω3 h)

theorem permGL3_mul_tau3 (v : Fin 3 → ZMod 3) :
    permGL3 * tau3 hω3 (.ofAdd v) = tau3 hω3 (.ofAdd (rot3 v)) * permGL3 := by
  rw [tau3_apply, tau3_apply, permGL3_mul_diagGL]
  congr 2
  funext i
  fin_cases i <;> rfl

theorem dftGL_mul_tau3_of_fixed (h2 : (2 : K) = 0) {ω' : K} (hω' : ω' ^ 2 + ω' + 1 = 0)
    {c : Fin 3 → ZMod 3} (hc : rot3 c = c) :
    dftGL h2 hω' * tau3 hω3 (.ofAdd c) = tau3 hω3 (.ofAdd c) * dftGL h2 hω' := by
  have hc' := rot3_fixed hc
  rw [tau3_apply, hc']
  exact dftGL_mul_diagGL_const h2 hω' _

theorem dftGL_mul_permGL3_tau3 (h2 : (2 : K) = 0) (hω : (ω : K) ^ 2 + ω + 1 = 0) :
    dftGL h2 hω * permGL3 = tau3 hω3 (.ofAdd ![0, 1, 2]) * dftGL h2 hω := by
  rw [dftGL_mul_permGL3 h2 hω, tau3_apply]
  congr 2
  funext i
  fin_cases i
  · show (1 : Kˣ) = ω ^ (0 : ZMod 3).val
    rw [ZMod.val_zero, pow_zero]
  · show ω = ω ^ (1 : ZMod 3).val
    rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  · show ω ^ 2 = ω ^ (2 : ZMod 3).val
    rfl

end Tau3

section Tau9

variable {ζ : Kˣ} (hζ9 : ζ ^ 9 = 1)

@[expose] def rot9 : (Fin 3 → ZMod 9) × ZMod 9 →+ (Fin 3 → ZMod 9) × ZMod 9 :=
  AddMonoidHom.prodMap rot3 (AddMonoidHom.id _)

theorem rot9_apply (u : Fin 3 → ZMod 9) (d : ZMod 9) : rot9 (u, d) = (rot3 u, d) := rfl

@[expose] def tau9 : Multiplicative ((Fin 3 → ZMod 9) × ZMod 9) →* GL (Fin 3) K × Kˣ :=
  MonoidHom.prod ((TauCeti.diagGL.comp (powVec ζ hζ9)).comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.fst _ _)))
    ((expHom ζ hζ9).comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd _ _)))

theorem tau9_apply (u : Fin 3 → ZMod 9) (d : ZMod 9) :
    tau9 hζ9 (.ofAdd (u, d)) = (TauCeti.diagGL fun i => ζ ^ (u i).val, ζ ^ d.val) := rfl

theorem tau9_injective (h : orderOf ζ = 9) : Function.Injective (tau9 hζ9) := by
  intro x y hxy
  obtain ⟨⟨u, d⟩, rfl⟩ := Multiplicative.ofAdd.surjective x
  obtain ⟨⟨u', d'⟩, rfl⟩ := Multiplicative.ofAdd.surjective y
  rw [tau9_apply, tau9_apply, Prod.mk.injEq] at hxy
  have hu : powVec ζ hζ9 (.ofAdd u) = powVec ζ hζ9 (.ofAdd u') :=
    TauCeti.diagGL_injective hxy.1
  have hd : expHom ζ hζ9 (.ofAdd d) = expHom ζ hζ9 (.ofAdd d') := hxy.2
  rw [Multiplicative.ofAdd.injective (powVec_injective hζ9 h hu),
    Multiplicative.ofAdd.injective (expHom_injective hζ9 h hd)]

theorem permGL3_mul_tau9 (v : (Fin 3 → ZMod 9) × ZMod 9) :
    (permGL3, 1) * tau9 hζ9 (.ofAdd v) = tau9 hζ9 (.ofAdd (rot9 v)) * (permGL3, 1) := by
  obtain ⟨u, d⟩ := v
  rw [rot9_apply, tau9_apply, tau9_apply, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one,
    permGL3_mul_diagGL]
  congr 3
  funext i
  fin_cases i <;> rfl

theorem dftGL_mul_tau9_of_fixed (h2 : (2 : K) = 0) {ω' : K} (hω' : ω' ^ 2 + ω' + 1 = 0)
    {c : (Fin 3 → ZMod 9) × ZMod 9} (hc : rot9 c = c) :
    (dftGL h2 hω', 1) * tau9 hζ9 (.ofAdd c) = tau9 hζ9 (.ofAdd c) * (dftGL h2 hω', 1) := by
  obtain ⟨u, d⟩ := c
  rw [rot9_apply, Prod.mk.injEq] at hc
  have hu := rot3_fixed hc.1
  rw [tau9_apply, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, mul_one, hu,
    dftGL_mul_diagGL_const h2 hω']

theorem dftGL_mul_permGL3_tau9 (h2 : (2 : K) = 0) (hω : ((ζ ^ 3 : Kˣ) : K) ^ 2 + ↑(ζ ^ 3) + 1 = 0) :
    (dftGL h2 hω, 1) * (permGL3, 1) =
      tau9 hζ9 (.ofAdd (![0, 3, 6], 0)) * (dftGL h2 hω, 1) := by
  rw [tau9_apply, Prod.mk_mul_mk, Prod.mk_mul_mk, one_mul, dftGL_mul_permGL3 h2 hω]
  have h0 : (0 : ZMod 9).val = 0 := rfl
  rw [h0, pow_zero, mul_one]
  congr 3
  funext i
  fin_cases i
  · show (1 : Kˣ) = ζ ^ (0 : ZMod 9).val
    rw [ZMod.val_zero, pow_zero]
  · show ζ ^ 3 = ζ ^ (3 : ZMod 9).val
    rfl
  · show (ζ ^ 3) ^ 2 = ζ ^ (6 : ZMod 9).val
    rw [← pow_mul]
    rfl

end Tau9

theorem rot9_norm (v : (Fin 3 → ZMod 9) × ZMod 9) (hv : v + rot9 v + rot9 (rot9 v) = 0) :
    ∃ s c, v = rot9 s - s + c ∧ rot9 c = c ∧ 3 • c = 0 := by
  obtain ⟨u, d⟩ := v
  rw [rot9_apply, rot9_apply, Prod.mk_add_mk, Prod.mk_add_mk, Prod.mk_eq_zero] at hv
  refine ⟨(![0, -u 1, u 0], 0), (0, d), ?_, by rw [rot9_apply, map_zero], ?_⟩
  · rw [rot9_apply, Prod.mk_sub_mk, Prod.mk_add_mk, ← rot3_norm u hv.1, sub_zero, add_zero,
      zero_add]
  · rw [Prod.smul_mk, smul_zero, succ_nsmul, two_nsmul, hv.2]
    rfl

theorem rot3_norm' (v : Fin 3 → ZMod 3) (hv : v + rot3 v + rot3 (rot3 v) = 0) :
    ∃ s c, v = rot3 s - s + c ∧ rot3 c = c ∧ 3 • c = 0 :=
  ⟨![0, -v 1, v 0], 0, by rw [add_zero]; exact rot3_norm v hv, map_zero _, smul_zero _⟩

end CFSG.RankThree.PartTwo.KFacts.KS21.DFT
