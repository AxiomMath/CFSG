module

public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bField
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LieType.Steinberg.Isogeny.TwistedE6

public noncomputable section

namespace CFSG.StandardType.E4bLift

variable {F : Type} [Field F]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
open CFSG.StandardType.TwE6FixedA2SL3
open scoped MatrixGroups

@[expose] def fixedA2AdjRho : SL(3, F) →* ↥(adjointGroup Tag.E6 F) :=
  (fixedA2Rho F).codRestrict _
    (fun A => by
      have h : fixedA2Rho F A ∈ (fixedA2Rho F).range := ⟨A, rfl⟩
      rw [range_fixedA2Rho] at h
      exact rootSpan_le_adjointGroup F _ h)

theorem fixedA2AdjRho_injective : Function.Injective (fixedA2AdjRho (F := F)) :=
  fun _ _ h => fixedA2Rho_injective F (congrArg Subtype.val h)

@[simp]
theorem fixedA2AdjRho_coe (A : SL(3, F)) :
    ((fixedA2AdjRho (F := F) A : ↥(adjointGroup Tag.E6 F)) : ModGL Tag.E6 F) =
      fixedA2Rho F A :=
  rfl

@[expose] def fixedA2Scalar (ω : Fˣ) : SL(3, F) :=
  diagSL3 ω (ω ^ 2)

theorem fixedA2Scalar_eq_diagSL3 (ω : Fˣ) :
    fixedA2Scalar (F := F) ω = diagSL3 ω (ω ^ 2) :=
  rfl

theorem fixedA2Scalar_eq_scalarElement {ω : Fˣ} (hω3 : ω ^ 3 = 1) :
    fixedA2Scalar (F := F) ω =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement (n := 3) ω hω3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fixedA2Scalar, diagSL3,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement,
      Matrix.scalar_apply]
  · have h : ω⁻¹ * ω ^ 2 = ω := by group
    simpa only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] using
      congrArg Units.val h
  · have h : (ω ^ 2)⁻¹ = ω := by
      rw [inv_eq_iff_mul_eq_one]
      simpa [pow_succ, show (3 : ℕ) = 2 + 1 by norm_num] using hω3
    simpa only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val] using
      congrArg Units.val h

theorem fixedA2Scalar_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) :
    fixedA2Scalar (F := F) ω ^ 3 = 1 := by
  rw [fixedA2Scalar_eq_scalarElement (F := F) hω3]
  ext i j
  change ((Matrix.scalar (Fin 3) (ω : F)) ^ 3) i j =
    (1 : Matrix (Fin 3) (Fin 3) F) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_pow]
  by_cases hij : i = j
  · subst hij
    simpa [Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
      Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hω3
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem fixedA2Scalar_ne_one {ω : Fˣ} (hω1 : ω ≠ 1) :
    fixedA2Scalar (F := F) ω ≠ 1 := by
  intro h
  apply hω1
  ext
  have h00 := congrArg (fun A : SL(3, F) =>
    (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simpa [fixedA2Scalar, diagSL3] using h00

theorem fixedA2Scalar_pow_three_eq (ζ : Fˣ) :
    fixedA2Scalar (F := F) ζ ^ 3 = fixedA2Scalar (F := F) (ζ ^ 3) := by
  apply fixedA2Rho_injective F
  dsimp [fixedA2Scalar]
  rw [map_pow, fixedA2Rho_diagSL3, fixedA2Rho_diagSL3]
  show (rootDiagUnitHom Tag.E6 F) (diagTuple ζ (ζ ^ 2)) ^ 3 =
    (rootDiagUnitHom Tag.E6 F) (diagTuple (ζ ^ 3) ((ζ ^ 3) ^ 2))
  rw [← map_pow (rootDiagUnitHom Tag.E6 F), diagTuple_pow]
  have h : (ζ ^ 2) ^ 3 = (ζ ^ 3) ^ 2 := by
    ext
    rw [← pow_mul, ← pow_mul]
  rw [h]


def fixedA2RangeEquiv : SL(3, F) ≃* (fixedA2AdjRho (F := F)).range :=
  MulEquiv.ofBijective (fixedA2AdjRho (F := F)).rangeRestrict
    ⟨fun _ _ h => fixedA2AdjRho_injective (F := F) (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

def fixedA2NormalizerMulAut (X : ↥(adjointGroup Tag.E6 F))
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F))) :
    MulAut (SL(3, F)) :=
  MulAut.congr (fixedA2RangeEquiv (F := F)).symm
    ((fixedA2AdjRho (F := F)).range.normalizerMonoidHom ⟨X, hX⟩)

theorem fixedA2NormalizerMulAut_apply (X : ↥(adjointGroup Tag.E6 F))
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F))) (A : SL(3, F)) :
    fixedA2AdjRho (F := F) (fixedA2NormalizerMulAut (F := F) X hX A) =
      X * fixedA2AdjRho (F := F) A * X⁻¹ := by
  have hcongr : fixedA2RangeEquiv (F := F) (fixedA2NormalizerMulAut (F := F) X hX A) =
      ((fixedA2AdjRho (F := F)).range.normalizerMonoidHom ⟨X, hX⟩)
        (fixedA2RangeEquiv (F := F) A) := by
    rw [fixedA2NormalizerMulAut, MulAut.congr_apply]
    change fixedA2RangeEquiv (F := F)
      ((fixedA2RangeEquiv (F := F)).symm
        (((fixedA2AdjRho (F := F)).range.normalizerMonoidHom ⟨X, hX⟩)
          (fixedA2RangeEquiv (F := F) A))) = _
    rw [MulEquiv.apply_symm_apply]
  have hval := congrArg Subtype.val hcongr
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at hval
  change fixedA2AdjRho (F := F) (fixedA2NormalizerMulAut (F := F) X hX A) =
    X * fixedA2AdjRho (F := F) A * X⁻¹ at hval
  exact hval

theorem exists_fixedA2NormalizerMulAut (X : ↥(adjointGroup Tag.E6 F))
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F))) :
    ∃ α : MulAut (SL(3, F)),
      ∀ A, fixedA2AdjRho (F := F) (α A) = X * fixedA2AdjRho (F := F) A * X⁻¹ :=
  ⟨fixedA2NormalizerMulAut (F := F) X hX,
    fixedA2NormalizerMulAut_apply (F := F) X hX⟩


section Cover

variable
  [Finite F]

theorem ker_e6Isogeny_le_center :
    (e6Isogeny F).ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F) :=
  ker_e6IsogenyT_le_center (k := F)

theorem ker_e6Isogeny_pow_three (z : ↥(e6Data_valid.minGroup F))
    (hz : e6Isogeny F z = 1) : z ^ 3 = 1 := by
  have hZ3 : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup F)) ∣ 3 := by
    rw [(CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 (k := F)).1]
    exact Nat.gcd_dvd_left 3 _
  have hzmem : z ∈ Subgroup.center ↥(e6Data_valid.minGroup F) :=
    ker_e6Isogeny_le_center (F := F) (MonoidHom.mem_ker.mpr hz)
  exact orderOf_dvd_iff_pow_eq_one.1
    ((Subgroup.orderOf_dvd_natCard _ hzmem).trans hZ3)

theorem exists_fixedA2LiftSection (hF : 4 < Nat.card F) :
    ∃ σ : SL(3, F) →* pullback (fixedA2AdjRho (F := F)) (e6Isogeny F),
      ∀ A, pullbackFst (fixedA2AdjRho (F := F)) (e6Isogeny F) (σ A) = A :=
  TypeA.slHasSections_of_card (d := 3) (K := F)
    (by norm_num) (by omega) (by omega) (by omega)
    (pullback (fixedA2AdjRho (F := F)) (e6Isogeny F))
    (pullbackFst (fixedA2AdjRho (F := F)) (e6Isogeny F))
    (pullbackFst_surjective (β := fixedA2AdjRho (F := F)) (η := e6Isogeny F)
      (e6Isogeny_surjective F))
    (ker_pullbackFst_le_center (β := fixedA2AdjRho (F := F)) (η := e6Isogeny F)
      (ker_e6Isogeny_le_center (F := F)))

def fixedA2LiftSection (hF : 4 < Nat.card F) :
    SL(3, F) →* pullback (fixedA2AdjRho (F := F)) (e6Isogeny F) :=
  (exists_fixedA2LiftSection (F := F) hF).choose

theorem fixedA2LiftSection_spec (hF : 4 < Nat.card F) (A : SL(3, F)) :
    pullbackFst (fixedA2AdjRho (F := F)) (e6Isogeny F) (fixedA2LiftSection (F := F) hF A) =
      A :=
  (exists_fixedA2LiftSection (F := F) hF).choose_spec A

@[expose] def fixedA2Lift (hF : 4 < Nat.card F) : SL(3, F) →* ↥(e6Data_valid.minGroup F) :=
  ((MonoidHom.snd (SL(3, F)) ↥(e6Data_valid.minGroup F)).comp
    (pullback (fixedA2AdjRho (F := F)) (e6Isogeny F)).subtype).comp
    (fixedA2LiftSection (F := F) hF)

theorem fixedA2Lift_pi (hF : 4 < Nat.card F) (A : SL(3, F)) :
    e6Isogeny F (fixedA2Lift (F := F) hF A) = fixedA2AdjRho (F := F) A := by
  have hmem := mem_pullback.1 (fixedA2LiftSection (F := F) hF A).2
  have h1 : ((fixedA2LiftSection (F := F) hF A :
      pullback (fixedA2AdjRho (F := F)) (e6Isogeny F)) : SL(3, F) ×
        ↥(e6Data_valid.minGroup F)).1 = A := fixedA2LiftSection_spec (F := F) hF A
  change e6Isogeny F ((fixedA2LiftSection (F := F) hF A :
    pullback (fixedA2AdjRho (F := F)) (e6Isogeny F)) : SL(3, F) ×
      ↥(e6Data_valid.minGroup F)).2 = _
  rw [← hmem, h1]

theorem e6Isogeny_comp_fixedA2Lift (hF : 4 < Nat.card F) :
    (e6Isogeny F).comp (fixedA2Lift (F := F) hF) = fixedA2AdjRho (F := F) :=
  MonoidHom.ext (fixedA2Lift_pi (F := F) hF)

theorem fixedA2Lift_injective (hF : 4 < Nat.card F) :
    Function.Injective (fixedA2Lift (F := F) hF) := by
  intro A B h
  apply fixedA2AdjRho_injective (F := F)
  rw [← fixedA2Lift_pi (F := F) hF A, ← fixedA2Lift_pi (F := F) hF B, h]

theorem fixedA2Lift_unique (hF : 4 < Nat.card F)
    {lam' : SL(3, F) →* ↥(e6Data_valid.minGroup F)}
    (hlam' : ∀ A, e6Isogeny F (lam' A) = fixedA2AdjRho (F := F) A) :
    lam' = fixedA2Lift (F := F) hF := by
  have hperf : Group.IsPerfect (SL(3, F)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  apply TypeA.eq_of_inv_mul_mem_center (G := ↥(e6Data_valid.minGroup F))
    (hS := hperf.commutator_eq_top)
  intro A
  exact ker_e6Isogeny_le_center (F := F) (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hlam', fixedA2Lift_pi (F := F) hF, inv_mul_cancel])

theorem fixedA2Lift_equivariant (hF : 4 < Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)} (Xhat : ↥(e6Data_valid.minGroup F))
    (hXhat : e6Isogeny F Xhat = X)
    {α : MulAut (SL(3, F))}
    (hα : ∀ A, fixedA2AdjRho (F := F) (α A) =
      X * fixedA2AdjRho (F := F) A * X⁻¹) :
    ∀ A, Xhat * fixedA2Lift (F := F) hF A * Xhat⁻¹ =
      fixedA2Lift (F := F) hF (α A) := by
  have hperf : Group.IsPerfect (SL(3, F)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  let F₁ : SL(3, F) →* ↥(e6Data_valid.minGroup F) :=
    (MulAut.conj Xhat).toMonoidHom.comp (fixedA2Lift (F := F) hF)
  let F₂ : SL(3, F) →* ↥(e6Data_valid.minGroup F) :=
    (fixedA2Lift (F := F) hF).comp α.toMonoidHom
  have heq : F₁ = F₂ := by
    apply TypeA.eq_of_inv_mul_mem_center (G := ↥(e6Data_valid.minGroup F))
      (hS := hperf.commutator_eq_top)
    intro A
    exact ker_e6Isogeny_le_center (F := F) (by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      rw [show F₁ A = Xhat * fixedA2Lift (F := F) hF A * Xhat⁻¹ from rfl,
        show F₂ A = fixedA2Lift (F := F) hF (α A) from rfl,
        map_mul, map_mul, map_inv, hXhat, fixedA2Lift_pi (F := F) hF,
        fixedA2Lift_pi (F := F) hF, hα, inv_mul_cancel])
  intro A
  have h := DFunLike.congr_fun heq A
  simpa [F₁, F₂, MulAut.conj_apply, MonoidHom.comp_apply] using h

theorem fixedA2Lift_normalizer_conj (hF : 4 < Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)}
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F)))
    (Xhat : ↥(e6Data_valid.minGroup F)) (hXhat : e6Isogeny F Xhat = X) (A : SL(3, F)) :
    Xhat * fixedA2Lift (F := F) hF A * Xhat⁻¹ =
      fixedA2Lift (F := F) hF (fixedA2NormalizerMulAut (F := F) X hX A) :=
  fixedA2Lift_equivariant (F := F) hF Xhat hXhat
    (fixedA2NormalizerMulAut_apply (F := F) X hX) A

def fixedA2Ahat (hF : 4 < Nat.card F) (ω : Fˣ) :
    ↥(e6Data_valid.minGroup F) :=
  fixedA2Lift (F := F) hF (fixedA2Scalar (F := F) ω)

theorem fixedA2Ahat_pi (hF : 4 < Nat.card F) (ω : Fˣ) :
    e6Isogeny F (fixedA2Ahat (F := F) hF ω) =
      fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) :=
  fixedA2Lift_pi (F := F) hF _

theorem fixedA2Ahat_pow_three (hF : 4 < Nat.card F) {ω : Fˣ} (hω3 : ω ^ 3 = 1) :
    fixedA2Ahat (F := F) hF ω ^ 3 = 1 := by
  rw [fixedA2Ahat, ← map_pow, fixedA2Scalar_pow_three (F := F) hω3, map_one]

theorem fixedA2Ahat_ne_one (hF : 4 < Nat.card F) {ω : Fˣ} (hω1 : ω ≠ 1) :
    fixedA2Ahat (F := F) hF ω ≠ 1 := by
  intro h
  have h1 : fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) = 1 := by
    rw [← fixedA2Ahat_pi (F := F) hF ω, h, map_one]
  exact fixedA2Scalar_ne_one (F := F) hω1 (fixedA2AdjRho_injective (F := F) (by
    simpa using h1))

theorem fixedA2Ahat_normalizer_fixes (hF : 4 < Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)}
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F)))
    (Xhat : ↥(e6Data_valid.minGroup F)) (hXhat : e6Isogeny F Xhat = X)
    (ω : Fˣ)
    (hfix : X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
      fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) :
    Xhat * fixedA2Ahat (F := F) hF ω * Xhat⁻¹ = fixedA2Ahat (F := F) hF ω := by
  have hβ : fixedA2NormalizerMulAut (F := F) X hX (fixedA2Scalar (F := F) ω) =
      fixedA2Scalar (F := F) ω :=
    fixedA2AdjRho_injective (F := F) (by
      rw [fixedA2NormalizerMulAut_apply (F := F) X hX, hfix])
  have h := fixedA2Lift_normalizer_conj (F := F) hF hX Xhat hXhat
    (fixedA2Scalar (F := F) ω)
  simpa [fixedA2Ahat, hβ] using h

theorem fixedA2Ahat_normalizer_inverts (hF : 4 < Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)}
    (hX : X ∈ Subgroup.normalizer ((fixedA2AdjRho (F := F)).range :
      Set ↥(adjointGroup Tag.E6 F)))
    (Xhat : ↥(e6Data_valid.minGroup F)) (hXhat : e6Isogeny F Xhat = X)
    (ω : Fˣ)
    (hinv : X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
      (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω))⁻¹) :
    Xhat * fixedA2Ahat (F := F) hF ω * Xhat⁻¹ =
      (fixedA2Ahat (F := F) hF ω)⁻¹ := by
  have hβ : fixedA2NormalizerMulAut (F := F) X hX (fixedA2Scalar (F := F) ω) =
      (fixedA2Scalar (F := F) ω)⁻¹ :=
    fixedA2AdjRho_injective (F := F) (by
      rw [fixedA2NormalizerMulAut_apply (F := F) X hX, map_inv, hinv])
  have h := fixedA2Lift_normalizer_conj (F := F) hF hX Xhat hXhat
    (fixedA2Scalar (F := F) ω)
  simpa [fixedA2Ahat, hβ, map_inv] using h

theorem fixedA2Ahat_conj_zpow_of_cube_preimage (hF : 4 < Nat.card F)
    {X : ↥(adjointGroup Tag.E6 F)}
    (Xhat : ↥(e6Data_valid.minGroup F)) (hXhat : e6Isogeny F Xhat = X)
    (ζ ω : Fˣ) (hζ : ζ ^ 3 = ω)
    (B : SL(3, F))
    (hB : fixedA2AdjRho (F := F) B =
      X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ζ) * X⁻¹)
    (m : ℤ)
    (hXω : X * fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω) * X⁻¹ =
      (fixedA2AdjRho (F := F) (fixedA2Scalar (F := F) ω)) ^ m) :
    Xhat * fixedA2Ahat (F := F) hF ω * Xhat⁻¹ =
      (fixedA2Ahat (F := F) hF ω) ^ m := by
  classical
  let t : SL(3, F) := fixedA2Scalar (F := F) ζ
  let s : SL(3, F) := fixedA2Scalar (F := F) ω
  have hts : t ^ 3 = s := by
    dsimp [t, s]
    rw [fixedA2Scalar_pow_three_eq (F := F) ζ, hζ]
  let A : ↥(e6Data_valid.minGroup F) :=
    Xhat * fixedA2Lift (F := F) hF t * Xhat⁻¹
  let C : ↥(e6Data_valid.minGroup F) := fixedA2Lift (F := F) hF B
  let z : ↥(e6Data_valid.minGroup F) := A * C⁻¹
  have hBt : fixedA2AdjRho (F := F) B = X * fixedA2AdjRho (F := F) t * X⁻¹ := by
    simpa [t] using hB
  have hpiA : e6Isogeny F A = X * fixedA2AdjRho (F := F) t * X⁻¹ := by
    dsimp [A]
    rw [map_mul, map_mul, map_inv, hXhat, fixedA2Lift_pi (F := F) hF]
  have hpiC : e6Isogeny F C = fixedA2AdjRho (F := F) B := by
    dsimp [C]
    exact fixedA2Lift_pi (F := F) hF B
  have hzpi : e6Isogeny F z = 1 := by
    dsimp [z]
    rw [map_mul, map_inv, hpiA, hpiC, hBt, mul_inv_cancel]
  have hzmem : z ∈ Subgroup.center ↥(e6Data_valid.minGroup F) :=
    ker_e6Isogeny_le_center (F := F) (MonoidHom.mem_ker.mpr hzpi)
  have hz3 : z ^ 3 = 1 := ker_e6Isogeny_pow_three (F := F) z hzpi
  have hzA : A = z * C := by
    dsimp [z]
    group
  have hzC : Commute z C := (Subgroup.mem_center_iff.mp hzmem C).symm
  have hA3C3 : A ^ 3 = C ^ 3 := by
    calc A ^ 3 = (z * C) ^ 3 := by rw [hzA]
      _ = z ^ 3 * C ^ 3 := hzC.mul_pow 3
      _ = C ^ 3 := by rw [hz3, one_mul]
  have hA3_eq : A ^ 3 = Xhat * fixedA2Lift (F := F) hF s * Xhat⁻¹ := by
    dsimp [A]
    rw [conj_pow, ← map_pow, hts]
  have hXω' : X * fixedA2AdjRho (F := F) s * X⁻¹ =
      (fixedA2AdjRho (F := F) s) ^ m := by
    simpa [s] using hXω
  have hB3 : B ^ 3 = s ^ m := by
    apply fixedA2AdjRho_injective (F := F)
    rw [map_pow, hBt, conj_pow, ← map_pow, hts, hXω', ← map_zpow]
  have hC3_eq : C ^ 3 = (fixedA2Lift (F := F) hF s) ^ m := by
    dsimp [C]
    rw [← map_pow, hB3, map_zpow]
  have hmain : Xhat * fixedA2Lift (F := F) hF s * Xhat⁻¹ =
      (fixedA2Lift (F := F) hF s) ^ m := by
    calc Xhat * fixedA2Lift (F := F) hF s * Xhat⁻¹ = A ^ 3 := hA3_eq.symm
      _ = C ^ 3 := hA3C3
      _ = (fixedA2Lift (F := F) hF s) ^ m := hC3_eq
  simpa [fixedA2Ahat, s] using hmain

end Cover

end CFSG.StandardType.E4bLift
