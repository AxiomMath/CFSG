module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType.ResJCubicBlock

section Linear

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]

noncomputable def frob : E →ₗ[K] E :=
  (FiniteField.frobeniusAlgHom K E).toLinearMap

omit [Fintype E] [FiniteDimensional K E] in
theorem frob_apply (x : E) : frob (K := K) (E := E) x = x ^ Fintype.card K := by
  rw [frob, AlgHom.toLinearMap_apply, FiniteField.frobeniusAlgHom_apply]

theorem det_frob_eq_one (hdeg : Module.finrank K E = 3) :
    LinearMap.det (frob (K := K) (E := E)) = 1 := by
  have hmin : minpoly K (frob (K := K) (E := E)) = Polynomial.X ^ 3 - 1 := by
    simpa [frob, hdeg] using (FiniteField.minpoly_frobeniusAlgHom K E)
  have hchar : (frob (K := K) (E := E)).charpoly = Polynomial.X ^ 3 - 1 := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le ?_ ?_ ?_ ?_
    · simpa using (Polynomial.monic_X_pow_sub_one (R := K) (n := 3) (by norm_num))
    · exact LinearMap.charpoly_monic _
    · simpa [hmin] using LinearMap.minpoly_dvd_charpoly (frob (K := K) (E := E))
    · rw [LinearMap.charpoly_natDegree, hdeg]
      have hnd : (Polynomial.X ^ 3 - 1 : Polynomial K).natDegree = 3 := by
        simpa using (Polynomial.natDegree_X_pow_sub_C (n := 3) (r := (1 : K)))
      rw [hnd]
  rw [LinearMap.det_eq_sign_charpoly_coeff, hchar, hdeg]
  have hcoeff : (Polynomial.X ^ 3 - 1 : Polynomial K).coeff 0 = -1 := by simp
  rw [hcoeff]
  ring

variable {s : ℕ} [NeZero s]

noncomputable def diagLin (y : Fin s → E) : (Fin s → E) →ₗ[K] (Fin s → E) :=
  LinearMap.pi fun i => (Algebra.lmul K E (y i)).comp (LinearMap.proj i)

omit [Fintype K] [Fintype E] [FiniteDimensional K E] [NeZero s] in
theorem diagLin_apply (y : Fin s → E) (v : Fin s → E) (i : Fin s) :
    diagLin (K := K) y v i = y i * v i := by
  simp [diagLin]

omit [Fintype K] [NeZero s] in
theorem diagLin_det (y : Fin s → E) :
    (diagLin (K := K) y).det = ∏ i, Algebra.norm K (y i) := by
  rw [diagLin, LinearMap.det_pi]
  exact Finset.prod_congr rfl fun i _ => (Algebra.norm_apply K (S := E) (y i)).symm

omit [Fintype K] [NeZero s] in
theorem diagLin_det_ne_zero {y : Fin s → E} (hy : ∀ i, y i ≠ 0) :
    (diagLin (K := K) y).det ≠ 0 := by
  have hdet : (diagLin (K := K) y).det = ∏ i, Algebra.norm K (y i) := diagLin_det y
  rw [hdet]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    (Algebra.norm_ne_zero_iff).mpr (hy i)

noncomputable def diagEquiv (y : Fin s → E) (hy : ∀ i, y i ≠ 0) :
    (Fin s → E) ≃ₗ[K] (Fin s → E) :=
  LinearMap.equivOfIsUnitDet (f := diagLin (K := K) y) (isUnit_iff_ne_zero.mpr (diagLin_det_ne_zero hy))

omit [Fintype K] [NeZero s] in
theorem diagEquiv_coe (y : Fin s → E) (hy : ∀ i, y i ≠ 0) :
    ((diagEquiv y hy : (Fin s → E) ≃ₗ[K] (Fin s → E)) : (Fin s → E) →ₗ[K] (Fin s → E)) =
      diagLin (K := K) y := by
  unfold diagEquiv
  exact LinearMap.coe_equivOfIsUnitDet (f := diagLin (K := K) y)
    (h := isUnit_iff_ne_zero.mpr (diagLin_det_ne_zero hy))

noncomputable def frobFirst : (Fin s → E) →ₗ[K] (Fin s → E) :=
  LinearMap.pi fun i =>
    (if i = 0 then frob (K := K) (E := E) else LinearMap.id).comp (LinearMap.proj i)

omit [Fintype E] [FiniteDimensional K E] in
theorem frobFirst_apply (v : Fin s → E) (i : Fin s) :
    frobFirst (K := K) (E := E) (s := s) v i =
      if i = 0 then (v i) ^ Fintype.card K else v i := by
  by_cases hi : i = 0
  · subst hi
    simp [frobFirst, frob_apply]
  · simp [frobFirst, hi]

theorem frobFirst_det (hdeg : Module.finrank K E = 3) :
    (frobFirst (K := K) (E := E) (s := s)).det = 1 := by
  rw [frobFirst, LinearMap.det_pi]
  rw [Finset.prod_eq_single (0 : Fin s)]
  · simp [det_frob_eq_one hdeg]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin s)) h

end Linear

section Zeta

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)

noncomputable def zetaLin : (Fin s → E) →ₗ[K] (Fin s → E) :=
  LinearMap.pi fun i =>
    (if i = 0 then Algebra.lmul K E (algebraMap K E ζ) else LinearMap.id).comp
      (LinearMap.proj i)

omit [Fintype K] [Fintype E] [FiniteDimensional K E] in
theorem zetaLin_apply (v : Fin s → E) (i : Fin s) :
    zetaLin (ζ := ζ) (K := K) (E := E) v i =
      if i = 0 then algebraMap K E ζ * v i else v i := by
  by_cases hi : i = 0
  · subst hi
    simp [zetaLin, Algebra.smul_def]
  · simp [zetaLin, hi]

omit [Fintype K] [Fintype E] [FiniteDimensional K E] in
theorem zetaLin_pow_apply (m : ℕ) (v : Fin s → E) (i : Fin s) :
    ((zetaLin (ζ := ζ) (K := K) (E := E)) ^ m) v i =
      if i = 0 then (algebraMap K E ζ) ^ m * v i else v i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ']
    change (zetaLin (ζ := ζ) (K := K) (E := E))
      (((zetaLin (ζ := ζ) (K := K) (E := E)) ^ m) v) i = _
    rw [zetaLin_apply, ih]
    by_cases hi : i = 0
    · subst hi
      simp [pow_succ', mul_assoc]
    · simp [hi]

omit [Fintype K] in
theorem zetaLin_det (hζ3 : ζ ^ 3 = 1) (hdeg : Module.finrank K E = 3) :
    (zetaLin (ζ := ζ) (K := K) (E := E) (s := s)).det = 1 := by
  rw [zetaLin, LinearMap.det_pi]
  rw [Finset.prod_eq_single (0 : Fin s)]
  · rw [if_pos rfl]
    rw [← Algebra.norm_apply K (S := E) (algebraMap K E ζ), Algebra.norm_algebraMap, hdeg, hζ3]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin s)) h

noncomputable def zetaEquiv (hζ3 : ζ ^ 3 = 1) (hdeg : Module.finrank K E = 3) :
    (Fin s → E) ≃ₗ[K] (Fin s → E) :=
  LinearMap.equivOfIsUnitDet (f := zetaLin (ζ := ζ))
    (isUnit_iff_ne_zero.mpr (by rw [zetaLin_det (ζ := ζ) hζ3 hdeg]; exact one_ne_zero))

omit [Fintype K] in
theorem zetaEquiv_coe (hζ3 : ζ ^ 3 = 1) (hdeg : Module.finrank K E = 3) :
    ((zetaEquiv (ζ := ζ) hζ3 hdeg : (Fin s → E) ≃ₗ[K] (Fin s → E)) :
      (Fin s → E) →ₗ[K] (Fin s → E)) = zetaLin (ζ := ζ) := by
  unfold zetaEquiv
  exact LinearMap.coe_equivOfIsUnitDet (f := zetaLin (ζ := ζ) (K := K) (E := E) (s := s))
    (h := isUnit_iff_ne_zero.mpr (by rw [zetaLin_det (ζ := ζ) hζ3 hdeg]; exact one_ne_zero))

end Zeta

section Commutator

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)

omit [Fintype K] [NeZero s] in
theorem diagEquiv_apply (y : Fin s → E) (hy : ∀ i, y i ≠ 0) (v : Fin s → E) :
    diagEquiv (K := K) (E := E) (s := s) y hy v =
      diagLin (K := K) y v := by
  change ((diagEquiv (K := K) (E := E) (s := s) y hy :
    (Fin s → E) ≃ₗ[K] (Fin s → E)) :
    (Fin s → E) →ₗ[K] (Fin s → E)) v = _
  rw [diagEquiv_coe]

omit [Fintype K] in
theorem zetaEquiv_apply (hζ3 : ζ ^ 3 = 1) (hdeg : Module.finrank K E = 3)
    (v : Fin s → E) :
    zetaEquiv (ζ := ζ) hζ3 hdeg v = zetaLin (ζ := ζ) (K := K) (E := E) v := by
  change ((zetaEquiv (ζ := ζ) hζ3 hdeg : (Fin s → E) ≃ₗ[K] (Fin s → E)) :
    (Fin s → E) →ₗ[K] (Fin s → E)) v = _
  rw [zetaEquiv_coe]

omit [Fintype K] in
theorem zetaEquiv_pow_apply (hζ3 : ζ ^ 3 = 1) (hdeg : Module.finrank K E = 3)
    (m : ℕ) (v : Fin s → E) :
    (zetaEquiv (ζ := ζ) hζ3 hdeg ^ m) v =
      (zetaLin (ζ := ζ) (K := K) (E := E) ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', LinearEquiv.mul_apply, pow_succ']
    change zetaEquiv (ζ := ζ) hζ3 hdeg
      (((zetaEquiv (ζ := ζ) hζ3 hdeg) ^ m) v) =
        zetaLin (ζ := ζ) (K := K) (E := E)
          (((zetaLin (ζ := ζ) (K := K) (E := E)) ^ m) v)
    rw [zetaEquiv_apply, ih]

omit [Fintype E] [FiniteDimensional K E] in
theorem pow_card_eq_zeta_mul {y : E} {lam : ℕ}
    (hy : y ^ (Fintype.card K - 1) = (algebraMap K E ζ) ^ lam) :
    y ^ Fintype.card K = (algebraMap K E ζ) ^ lam * y := by
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  calc y ^ Fintype.card K = y ^ ((Fintype.card K - 1) + 1) := by
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    _ = y ^ (Fintype.card K - 1) * y := by rw [pow_succ]
    _ = (algebraMap K E ζ) ^ lam * y := by rw [hy]

omit [Fintype E] [FiniteDimensional K E] in
theorem frobFirst_comp_diagLin (_hdeg : Module.finrank K E = 3) (y : Fin s → E)
    (lam : ℕ) (hy : ∀ i, y i ^ (Fintype.card K - 1) = (algebraMap K E ζ) ^ lam) :
    (frobFirst (K := K) (E := E) (s := s)).comp (diagLin (K := K) y) =
      ((zetaLin (ζ := ζ) (K := K) (E := E) (s := s)) ^ lam).comp
        ((diagLin (K := K) y).comp (frobFirst (K := K) (E := E) (s := s))) := by
  apply LinearMap.ext
  intro v
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [LinearMap.comp_apply, frobFirst_apply, diagLin_apply, zetaLin_pow_apply]
    rw [mul_pow, pow_card_eq_zeta_mul (ζ := ζ) (hy 0)]
    ring
  · simp [frobFirst_apply, diagLin_apply, zetaLin_pow_apply, hi]

theorem frobFirst_det_ne_zero (hdeg : Module.finrank K E = 3) :
    (frobFirst (K := K) (E := E) (s := s)).det ≠ 0 := by
  rw [frobFirst_det (K := K) (E := E) hdeg]
  exact one_ne_zero

noncomputable def frobEquiv (hdeg : Module.finrank K E = 3) :
    (Fin s → E) ≃ₗ[K] (Fin s → E) :=
  LinearMap.equivOfIsUnitDet (f := frobFirst (K := K) (E := E) (s := s))
    (isUnit_iff_ne_zero.mpr (frobFirst_det_ne_zero (K := K) (E := E) hdeg))

theorem frobEquiv_coe (hdeg : Module.finrank K E = 3) :
    ((frobEquiv (K := K) (E := E) (s := s) hdeg :
        (Fin s → E) ≃ₗ[K] (Fin s → E)) : (Fin s → E) →ₗ[K] (Fin s → E)) =
      frobFirst (K := K) (E := E) (s := s) := by
  unfold frobEquiv
  exact LinearMap.coe_equivOfIsUnitDet (f := frobFirst (K := K) (E := E) (s := s))
    (h := isUnit_iff_ne_zero.mpr (frobFirst_det_ne_zero (K := K) (E := E) hdeg))

theorem frobEquiv_apply (hdeg : Module.finrank K E = 3) (v : Fin s → E) :
    frobEquiv (K := K) (E := E) (s := s) hdeg v =
      frobFirst (K := K) (E := E) (s := s) v := by
  change ((frobEquiv (K := K) (E := E) (s := s) hdeg :
    (Fin s → E) ≃ₗ[K] (Fin s → E)) : (Fin s → E) →ₗ[K] (Fin s → E)) v = _
  rw [frobEquiv_coe]

theorem frobEquiv_mul_diagEquiv (hdeg : Module.finrank K E = 3) (y : Fin s → E)
    (hy0 : ∀ i, y i ≠ 0) (lam : ℕ)
    (hy : ∀ i, y i ^ (Fintype.card K - 1) = (algebraMap K E ζ) ^ lam) :
    frobEquiv (K := K) (E := E) hdeg * diagEquiv y hy0 =
      (zetaEquiv (ζ := ζ) hζ3 hdeg) ^ lam * diagEquiv y hy0 *
        frobEquiv (K := K) (E := E) hdeg := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [frobEquiv_apply, diagEquiv_apply (K := K) (E := E) (s := s) y hy0 v,
    zetaEquiv_pow_apply, diagEquiv_apply (K := K) (E := E) (s := s) y hy0,
    frobEquiv_apply]
  exact congrArg (fun f : (Fin s → E) →ₗ[K] (Fin s → E) => f v)
    (frobFirst_comp_diagLin (ζ := ζ) (K := K) (E := E) (s := s) hdeg y lam hy)

theorem frobEquiv_conj_diagEquiv (hdeg : Module.finrank K E = 3) (y : Fin s → E)
    (hy0 : ∀ i, y i ≠ 0) (lam : ℕ)
    (hy : ∀ i, y i ^ (Fintype.card K - 1) = (algebraMap K E ζ) ^ lam) :
    frobEquiv (K := K) (E := E) hdeg * diagEquiv y hy0 *
        (frobEquiv (K := K) (E := E) hdeg)⁻¹ =
      (zetaEquiv (ζ := ζ) hζ3 hdeg) ^ lam * diagEquiv y hy0 := by
  rw [frobEquiv_mul_diagEquiv (ζ := ζ) (K := K) (E := E) (s := s)
    (hζ3 := hζ3) hdeg y hy0 lam hy]
  group

end Commutator

section GroupModel

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [FiniteDimensional K E]
  {s : ℕ} [NeZero s]
variable (ζ : K) (hζ3 : ζ ^ 3 = 1) (hζ1 : ζ ≠ 1)
variable (hdeg : Module.finrank K E = 3)
variable (y : Fin s → E) (hy0 : ∀ i, y i ≠ 0)

abbrev GLV (K E : Type*) [Field K] [Field E] [Algebra K E] [Fintype K] (s : ℕ) :=
  (Fin s → E) ≃ₗ[K] (Fin s → E)

abbrev SLV (K E : Type*) [Field K] [Field E] [Algebra K E] [Fintype K] (s : ℕ) :=
  SpecialLinearGroup K (Fin s → E)

noncomputable abbrev conjSL (Y : GLV K E s) (g : SLV K E s) : SLV K E s :=
  SpecialLinearGroup.congr_linearEquiv (R := K) (V := Fin s → E) (W := Fin s → E) Y g

omit [Fintype E] [FiniteDimensional K E] [NeZero s] in
theorem conjSL_coe (Y : GLV K E s) (g : SLV K E s) :
    ((conjSL (K := K) (E := E) (s := s) Y g : SLV K E s) : GLV K E s) =
      Y * (g : GLV K E s) * Y⁻¹ := by
  simp only [conjSL, SpecialLinearGroup.congr_linearEquiv_coe_apply]
  ext v
  simp [LinearEquiv.mul_apply]

@[expose] noncomputable def zSL : SLV K E s :=
  ⟨zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg, by
    apply Units.ext
    rw [LinearEquiv.coe_det, zetaEquiv_coe (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg,
      zetaLin_det (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg]
    simp⟩

@[expose] noncomputable def nSL : SLV K E s :=
  ⟨frobEquiv (K := K) (E := E) (s := s) hdeg, by
    apply Units.ext
    rw [LinearEquiv.coe_det, frobEquiv_coe (K := K) (E := E) (s := s) hdeg,
      frobFirst_det (K := K) (E := E) (s := s) hdeg]
    simp⟩

theorem zSL_pow_three : (zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg ^ 3 :
    SLV K E s) = 1 := by
  apply SpecialLinearGroup.ext
  intro v
  change ((zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg ^ 3) v) =
    (1 : GLV K E s) v
  rw [zetaEquiv_pow_apply]
  funext i
  rw [zetaLin_pow_apply]
  have hζE : (algebraMap K E ζ) ^ 3 = 1 := by
    rw [← map_pow, hζ3, map_one]
  rw [hζE, one_mul]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]

omit [Fintype K] [Fintype E] [FiniteDimensional K E] in
theorem diagLin_comp_zetaLin :
    ((diagLin (K := K) y).comp (zetaLin (ζ := ζ) (K := K) (E := E))) =
      (zetaLin (ζ := ζ) (K := K) (E := E)).comp (diagLin (K := K) y) := by
  apply LinearMap.ext
  intro v
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [diagLin_apply, zetaLin_apply, mul_assoc, mul_comm]
  · simp [diagLin_apply, zetaLin_apply, hi]

omit [Fintype K] in
theorem diagEquiv_mul_zetaEquiv :
    diagEquiv (K := K) (E := E) (s := s) y hy0 *
        zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg =
      zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg *
        diagEquiv (K := K) (E := E) (s := s) y hy0 := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [diagEquiv_apply (K := K) (E := E) (s := s) y hy0,
    zetaEquiv_apply (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg,
    zetaEquiv_apply (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg,
    diagEquiv_apply (K := K) (E := E) (s := s) y hy0]
  exact congrArg (fun f : (Fin s → E) →ₗ[K] (Fin s → E) => f v i)
    (diagLin_comp_zetaLin (ζ := ζ) (K := K) (E := E) (s := s) y)

theorem frobEquiv_mul_zetaEquiv (hdeg : Module.finrank K E = 3) :
    frobEquiv (K := K) (E := E) (s := s) hdeg *
        zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg =
      zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg *
        frobEquiv (K := K) (E := E) (s := s) hdeg := by
  apply LinearEquiv.ext
  intro v
  funext i
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  rw [frobEquiv_apply, zetaEquiv_apply, zetaEquiv_apply, frobEquiv_apply]
  by_cases hi : i = 0
  · subst hi
    simp [frobFirst_apply, zetaLin_apply, mul_pow]
  · simp [frobFirst_apply, zetaLin_apply, hi]

theorem zSL_coe :
    ((zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg : SLV K E s) : GLV K E s) =
      zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg := rfl

theorem nSL_coe :
    ((nSL (K := K) (E := E) (s := s) hdeg : SLV K E s) : GLV K E s) =
      frobEquiv (K := K) (E := E) (s := s) hdeg := rfl

theorem nSL_conj_zSL :
    nSL (K := K) (E := E) (s := s) hdeg *
        zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg *
        (nSL (K := K) (E := E) (s := s) hdeg)⁻¹ =
      zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg := by
  apply Subtype.ext
  simp only [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv,
    zSL_coe, nSL_coe]
  rw [frobEquiv_mul_zetaEquiv (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg]
  group

theorem zSL_not_scalar (hs : 2 ≤ s) (hζ1 : ζ ≠ 1) :
    ¬ ∃ a : K, ∀ v : Fin s → E,
      ((zSL (ζ := ζ) (K := K) (E := E) (s := s) hζ3 hdeg : SLV K E s) : GLV K E s) v = a • v := by
  rintro ⟨a, ha⟩
  let e0 : Fin s := 0
  let e1 : Fin s := ⟨1, by omega⟩
  have h0 := congrFun (ha (Pi.single e0 1)) e0
  have h1 := congrFun (ha (Pi.single e1 1)) e1
  have h0' : a = ζ := by
    simpa [zSL, zetaEquiv_apply, zetaLin_apply, e0, Algebra.smul_def] using h0.symm
  have h1' : a = 1 := by
    have he1 : e1 ≠ (0 : Fin s) := by
      simp [e1]
    have h1a : algebraMap K E a = 1 := by
      simpa [zSL, zetaEquiv_apply, zetaLin_apply, e1, he1, Algebra.smul_def] using h1.symm
    exact (algebraMap K E).injective (by simpa using h1a)
  exact hζ1 (by rw [← h0', h1'])

end GroupModel

end CFSG.StandardType.ResJCubicBlock
