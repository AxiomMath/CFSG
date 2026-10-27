module

public import CFSG.RankThree.PartOne.KP.CentralCoverThree
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartOne

open CFSG.Fischer CFSG.Assembly.LowTwoRank Matrix

namespace KPUnitaryTorus

@[expose] def omegaUnit : F4ˣ := ⟨F4.ω, F4.ω * F4.ω, by decide, by decide⟩

@[expose] def cubeRootUnit (k : ZMod 3) : F4ˣ := omegaUnit ^ k.val

theorem cubeRootUnit_add (a b : ZMod 3) :
    cubeRootUnit (a + b) = cubeRootUnit a * cubeRootUnit b := by
  revert a b
  decide

theorem cubeRootUnit_zero : cubeRootUnit 0 = 1 := by decide

theorem cubeRootUnit_cube (a : ZMod 3) : cubeRootUnit a ^ 3 = 1 := by
  revert a
  decide

theorem cubeRootUnit_injective : Function.Injective cubeRootUnit := by decide

theorem prod_cubeRootUnit {s : Finset (Fin 6)} (f : Fin 6 → ZMod 3) :
    ∏ i ∈ s, cubeRootUnit (f i) = cubeRootUnit (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp [cubeRootUnit_zero]
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, cubeRootUnit_add]

@[expose] def diagGL (d : Fin 6 → F4ˣ) : GL (Fin 6) F4 where
  val := diagonal fun i => (d i : F4)
  inv := diagonal fun i => ((d i)⁻¹ : F4ˣ)
  val_inv := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]
  inv_val := by
    rw [diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [diagonal_apply_ne _ h, one_apply_ne h]

theorem coe_diagGL (d : Fin 6 → F4ˣ) :
    ((diagGL d : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = diagonal fun i => (d i : F4) :=
  rfl

theorem diagGL_mul (d e : Fin 6 → F4ˣ) : diagGL d * diagGL e = diagGL (d * e) := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, diagonal_mul_diagonal]
  rfl

@[expose] def torusGL (a : Fin 6 → ZMod 3) : GL (Fin 6) F4 := diagGL fun i => cubeRootUnit (a i)

theorem torusGL_add (a b : Fin 6 → ZMod 3) : torusGL (a + b) = torusGL a * torusGL b := by
  rw [torusGL, torusGL, torusGL, diagGL_mul]
  congr 1
  funext i
  exact cubeRootUnit_add _ _

theorem torusGL_mem (a : Fin 6 → ZMod 3) (ha : ∑ i, a i = 0) :
    torusGL a ∈ StatedSU 6 (2 ^ 1) F4 := by
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · show (diagonal fun i => (cubeRootUnit (a i) : F4)).det = 1
    rw [det_diagonal, ← Units.coe_prod, prod_cubeRootUnit, ha, cubeRootUnit_zero]
    rfl
  · show ((diagonal fun i => (cubeRootUnit (a i) : F4)).map (· ^ 2 ^ 1))ᵀ *
      diagonal (fun i => (cubeRootUnit (a i) : F4)) = 1
    rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      have h3 := cubeRootUnit_cube (a i)
      have : ((cubeRootUnit (a i) : F4ˣ) : F4) ^ 3 = 1 := by
        rw [← Units.val_pow_eq_pow_val, h3]
        rfl
      simp only [diagonal_apply_eq, one_apply_eq]
      rw [show (2 : ℕ) ^ 1 = 2 from rfl]
      calc ((cubeRootUnit (a i) : F4ˣ) : F4) ^ 2 * (cubeRootUnit (a i) : F4)
          = ((cubeRootUnit (a i) : F4ˣ) : F4) ^ 3 := by ring
        _ = 1 := this
    · simp [diagonal_apply_ne _ h, one_apply_ne h]

@[expose] def torusElt (a : sumZero6) : StatedSU 6 (2 ^ 1) F4 :=
  ⟨torusGL a, torusGL_mem a (mem_sumZero6.1 a.2)⟩

theorem torusGL_zero : torusGL 0 = 1 := by
  apply Units.ext
  simp only [torusGL, coe_diagGL, Pi.zero_apply, cubeRootUnit_zero, Units.val_one]
  exact diagonal_one

@[expose] noncomputable def unitaryTorusHom :
    Multiplicative sumZero6 →* StatedProj (StatedSU 6 (2 ^ 1) F4) where
  toFun a := QuotientGroup.mk (torusElt (Multiplicative.toAdd a))
  map_one' := by
    show (QuotientGroup.mk (torusElt 0) : StatedProj (StatedSU 6 (2 ^ 1) F4)) = 1
    have : torusElt 0 = 1 := Subtype.ext torusGL_zero
    rw [this]
    rfl
  map_mul' a b := by
    show (QuotientGroup.mk (torusElt (Multiplicative.toAdd a + Multiplicative.toAdd b)) :
      StatedProj (StatedSU 6 (2 ^ 1) F4)) = _
    have : torusElt (Multiplicative.toAdd a + Multiplicative.toAdd b) =
        torusElt (Multiplicative.toAdd a) * torusElt (Multiplicative.toAdd b) :=
      Subtype.ext (torusGL_add _ _)
    rw [this]
    rfl

theorem unitaryTorusHom_eq_one_iff (a : sumZero6) :
    unitaryTorusHom (Multiplicative.ofAdd a) = 1 ↔
      ∃ k : ZMod 3, ∀ i, (a : Fin 6 → ZMod 3) i = k := by
  show (QuotientGroup.mk (torusElt a) : StatedProj (StatedSU 6 (2 ^ 1) F4)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  show torusGL a ∈ StatedScalars (Fin 6) F4 ↔ _
  constructor
  · rintro ⟨c, hc⟩
    have hdiag : ∀ i, ((cubeRootUnit ((a : Fin 6 → ZMod 3) i) : F4ˣ) : F4) = (c : F4) := by
      intro i
      have h1 := congrArg (fun M : GL (Fin 6) F4 => (M : Matrix (Fin 6) (Fin 6) F4) i i) hc
      simpa [Matrix.GeneralLinearGroup.coe_scalar, torusGL, coe_diagGL] using h1.symm
    refine ⟨(a : Fin 6 → ZMod 3) 0, fun i => ?_⟩
    apply cubeRootUnit_injective
    apply Units.ext
    rw [hdiag i, hdiag 0]
  · rintro ⟨k, hk⟩
    refine ⟨cubeRootUnit k, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, torusGL, coe_diagGL, Matrix.scalar_apply]
    congr 1
    funext i
    rw [hk i]

theorem permMatrix_mul_diagonal (σ : Equiv.Perm (Fin 6)) (d : Fin 6 → F4) :
    σ.permMatrix F4 * diagonal d = diagonal (fun i => d (σ i)) * σ.permMatrix F4 := by
  ext i j
  have h1 : (σ.permMatrix F4 * diagonal d) i j = if σ i = j then d j else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ i)]
    · by_cases h : σ i = j
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · intro k _ hk
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Ne.symm hk]
    · simp
  have h2 : (diagonal (fun i => d (σ i)) * σ.permMatrix F4) i j = if σ i = j then d j else 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · by_cases h : σ i = j
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
      · simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, h]
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  rw [h1, h2]

theorem det_permMatrix_F4 (σ : Equiv.Perm (Fin 6)) : (σ.permMatrix F4).det = 1 := by
  rw [det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp only [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    rfl

@[expose] def permGL (σ : Equiv.Perm (Fin 6)) : GL (Fin 6) F4 where
  val := σ.permMatrix F4
  inv := σ⁻¹.permMatrix F4
  val_inv := by rw [← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem permGL_mem (σ : Equiv.Perm (Fin 6)) : permGL σ ∈ StatedSU 6 (2 ^ 1) F4 := by
  apply Subgroup.subset_closure
  refine ⟨det_permMatrix_F4 σ, ?_⟩
  show ((σ.permMatrix F4).map (· ^ 2 ^ 1))ᵀ * σ.permMatrix F4 = 1
  have hmap : (σ.permMatrix F4).map (· ^ 2 ^ 1) = σ.permMatrix F4 := by
    ext i j
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> decide
  rw [hmap, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel,
    permMatrix_one]

theorem unitaryTorus_conj (σ : Equiv.Perm (Fin 6)) :
    ∃ n : StatedProj (StatedSU 6 (2 ^ 1) F4), ∀ a : sumZero6,
      n * unitaryTorusHom (Multiplicative.ofAdd a) * n⁻¹ =
        unitaryTorusHom (Multiplicative.ofAdd (permSumZero σ a)) := by
  refine ⟨QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩, fun a => ?_⟩
  show (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩ : StatedProj (StatedSU 6 (2 ^ 1) F4)) *
      QuotientGroup.mk (torusElt a) * (QuotientGroup.mk ⟨permGL σ⁻¹, permGL_mem σ⁻¹⟩)⁻¹ =
    QuotientGroup.mk (torusElt (permSumZero σ a))
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  show permGL σ⁻¹ * torusGL a * (permGL σ⁻¹)⁻¹ = torusGL (permSumZero σ a)
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, permGL, torusGL, coe_diagGL]
  rw [permMatrix_mul_diagonal]
  rfl

end KPUnitaryTorus

open KPUnitaryTorus in
theorem stated_psu6_central_cover {Y : Type*} [Group Y] [Finite Y]
    (φ : Y →* StatedProj (StatedSU 6 (2 ^ 1) F4)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) :
    ∃ U : Subgroup Y, CFSG.IsElementaryAbelian 3 U ∧ Nat.card U = 3 ^ 4 :=
  central_cover_elementary_three_four φ hφ hker unitaryTorusHom unitaryTorusHom_eq_one_iff
    unitaryTorus_conj

end CFSG.RankThree.PartOne
