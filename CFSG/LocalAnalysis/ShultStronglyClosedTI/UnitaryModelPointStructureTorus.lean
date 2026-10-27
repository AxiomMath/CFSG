module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearUnitaryPoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverTorus

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryModel

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

universe u

theorem exists_subgroup_pow_eq_one_of_isCyclic {G : Type*} [Group G] (T : Subgroup G)
    [IsCyclic T] [Finite T] (n : ℕ) :
    ∃ C : Subgroup G, (C : Set G) = {x | x ∈ T ∧ x ^ n = 1} ∧ IsCyclic C ∧
      Nat.card C = Nat.gcd (Nat.card T) n := by
  let : CommGroup T := IsCyclic.commGroup
  let N := (powMonoidHom n : T →* T).ker
  refine ⟨N.map T.subtype, ?_, ?_, ?_⟩
  · ext x
    simp only [Subgroup.coe_map, Subgroup.coe_subtype, Set.mem_image, SetLike.mem_coe,
      MonoidHom.mem_ker, powMonoidHom_apply, Set.mem_ofPred_eq, N]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxn⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxn), rfl⟩
  · exact isCyclic_of_surjective (T.subtype.subgroupMap N) (T.subtype.subgroupMap_surjective N)
  · rw [Subgroup.card_map_of_injective T.subtype_injective]
    exact IsCyclic.card_powMonoidHom_ker T n

variable {K : Type u} [Field K]

instance instFiniteProjectiveSpecialUnitaryMatrixGroup [Finite K] (J : HermitianForm 3 K) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  have : Finite (ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  Subtype.finite

@[expose] def torusParam (J : HermitianForm 3 K) : Kˣ →* Kˣ :=
  (Units.map J.conj.toMonoidHom)⁻¹

@[simp] theorem torusParam_val (J : HermitianForm 3 K) (c : Kˣ) :
    ((torusParam J c : Kˣ) : K) = (J.conj (c : K))⁻¹ := by
  simp [torusParam]

theorem torusParam_torusParam (J : HermitianForm 3 K) (c : Kˣ) :
    torusParam J (torusParam J c) = c := by
  ext
  simp [map_inv₀, J.conj_involutive (c : K)]

theorem torusParam_eq_inv_pow [Finite K] (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q) (c : Kˣ) :
    torusParam J c = (c ^ q)⁻¹ := by
  ext
  rw [torusParam_val, huppert_II_10_4_conj_eq_frobenius J q hcard hfixed, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val]

@[expose] def torusMatrix (J : HermitianForm 3 K) (c : Kˣ) : Matrix (Fin 3) (Fin 3) K :=
  !![(c : K), 0, 0; 0, J.conj (c : K) / c, 0; 0, 0, (J.conj (c : K))⁻¹]

@[expose] def torusGL (J : HermitianForm 3 K) (c : Kˣ) : GL (Fin 3) K :=
  hermitianTorusGL J (torusParam J c)

@[simp] theorem torusGL_val (J : HermitianForm 3 K) (c : Kˣ) :
    (torusGL J c : Matrix (Fin 3) (Fin 3) K) = torusMatrix J c := by
  rw [torusGL, hermitianTorusGL_val, hermitianTorusMatrix_eq, torusParam_val, map_inv₀,
    J.conj_involutive (c : K), inv_inv, inv_inv, torusMatrix, div_eq_inv_mul]

@[expose] def torusPSU (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Kˣ →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (hermitianTorusPSU J hJ).comp (torusParam J)

@[simp] theorem torusPSU_val (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (c : Kˣ) :
    ((torusPSU J hJ c : ProjectiveSpecialUnitaryMatrixGroup J) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk (torusGL J c) :=
  rfl

theorem range_torusPSU (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (torusPSU J hJ).range = (hermitianTorusPSU J hJ).range := by
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨torusParam J c, rfl⟩
  · rintro ⟨k, rfl⟩
    refine ⟨torusParam J k, ?_⟩
    change hermitianTorusPSU J hJ (torusParam J (torusParam J k)) = _
    rw [torusParam_torusParam]

theorem range_torusPSU_card_isCyclic [Finite K] (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (torusPSU J hJ).range = (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      IsCyclic (torusPSU J hJ).range := by
  rw [range_torusPSU]
  exact unitaryCoverTorus_nativeStructure J q hcard hfixed hJ

theorem torusPSU_commute (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (c d : Kˣ) : Commute (torusPSU J hJ c) (torusPSU J hJ d) :=
  (Commute.all c d).map (torusPSU J hJ)

theorem torusPSU_mem_coordinateStabilizer (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (c : Kˣ) (i : Fin 3) :
    torusPSU J hJ c ∈ unitaryCoordinateStabilizer J i := by
  change ProjGenLinGroup.mk (torusGL J c) • unitaryCoordinatePoint (K := K) i =
    unitaryCoordinatePoint (K := K) i
  rw [unitary_projective_coordinate_maps_iff]
  intro k hk
  rw [torusGL_val, torusMatrix]
  fin_cases i <;> fin_cases k <;> simp_all

theorem mem_range_torusPSU_of_mem_stabilizers (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {g : ProjectiveSpecialUnitaryMatrixGroup J}
    (h0 : g ∈ unitaryCoordinateStabilizer J 0) (h2 : g ∈ unitaryCoordinateStabilizer J 2) :
    g ∈ (torusPSU J hJ).range := by
  obtain ⟨A, hA, hAg⟩ := g.property
  have hc0 : ∀ k : Fin 3, k ≠ 0 → (A : Matrix (Fin 3) (Fin 3) K) k 0 = 0 :=
    (unitary_projective_coordinate_maps_iff A 0 0).mp (by rw [hAg]; exact h0)
  have hc2 : ∀ k : Fin 3, k ≠ 2 → (A : Matrix (Fin 3) (Fin 3) K) k 2 = 0 :=
    (unitary_projective_coordinate_maps_iff A 2 2).mp (by rw [hAg]; exact h2)
  have h10 := hc0 1 (by decide)
  have h20 := hc0 2 (by decide)
  have h02 := hc2 0 (by decide)
  have h12 := hc2 1 (by decide)
  obtain ⟨h01, h21⟩ := unitary_outer_plane_preserves_middle J hJ A
    (J.specialSubgroup_le_unitarySubgroup hA) h10 h12
  obtain ⟨hgram, hdet⟩ := (J.mem_specialSubgroup_iff A).mp hA
  set M : Matrix (Fin 3) (Fin 3) K := (A : Matrix (Fin 3) (Fin 3) K) with hM
  have hnorm : J.conj (M 2 2) * M 0 0 = 1 := by
    simpa [hJ, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, h10, h20,
      h01, h21, h02, h12] using congrArg (fun B => B 2 0) hgram
  have hdet' : M 0 0 * M 1 1 * M 2 2 = 1 := by
    have h := congrArg Units.val hdet
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_fin_three] at h
    simpa [← hM, h10, h20, h01, h21, h02, h12] using h
  have h00 : M 0 0 ≠ 0 := fun h => by simp [h] at hnorm
  have h22 : M 2 2 ≠ 0 := fun h => by simp [h] at hnorm
  have hconj : J.conj (M 0 0) = (M 2 2)⁻¹ := by
    have h := congrArg J.conj hnorm
    rw [map_mul, J.conj_involutive, map_one] at h
    exact eq_inv_of_mul_eq_one_right h
  refine ⟨Units.mk0 (M 0 0) h00, ?_⟩
  apply Subtype.ext
  rw [torusPSU_val, ← hAg]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [torusGL_val, torusMatrix, Units.val_mk0, hconj, inv_inv]
  fin_cases i <;> fin_cases j <;> simp [← hM, h10, h20, h01, h21, h02, h12]
  field_simp
  linear_combination -hdet'

theorem range_torusPSU_eq_inf (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (torusPSU J hJ).range = unitaryCoordinateStabilizer J 0 ⊓ unitaryCoordinateStabilizer J 2 := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    exact ⟨torusPSU_mem_coordinateStabilizer J hJ c 0,
      torusPSU_mem_coordinateStabilizer J hJ c 2⟩
  · rintro g ⟨h0, h2⟩
    exact mem_range_torusPSU_of_mem_stabilizers J hJ h0 h2

theorem hermitianWeylGL_mul_hermitianWeylGL :
    (hermitianWeylGL : GL (Fin 3) K) * hermitianWeylGL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem hermitianWeylPSU_mul_self (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    hermitianWeylPSU J hJ * hermitianWeylPSU J hJ = 1 := by
  apply Subtype.ext
  change ProjGenLinGroup.mk (hermitianWeylGL (K := K)) * ProjGenLinGroup.mk hermitianWeylGL = 1
  rw [← map_mul, hermitianWeylGL_mul_hermitianWeylGL, map_one]

theorem hermitianWeylPSU_smul_zero (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ((hermitianWeylPSU J hJ : ProjectiveSpecialUnitaryMatrixGroup J) :
        ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 2 := by
  rw [hermitianWeylPSU_val, unitary_projective_coordinate_maps_iff]
  intro k hk
  fin_cases k <;> simp_all [hermitianWeylGL, hermitianWeylMatrix]

theorem hermitianWeylPSU_smul_two (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ((hermitianWeylPSU J hJ : ProjectiveSpecialUnitaryMatrixGroup J) :
        ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 0 := by
  rw [hermitianWeylPSU_val, unitary_projective_coordinate_maps_iff]
  intro k hk
  fin_cases k <;> simp_all [hermitianWeylGL, hermitianWeylMatrix]

theorem orderOf_hermitianWeylPSU (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    orderOf (hermitianWeylPSU J hJ) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, hermitianWeylPSU_mul_self]
  · intro h
    have hpt := hermitianWeylPSU_smul_zero J hJ
    rw [h, Subgroup.coe_one, one_smul] at hpt
    rw [unitaryCoordinatePoint, unitaryCoordinatePoint, Projectivization.mk_eq_mk_iff'] at hpt
    obtain ⟨a, ha⟩ := hpt
    simpa using congrFun ha 0

theorem hermitianWeylGL_mul_torusGL (J : HermitianForm 3 K) (c : Kˣ) :
    (hermitianWeylGL : GL (Fin 3) K) * torusGL J c * hermitianWeylGL =
      torusGL J (torusParam J c) := by
  have hc : (c : K) ≠ 0 := Units.ne_zero c
  have hconj : J.conj (c : K) ≠ 0 := (map_ne_zero J.conj).2 hc
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylGL, hermitianWeylMatrix, torusMatrix, Matrix.mul_apply,
      Fin.sum_univ_three, map_inv₀, J.conj_involutive (c : K)]
  field_simp

theorem hermitianWeylPSU_conj_torusPSU (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (c : Kˣ) :
    (hermitianWeylPSU J hJ)⁻¹ * torusPSU J hJ c * hermitianWeylPSU J hJ =
      torusPSU J hJ (torusParam J c) := by
  rw [inv_eq_of_mul_eq_one_right (hermitianWeylPSU_mul_self J hJ)]
  apply Subtype.ext
  change ProjGenLinGroup.mk (hermitianWeylGL (K := K)) * ProjGenLinGroup.mk (torusGL J c) *
      ProjGenLinGroup.mk hermitianWeylGL = ProjGenLinGroup.mk (torusGL J (torusParam J c))
  rw [← map_mul, ← map_mul, hermitianWeylGL_mul_torusGL]

theorem hermitianWeylPSU_inv_mul_mem_range_torusPSU (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw0 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 2)
    (hw2 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 0) :
    (hermitianWeylPSU J hJ)⁻¹ * w ∈ (torusPSU J hJ).range := by
  apply mem_range_torusPSU_of_mem_stabilizers J hJ
  · change (((hermitianWeylPSU J hJ)⁻¹ * w : ProjectiveSpecialUnitaryMatrixGroup J) :
        ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 = _
    rw [Subgroup.coe_mul, mul_smul, hw0, Subgroup.coe_inv, inv_smul_eq_iff,
      hermitianWeylPSU_smul_zero]
  · change (((hermitianWeylPSU J hJ)⁻¹ * w : ProjectiveSpecialUnitaryMatrixGroup J) :
        ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 = _
    rw [Subgroup.coe_mul, mul_smul, hw2, Subgroup.coe_inv, inv_smul_eq_iff,
      hermitianWeylPSU_smul_two]

theorem swap_conj_torusPSU (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw0 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 2)
    (hw2 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 0) (c : Kˣ) :
    w⁻¹ * torusPSU J hJ c * w = torusPSU J hJ (torusParam J c) := by
  obtain ⟨d, hd⟩ := hermitianWeylPSU_inv_mul_mem_range_torusPSU J hJ hw0 hw2
  have hw : w = hermitianWeylPSU J hJ * torusPSU J hJ d := by
    rw [hd, mul_inv_cancel_left]
  have hcomm := (torusPSU_commute J hJ (torusParam J c) d).eq
  calc w⁻¹ * torusPSU J hJ c * w
      = (torusPSU J hJ d)⁻¹ * ((hermitianWeylPSU J hJ)⁻¹ * torusPSU J hJ c *
          hermitianWeylPSU J hJ) * torusPSU J hJ d := by
        rw [hw]
        group
    _ = (torusPSU J hJ d)⁻¹ * (torusPSU J hJ (torusParam J c) * torusPSU J hJ d) := by
        rw [hermitianWeylPSU_conj_torusPSU, mul_assoc]
    _ = torusPSU J hJ (torusParam J c) := by
        rw [hcomm, inv_mul_cancel_left]

theorem swap_inverted_torus [Finite K] (J : HermitianForm 3 K) (f : ℕ)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {w : ProjectiveSpecialUnitaryMatrixGroup J}
    (hw0 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 2)
    (hw2 : (w : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 0) :
    ∃ C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      (C : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
        {x | x ∈ (torusPSU J hJ).range ∧ w⁻¹ * x * w = x⁻¹} ∧
      IsCyclic C ∧ Nat.card C = 2 ^ f - 1 := by
  set q := 2 ^ f
  have hqpos : 0 < q := by positivity
  obtain ⟨hTcard, hTcyc⟩ := range_torusPSU_card_isCyclic J q hcard hfixed hJ
  obtain ⟨C, hC, hCcyc, hCcard⟩ :=
    exists_subgroup_pow_eq_one_of_isCyclic (torusPSU J hJ).range (q - 1)
  refine ⟨C, ?_, hCcyc, ?_⟩
  · rw [hC]
    ext x
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hx => ?_
    obtain ⟨c, rfl⟩ := hx
    rw [swap_conj_torusPSU J hJ hw0 hw2, torusParam_eq_inv_pow J q hcard hfixed, map_inv,
      map_pow, _root_.inv_inj]
    have hq1 : q = q - 1 + 1 := by omega
    constructor
    · intro h
      rw [hq1, pow_succ, h, one_mul]
    · intro h
      rw [hq1, pow_succ] at h
      simpa using h
  · rw [hCcard, hTcard]
    have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
      simpa [mul_comm] using Nat.sq_sub_sq q 1
    rw [hfactor, Nat.mul_div_assoc _ (Nat.gcd_dvd_right 3 (q + 1))]
    exact Nat.gcd_eq_right (dvd_mul_right _ _)

end CFSG.ShultStronglyClosedTI.UnitaryModel
