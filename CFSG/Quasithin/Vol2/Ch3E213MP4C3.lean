module

public import CFSG.Quasithin.Vol2.Ch3E213MP4C2
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryRealizationTransport

public section

namespace CFSG.Quasithin.Ch3E213M.P4C

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.LocalCriterionNoncentralPairAction

theorem exists_cube_eq {M : Type*} [CommGroup M] {x s : M} (k : ℕ) (h : x ^ 2 ^ k = s ^ 3) :
    ∃ u v : ℤ, (s ^ u * x ^ v) ^ 3 = x := by
  have h23 : IsCoprime (2 : ℤ) 3 := Int.isCoprime_iff_gcd_eq_one.mpr (by norm_num)
  obtain ⟨u, v, huv⟩ := h23.pow_left (m := k)
  refine ⟨u, v, ?_⟩
  have e1 : (s ^ u) ^ 3 = x ^ (u * 2 ^ k) := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← h,
      ← zpow_natCast x (2 ^ k), ← _root_.zpow_mul]
    congr 1
    push_cast
    ring
  have e2 : (x ^ v) ^ 3 = x ^ (v * 3) := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
    rfl
  rw [mul_pow, e1, e2, ← _root_.zpow_add, huv, zpow_one]

variable {K : Type} [Field K]

theorem det_conjTranspose (J : HermitianForm 3 K) (A : Matrix (Fin 3) (Fin 3) K) :
    (J.conjTranspose A).det = J.conj A.det := by
  have : J.conjTranspose A = (A.map J.conj)ᵀ := by
    ext i j
    rfl
  rw [this, Matrix.det_transpose, ← RingEquiv.coe_toRingHom, RingHom.map_det]
  rfl

theorem norm_det_eq_one (J : HermitianForm 3 K) {A : GL (Fin 3) K} (hA : A ∈ J.unitarySubgroup) :
    J.conj (A : Matrix (Fin 3) (Fin 3) K).det * (A : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  have h := congrArg Matrix.det ((J.mem_unitarySubgroup_iff A).mp hA)
  rw [Matrix.det_mul, Matrix.det_mul, det_conjTranspose] at h
  have hJ := J.form_nondegenerate
  have : (J.conj (A : Matrix (Fin 3) (Fin 3) K).det * (A : Matrix (Fin 3) (Fin 3) K).det - 1) *
      J.form.det = 0 := by linear_combination h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hJ)

theorem scalar_mem_unitary_iff (J : HermitianForm 3 K) (c : Kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ J.unitarySubgroup ↔ J.conj (c : K) * c = 1 := by
  have hconj : J.conjTranspose (Matrix.scalar (Fin 3) (c : K)) =
      Matrix.scalar (Fin 3) (J.conj (c : K)) := by
    ext i j
    simp only [HermitianForm.conjTranspose, Matrix.scalar_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have key : J.conjTranspose (Matrix.scalar (Fin 3) (c : K)) * J.form *
      Matrix.scalar (Fin 3) (c : K) = (J.conj (c : K) * c) • J.form := by
    rw [hconj, Matrix.scalar_apply, Matrix.scalar_apply]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [J.mem_unitarySubgroup_iff, GeneralLinearGroup.coe_scalar, key]
  constructor
  · intro h
    have hF : J.form ≠ 0 := fun h0 => J.form_nondegenerate (by rw [h0, Matrix.det_zero])
    have : (J.conj (c : K) * c - 1) • J.form = 0 := by rw [sub_smul, h, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hF)
  · intro h
    rw [h, one_smul]

theorem exists_lowerRoot [CharP K 2] (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    ∃ g : GL (Fin 3) K, g ∈ J.specialSubgroup ∧
      (g : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 1, 0; 1, 0, 1] := by
  have hsq : (!![1, 0, 0; 0, 1, 0; 1, 0, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![1, 0, 0; 0, 1, 0; 1, 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
  refine ⟨⟨_, _, hsq, hsq⟩, (J.mem_specialSubgroup_iff _).mpr ⟨?_, ?_⟩, rfl⟩
  · rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]
  · ext
    change Matrix.det !![(1 : K), 0, 0; 0, 1, 0; 1, 0, 1] = 1
    simp [Matrix.det_fin_three]

variable [Finite K]

theorem exists_inner (J : HermitianForm 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}
    (hβB : ∀ x ∈ unitaryCoordinateStabilizer J 0, β x ∈ unitaryCoordinateStabilizer J 0)
    (hβT : ∀ c : Kˣ, β (torusPSU J hJ c) * (torusPSU J hJ c)⁻¹ ∈
      (hermitianUnipotentPSU J hJ).range)
    {k : ℕ} (hβk : β ^ 2 ^ k = 1) :
    ∃ g : ProjectiveSpecialUnitaryMatrixGroup J, ∀ x, β x = g * x * g⁻¹ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  obtain ⟨σ, A, hA, hβ⟩ :=
    ProperTwoGeneratedCore.HighRankPair.unitaryAutomorphismRealization K J f hf hcard hfixed hJ β
  have hσ := eq_refl_of_cube hf hcard (cube_fixed_of_centralizes J hf hcard hfixed hJ hβB hβT hβ)
  subst hσ
  have hreal : ∀ (y : ProjectiveSpecialUnitaryMatrixGroup J) (M : GL (Fin 3) K),
      (y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M →
      (β y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (A * M * A⁻¹) := fun y M hyM => by
    rw [realize_mk hβ y M hyM]
    rfl
  have hpow : ∀ (m : ℕ) (y : ProjectiveSpecialUnitaryMatrixGroup J) (M : GL (Fin 3) K),
      (y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M →
      ((β ^ m) y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (A ^ m * M * (A ^ m)⁻¹) := by
    intro m
    induction m with
    | zero => intro y M hyM; simpa using hyM
    | succ m ih =>
      intro y M hyM
      rw [pow_succ, MulAut.mul_apply, ih _ _ (hreal y M hyM)]
      congr 1
      group
  have hconj : ∀ (y : ProjectiveSpecialUnitaryMatrixGroup J) (M : GL (Fin 3) K),
      (y : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk M →
      ∃ c : K, ((A ^ 2 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
        c • ((M : Matrix (Fin 3) (Fin 3) K) * (A ^ 2 ^ k : GL (Fin 3) K)) := by
    intro y M hyM
    have h := hpow (2 ^ k) y M hyM
    rw [hβk, MulAut.one_apply, hyM] at h
    obtain ⟨c, -, hc⟩ := exists_smul_of_mk_eq h
    refine ⟨c, ?_⟩
    rw [← Matrix.smul_mul, ← hc, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have hone : J.conj 1 = 1 := map_one _
  obtain ⟨c₁, h1⟩ := hconj _ _ (hermitianUnipotentPSU_val J hJ (centralCoord J 1 hone))
  rw [centralCoord_matrix] at h1
  obtain ⟨Q, hQ, hQv⟩ := exists_lowerRoot J hJ
  obtain ⟨c₂, h2⟩ := hconj ⟨ProjGenLinGroup.mk Q, Subgroup.mem_map_of_mem _ hQ⟩ Q rfl
  rw [hQv] at h2
  obtain ⟨t, ht⟩ := huppert_II_10_4_trace_surjective J (2 ^ f) hcard hfixed (1 * J.conj 1)
    (by rw [map_mul, J.conj_involutive, mul_comm])
  let z : hermitianUnipotentCoord J := ⟨(1, t), by
    change t + J.conj t + 1 * J.conj 1 = 0
    rw [ht]
    exact CharTwo.add_self_eq_zero _⟩
  obtain ⟨c₃, h3⟩ := hconj _ _ (hermitianUnipotentPSU_val J hJ z)
  rw [hermitianUnipotentGL_val, hermitianUnipotentMatrix_eq] at h3
  have hscal := eq_scalar_of_conj (GeneralLinearGroup.det_ne_zero _) one_ne_zero h1 h2 h3
  have hs0 : ((A ^ 2 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    apply GeneralLinearGroup.det_ne_zero (A ^ 2 ^ k)
    rw [hscal, h0, Matrix.scalar_apply, Matrix.diagonal_zero, Matrix.det_zero]
  set s : Kˣ := Units.mk0 _ hs0
  have hAs : A ^ 2 ^ k = GeneralLinearGroup.scalar (Fin 3) s :=
    Units.ext (by rw [GeneralLinearGroup.coe_scalar]; exact hscal)
  have hxs : GeneralLinearGroup.det A ^ 2 ^ k = s ^ 3 := by
    rw [← map_pow, hAs, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  let nrm : Kˣ →* Kˣ := Units.map (J.conj : K →* K) * MonoidHom.id Kˣ
  have hnrm : ∀ u : Kˣ, u ∈ nrm.ker ↔ J.conj (u : K) * u = 1 := fun u => by
    rw [MonoidHom.mem_ker, Units.ext_iff]
    rfl
  have hx : GeneralLinearGroup.det A ∈ nrm.ker := by
    rw [hnrm, GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one J hA
  have hsn : s ∈ nrm.ker := (hnrm s).mpr ((scalar_mem_unitary_iff J s).mp
    (hAs ▸ J.unitarySubgroup.pow_mem hA _))
  obtain ⟨u, v, huv⟩ := exists_cube_eq k hxs
  set c := s ^ u * GeneralLinearGroup.det A ^ v with hc
  have hcn : c⁻¹ ∈ nrm.ker := nrm.ker.inv_mem (nrm.ker.mul_mem (nrm.ker.zpow_mem hsn u)
    (nrm.ker.zpow_mem hx v))
  set A' := GeneralLinearGroup.scalar (Fin 3) c⁻¹ * A
  have hA' : A' ∈ J.specialSubgroup := by
    refine (J.mem_specialSubgroup_iff A').mpr ⟨(J.mem_unitarySubgroup_iff A').mp
      (J.unitarySubgroup.mul_mem ((scalar_mem_unitary_iff J _).mpr ((hnrm _).mp hcn)) hA), ?_⟩
    rw [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, inv_pow, huv, inv_mul_cancel]
  have hmk : ProjGenLinGroup.mk A' = ProjGenLinGroup.mk A := by
    rw [map_mul, ProjGenLinGroup.mk_scalar, one_mul]
  refine ⟨⟨ProjGenLinGroup.mk A', Subgroup.mem_map_of_mem _ hA'⟩, fun x => Subtype.ext ?_⟩
  obtain ⟨M, -, hxM⟩ := Subgroup.mem_map.mp x.2
  rw [hreal x M hxM.symm, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  change _ = ProjGenLinGroup.mk A' * (x : ProjGenLinGroup (Fin 3) K) * (ProjGenLinGroup.mk A')⁻¹
  rw [hmk, ← hxM, map_mul, map_mul, map_inv]

end CFSG.Quasithin.Ch3E213M.P4C
