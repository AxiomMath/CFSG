module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveLieGen
public import CFSG.Quasithin.H13.NQCatLieOverRank2
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.H13.FiveNorm.LieL3

open Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem isUpperTriangular_pow {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (hM : M.IsUpperTriangular)
    (k : ℕ) : (M ^ k).IsUpperTriangular := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact Matrix.blockTriangular_one
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hM

omit [Finite K] in
theorem matrix_pow_apply_self {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (hM : M.IsUpperTriangular)
    (k : ℕ) (i : Fin n) : (M ^ k) i i = M i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_apply_self_of_isUpperTriangular (isUpperTriangular_pow hM k) hM, ih,
      pow_succ]

omit [Finite K] in
theorem pow_apply_self {n : ℕ} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ upperTriangular n K) (k : ℕ) (i : Fin n) :
    ((A ^ k : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      (A : Matrix (Fin n) (Fin n) K) i i ^ k :=
  (congrFun (congrFun (Matrix.SpecialLinearGroup.coe_pow A k) i) i).trans
    (matrix_pow_apply_self (mem_upperTriangular_iff_isUpperTriangular.mp hA) k i)

theorem pow_card_sub_one_mem_unitriangular {n : ℕ} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ upperTriangular n K) : A ^ (Nat.card K - 1) ∈ unitriangular n K := by
  have := Fintype.ofFinite K
  refine ⟨Subgroup.pow_mem _ hA _, fun i => (pow_apply_self hA _ i).trans ?_⟩
  rw [Nat.card_eq_fintype_card]
  apply FiniteField.pow_card_sub_one_eq_one
  intro h0
  have h1 := coe_inv_apply_self_of_isUpperTriangular
    (mem_upperTriangular_iff_isUpperTriangular.mp hA) i
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

theorem powOver_projectiveSL [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    PowOver (projectiveSL 3 K) (projUnitriangular 3 K) (Nat.card K - 1) := by
  intro H hUH hH x hx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := NQCat.solvOver_projectiveSL hK4 H hUH hH hx
  rw [normalizer_projUnitriangular 2] at hN
  obtain ⟨A, hA, rfl⟩ := hN
  exact ⟨_, pow_card_sub_one_mem_unitriangular hA, map_pow _ _ _⟩

theorem fiveRigid_projectiveSL [CharP K 2] (hk : Nat.card K = 4) :
    FiveRigid (projectiveSL 3 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (projectiveSL 3 K) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 2
      ⟨⟨Nat.prime_two, by norm_num, by decide⟩, K, inferInstance, inferInstance,
        by rw [hk]; norm_num, ⟨(Setup.X7a.statedSLEquivProjectiveSL 3 K).symm⟩⟩).2
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have : Group.IsPerfect (projectiveSL 3 K) :=
    Group.IsPerfect.ofSurjective (f := proj 3 K) (proj_surjective 3 K)
  have hZ : Subgroup.center (projectiveSL 3 K) = ⊥ := center_eq_bot_of_isPerfect
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hcardT : Nat.card (Kˣ ⋊[LinearThreeFourOuter.inversionAction Kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) = 12 := by
    rw [SemidirectProduct.card, LinearThreeFourOuter.card_units_eq_three hk, Nat.card_prod]
    simp
  have hinn : FiveInner (projectiveSL 3 K) := by
    refine fiveInner_of_hom Ψ (fun α hα => ?_)
      (eq_one_of_pow_five_eq_one (by rw [hcardT]; norm_num))
    have hmem : α ∈ Ψ.ker := hα
    rw [hker] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact ⟨x, hx.symm⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have hU : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hK4 := NQCat.exists_finset_card_four_of_card (k := 2) le_rfl (by rw [hk]; norm_num)
  exact ⟨hZ, hinn, noFiveOver_of_powOver hU (by rw [hk]; norm_num) (powOver_projectiveSL hK4)⟩

theorem fiveRigid_quot_of_isPSL3 {X : Type} [Group X] (hX : CFSG.Quasithin.IsPSL 3 2 2 X) :
    FiveRigid (X ⧸ Subgroup.center X) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hk : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  have hP := fiveRigid_projectiveSL hk
  obtain ⟨-, ⟨e'⟩⟩ := nonempty_quotCenter_equiv (e.trans (Setup.X7a.statedSLEquivProjectiveSL 3 K))
    hP.1
  exact fiveRigid_of_mulEquiv e'.symm hP

theorem fiveRigid_quot_of_isSL3 {X : Type} [Group X] (hX : CFSG.Quasithin.IsSL3 4 X) :
    FiveRigid (X ⧸ Subgroup.center X) := by
  obtain ⟨K, _, _, hk, ⟨e⟩⟩ := hX
  have : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (k := 2) (by norm_num)
      (by rw [hk]; norm_num)
  have hP := fiveRigid_projectiveSL hk
  let φ : X ≃* SpecialLinearGroup (Fin 3) K := e.trans (specialLinearGroupEquivStatedSL 3 K).symm
  let ψ : X ⧸ Subgroup.center X ≃* projectiveSL 3 K :=
    (QuotientGroup.congr (Subgroup.center X) (Subgroup.center _) φ
      (Subgroup.map_center_eq φ)).trans
      (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 K).symm)
  exact fiveRigid_of_mulEquiv ψ.symm hP

end CFSG.Quasithin.H13.FiveNorm.LieL3
