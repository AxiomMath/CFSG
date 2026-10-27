module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamNoFive
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroup
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.RankThree.SteinbergR3EHigherLinearOuterOrder
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.E9

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique CFSG.Quasithin.H23P4

variable {K : Type} [Field K] [CharP K 2]

theorem one_add_one_eq_zero_of_charTwo : (1 : K) + 1 = 0 := by
  have : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [← this]
  norm_num

theorem transvection_pair_cube (a b : Fin 3) (hab : a ≠ b) :
    (SpecialLinearGroup.transvection hab (1 : K) *
      SpecialLinearGroup.transvection hab.symm (1 : K)) ^ 3 = 1 := by
  have h1 : (1 : K) + 1 = 0 := one_add_one_eq_zero_of_charTwo
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.coe_one]
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | skip
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply, Matrix.one_apply,
        h1]

omit [CharP K 2] in
theorem transvection_pair_not_scalar (a b : Fin 3) (hab : a ≠ b) :
    SpecialLinearGroup.transvection hab (1 : K) *
      SpecialLinearGroup.transvection hab.symm (1 : K) ∉ scalars 3 K := by
  rintro ⟨c, -, hc⟩
  have h := congrFun (congrFun hc a) b
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.SpecialLinearGroup.transvection_coe] at h
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply, hab, Matrix.scalar_apply] at h

theorem exists_order_three_of_reflection_mem (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hU : unitriangular 3 K ≤ M) {i : ℕ} (hi : 1 ≤ i) (hin : i < 3)
    (hr : reflection 3 K i hi hin ∈ M) : ∃ g ∈ M, g ^ 3 = 1 ∧ g ∉ scalars 3 K := by
  set a : Fin 3 := ⟨i - 1, by omega⟩ with ha
  set b : Fin 3 := ⟨i, hin⟩ with hb
  have hab : a < b := by
    rw [Fin.lt_def]
    simp only [ha, hb]
    omega
  have hform := (monomial_root_transport (K := K) (n := 3)).2.2 i hi hin
  have hform' : reflection 3 K i hi hin =
      Matrix.SpecialLinearGroup.transvection hab.ne (1 : K) *
        Matrix.SpecialLinearGroup.transvection hab.ne' (1 : K) *
        Matrix.SpecialLinearGroup.transvection hab.ne (1 : K) := by
    rw [hform]
    simp only [CharTwo.neg_eq]
  have hx : Matrix.SpecialLinearGroup.transvection hab.ne (1 : K) ∈ M :=
    hU (transvection_mem_unitriangular hab 1)
  have hy : Matrix.SpecialLinearGroup.transvection hab.ne' (1 : K) ∈ M := by
    have : Matrix.SpecialLinearGroup.transvection hab.ne' (1 : K) =
        (Matrix.SpecialLinearGroup.transvection hab.ne (1 : K))⁻¹ * reflection 3 K i hi hin *
          (Matrix.SpecialLinearGroup.transvection hab.ne (1 : K))⁻¹ := by
      rw [hform']
      group
    rw [this]
    exact mul_mem (mul_mem (inv_mem hx) hr) (inv_mem hx)
  exact ⟨_, mul_mem hx hy, transvection_pair_cube a b hab.ne, transvection_pair_not_scalar a b
    hab.ne⟩

theorem borel_or_order_three (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hU : unitriangular 3 K ≤ M) :
    M ≤ upperTriangular 3 K ∨ ∃ g ∈ M, g ^ 3 = 1 ∧ g ∉ scalars 3 K := by
  by_cases h : ∃ (i : ℕ) (hi : 1 ≤ i) (hin : i < 3), reflection 3 K i hi hin ∈ M
  · obtain ⟨i, hi, hin, hr⟩ := h
    exact Or.inr (exists_order_three_of_reflection_mem M hU hi hin hr)
  · push Not at h
    refine Or.inl ((le_flagStabilizer_borelOvergroupCuts M hU).trans ?_)
    rw [(subflag_stabilizer_generation (K := K) (n := 3) (borelOvergroupCuts M)).1,
      Subgroup.closure_le]
    rintro g (hg | ⟨j, hj, hjn, hjI, rfl⟩)
    · exact hg
    · exact absurd ⟨hj, hjn, h j hj hjn⟩ hjI

omit [CharP K 2] in
theorem diag_ne_zero_of_mem_upperTriangular {n : ℕ}
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ upperTriangular n K) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) i i ≠ 0 := by
  intro h0
  have hdet : (g : Matrix (Fin n) (Fin n) K).det = 1 := g.2
  rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hg),
    Finset.prod_eq_zero (f := fun k => (g : Matrix (Fin n) (Fin n) K) k k) (Finset.mem_univ i)
      h0] at hdet
  exact zero_ne_one hdet

omit [CharP K 2] in
theorem pow_three_mem_unitriangular (hK3 : ∀ x : K, x ≠ 0 → x ^ 3 = 1) {n : ℕ}
    {g : Matrix.SpecialLinearGroup (Fin n) K} (hg : g ∈ upperTriangular n K) :
    g ^ 3 ∈ unitriangular n K := by
  refine ⟨(upperTriangular n K).pow_mem hg 3 , fun i => ?_⟩
  have hg' : (g : Matrix (Fin n) (Fin n) K).IsUpperTriangular := fun _ _ h => hg _ _ h
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    mul_apply_self_of_isUpperTriangular hg' (hg'.mul hg'),
    mul_apply_self_of_isUpperTriangular hg' hg', ← pow_three]
  exact hK3 _ (diag_ne_zero_of_mem_upperTriangular hg i)

variable [Finite K]

theorem noFiveIndex_projectiveSL_three (hK3 : ∀ x : K, x ≠ 0 → x ^ 3 = 1) :
    NoFiveIndex (projectiveSL 3 K) := by
  obtain ⟨P, hP⟩ := exists_sylow_projUnitriangular (K := K) 2 (by norm_num : 1 ≤ 3)
  have hS : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
    rw [isSylowTwoOf_top_iff, ← hP]
    exact ⟨P.isPGroup', P.not_dvd_index⟩
  refine noFiveIndex_of_dichotomy (B := projUpperTriangular 3 K) hS ?_ ?_ ?_
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨s, hs, rfl⟩
    exact ⟨b * s * b⁻¹, conj_mem_unitriangular hb hs, by simp⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨g ^ 3, pow_three_mem_unitriangular hK3 hg, by simp⟩
  · intro A hA
    have hUM : unitriangular 3 K ≤ A.comap (proj 3 K) := fun u hu =>
      hA (Subgroup.mem_map_of_mem _ hu)
    rcases borel_or_order_three (A.comap (proj 3 K)) hUM with hle | ⟨g, hgM, hg3, hgs⟩
    · left
      intro a ha
      obtain ⟨g, rfl⟩ := proj_surjective 3 K a
      exact ⟨g, hle ha, rfl⟩
    · right
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact ⟨proj 3 K g, hgM, orderOf_eq_prime (by rw [← map_pow, hg3, map_one])
        fun h => hgs (proj_eq_one_iff.mp h)⟩

end CFSG.Quasithin.E9

namespace CFSG.Quasithin.E9

open CFSG.QuasithinUnique CFSG.Quasithin.H23P4 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.Quasithin

theorem exists_equiv_projectiveSL_of_isPSL_three_two_two {X : Type} [Group X]
    (h : IsPSL 3 2 2 X) : ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 4 ∧ Nonempty (X ≃* projectiveSL 3 K) := by
  obtain ⟨-, K, hF, hfin, hK, ⟨e⟩⟩ := h
  have hK4 : Nat.card K = 4 := by simpa using hK
  have hchar : CharP K 2 :=
    finite_field_prime_power_characteristic Nat.prime_two (by norm_num : 1 ≤ 2) hK
  exact ⟨K, hF, hfin, hchar, hK4, ⟨e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))⟩⟩

theorem rowOK_of_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) : RowOK X := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL_of_isPSL_three_two_two h
  have hfin : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hsimple : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 2 h).2
  have hout : CFSG.Quasithin.H23Out.NoFiveOut (projectiveSL 3 K) := by
    intro h5
    have h12 := CFSG.RankThree.Automorphisms.higher_linear_outer_order_divides_field_scalar_bound
      (K := K) (ℓ := 2) (f := 2) (n := 3) Nat.prime_two (by norm_num) le_rfl (by simpa using hK)
    have := h5.trans h12
    norm_num at this
  refine ⟨?_, CFSG.Quasithin.H23Out.Out5Pow.of_noFiveOut
    (CFSG.Quasithin.H23Out.NoFiveOut.of_mulEquiv e hout),
    NoFiveIndex.of_mulEquiv e (noFiveIndex_projectiveSL_three (pow_three_eq_one_of_card_four hK))⟩
  have hcard : Nat.card ((projUnitriangular 3 K).map (e.symm : projectiveSL 3 K →* X)) = 64 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, card_projUnitriangular, hK]
    norm_num
  exact center_eq_bot_of_simple_of_card hcard (by norm_num) (by norm_num)

end CFSG.Quasithin.E9
