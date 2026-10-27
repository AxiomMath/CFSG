module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeIsComp
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeCQ
import CFSG.GroupTheory.ConjQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GUniMat
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

section UniCubeQS

open CFSG.GroupTheory

private theorem mem_LargeEvenGUSet_of_isHermIsometry {K : Type} [Field K] {q n : ℕ}
    (hq0 : q ≠ 0) {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) :
    d ∈ LargeEvenGUSet (Fin n) K q := by
  refine ⟨1, one_ne_zero, by simp, ?_⟩
  simp only [one_smul]
  ext i j
  have h := hd (Pi.single i (1 : K)) (Pi.single j (1 : K))
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.mulVec_single_one, Matrix.col_apply] at h ⊢
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.one_apply, Pi.single_apply, hij, Ne.symm hij, hq0]

private theorem not_isQuasisimple_of_isSolvable_centerQuot {Q P : Type} [Group Q] [Group P]
    (e : Q ⧸ Subgroup.center Q ≃* P) (hsolv : Group.IsSolvable P)
    (hqs : CFSG.Assembly.IsQuasisimple Q) : False := by
  haveI : Group.IsSolvable P := hsolv
  haveI hQ : Group.IsSolvable (Q ⧸ Subgroup.center Q) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hqs.2
  have hcomm : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
    ⟨⟨(IsSimpleGroup.comm_iff_isSolvable (G := Q ⧸ Subgroup.center Q)).mpr hQ⟩⟩
  have hle : commutator Q ≤ Subgroup.center Q :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (G := Q)
      (N := Subgroup.center Q)).mp hcomm
  rw [hqs.1] at hle
  have hcenter : Subgroup.center Q = ⊤ := top_le_iff.mp hle
  have hsub : Subsingleton (Q ⧸ Subgroup.center Q) := by
    rw [QuotientGroup.subsingleton_iff]
    exact hcenter
  exact not_subsingleton _ hsub

private theorem subsingleton_largeEvenSU_of_le_one {K : Type} [Field K] {f k : ℕ}
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) (hk : k ≤ 1) :
    Subsingleton ↥(LargeEvenSUGroup (Fin k) K (2 ^ f)) := by
  rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
  refine ⟨fun a b => ?_⟩
  rw [CFSG.AGLEmbedding.ToralCensus.eq_one_of_le_one hU hk a,
    CFSG.AGLEmbedding.ToralCensus.eq_one_of_le_one hU hk b]

private theorem isSolvable_largeEvenProj_su_two_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin 2) K 2)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(LargeEvenSUGroup (Fin 2) K 2) = 6 := by
    rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
    have h := CFSG.RankThree.SubgroupLists.card_statedSU_two (K := K) (r := 2) (f := 1)
      (by rw [hK]; norm_num)
    simpa using h
  haveI : Group.IsSolvable ↥(LargeEvenSUGroup (Fin 2) K 2) :=
    CFSG.Quasithin.isSolvable_of_card_six hcard
  exact Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

private theorem isSolvable_largeEvenProj_su_three_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) :
    Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup (Fin 3) K 2)) := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq (by rw [hK]; norm_num)
      (by norm_num)
  have h := CFSG.HardMathSupport.Solomon.Coordinator.isSolvable_statedProj_of_pow_eq_two hU
    (by norm_num : (2 : ℕ) ^ 1 = 2)
  rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU]
  simpa using h

end UniCubeQS

theorem uni_cube_eigBlock_quasisimple_iff {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {μ : K} (hμ : μ ^ 3 = 1) :
    CFSG.Assembly.IsQuasisimple ↥(eigBlock q d μ) ↔ CubeBlockQS q d μ := by
  obtain ⟨f, hf1, hq⟩ := ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have hq0 : q ≠ 0 := by
    rw [hq]
    exact pow_ne_zero _ (by norm_num)
  have hdGU : d ∈ LargeEvenGUSet (Fin n) K (2 ^ f) := by
    rw [← hq]
    exact mem_LargeEvenGUSet_of_isHermIsometry hq0 hd
  have hnormSU : d ∈ Subgroup.normalizer (LargeEvenSUGroup (Fin n) K q : Set (GL (Fin n) K)) := by
    rw [hq]
    exact Subgroup.mem_normalizer_fintype fun x hx =>
      CFSG.LocalAnalysis.GLTheoremA.T156.Uni.conj_mem_su (j := f) hdGU hx
  have hnormS : d ∈ Subgroup.normalizer (LargeEvenScalars (Fin n) K : Set (GL (Fin n) K)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top d
  let δ' : MulAut (PSUg n K q) := CFSG.GroupTheory.conjQuotAut hnormSU hnormS
  have hδ : IsConjBy d δ' := by
    unfold IsConjBy LargeEvenGraphAut
    intro a b hab
    change (CFSG.GroupTheory.conjQuotAut hnormSU hnormS) (a : PSUg n K q) =
      (b : PSUg n K q)
    rw [CFSG.GroupTheory.conjQuotAut_mk]
    congr 1
    exact Subtype.ext hab.symm
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq (by rw [hK, hq]) hf1
  constructor
  · intro hqs
    by_contra hnot
    have hnot' : ¬ ((2 ≤ Module.finrank K (cubeEigen d μ) ∧ 4 ≤ q) ∨
        4 ≤ Module.finrank K (cubeEigen d μ)) := by
      simpa only [CubeBlockQS] using hnot
    obtain ⟨e⟩ := uni_cube_eigBlock_centerQuot hK hq3 hn hd hd3 hμ
    by_cases hk1 : Module.finrank K (cubeEigen d μ) ≤ 1
    · haveI : Subsingleton ↥(LargeEvenSUGroup
          (Fin (Module.finrank K (cubeEigen d μ))) K q) := by
        rw [hq]
        exact subsingleton_largeEvenSU_of_le_one hU hk1
      haveI : Group.IsSolvable ↥(LargeEvenSUGroup
          (Fin (Module.finrank K (cubeEigen d μ))) K q) := inferInstance
      have hsolv : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup
          (Fin (Module.finrank K (cubeEigen d μ))) K q)) :=
        Group.isSolvable_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      exact not_isQuasisimple_of_isSolvable_centerQuot e hsolv hqs
    · have hk2' : 2 ≤ Module.finrank K (cubeEigen d μ) := by omega
      have hqle : ¬ 4 ≤ q := fun h => hnot' (Or.inl ⟨hk2', h⟩)
      have hk4 : ¬ 4 ≤ Module.finrank K (cubeEigen d μ) := fun h => hnot' (Or.inr h)
      have hk3 : Module.finrank K (cubeEigen d μ) ≤ 3 := by omega
      have h4f : ¬ 4 ≤ 2 ^ f := by rw [← hq]; exact hqle
      have hf_le1 : f ≤ 1 := by
        by_contra h
        have h2f : 2 ≤ f := by omega
        exact h4f (by
          calc (4 : ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2f)
      have hf_eq1 : f = 1 := by omega
      have hq2 : q = 2 := by rw [hq, hf_eq1]; norm_num
      have hK4 : Nat.card K = 4 := by rw [hK, hq2]; norm_num
      have hk23 : Module.finrank K (cubeEigen d μ) = 2 ∨
          Module.finrank K (cubeEigen d μ) = 3 := by omega
      have hsolv : Group.IsSolvable (LargeEvenProj (LargeEvenSUGroup
          (Fin (Module.finrank K (cubeEigen d μ))) K q)) := by
        rcases hk23 with hk | hk
        · rw [hk, hq2]; exact isSolvable_largeEvenProj_su_two_two hK4
        · rw [hk, hq2]; exact isSolvable_largeEvenProj_su_three_two hK4
      exact not_isQuasisimple_of_isSolvable_centerQuot e hsolv hqs
  · intro hcb
    exact (uni_cube_eigBlock_isComponent hK hq3 hn hd hd3 hδ hμ hcb).2.2

end CFSG.StandardType.TablePThreeKG

end
