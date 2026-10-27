module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs
public import CFSG.LieType.SeitzGeneration.OuterLinearField
public import CFSG.LieType.SeitzGeneration.OuterLinearLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.RankThree.PartOne (linearSubfieldInclusion)
open CFSG.RankThree.PartOne.CTP (slSub range_linearSubfieldInclusion_eq_map
  map_conjAut_range_linearSubfieldInclusion)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

private lemma ksl3f_mem_fixedBy_zpowers_iff {J : Type*} [Group J] (f : MulAut J) (x : J) :
    x ∈ fixedBy (Subgroup.zpowers f) ↔ f x = x := by
  rw [mem_fixedBy]
  refine ⟨fun h => h f (Subgroup.mem_zpowers f), fun h w hw => ?_⟩
  have h1 : w • x = x :=
    smul_eq_self_of_mem_zpowers hw (by simpa [MulAut.smul_def] using h)
  simpa [MulAut.smul_def] using h1

theorem fixedBy_zpowers_fieldAut_eq_range {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : orderOf σ = 7) (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K)) :
    fixedBy (Subgroup.zpowers (fieldAut 3 K σ)) =
      (linearSubfieldInclusion 3 (semilinearFixedSubfield σ)).range := by
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hσp : σ ^ 7 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hset : {x : projectiveSL 3 K | fieldAut 3 K σ x = x} =
      ((linearSubfieldInclusion 3 (semilinearFixedSubfield σ)).range :
        Set (projectiveSL 3 K)) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.fixed_points_eq_range (n := 3) hk (by norm_num)
      (CFSG.RankThree.PartOne.KCLinearSubfield.root_descent_of_coprime (n := 3) hk hσp
        (by norm_num))
  ext x
  rw [ksl3f_mem_fixedBy_zpowers_iff]
  exact Set.ext_iff.mp hset x

theorem mem_zpowers_fieldAut_of_fixes {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : orderOf σ = 7) (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K))
    (α : MulAut (projectiveSL 3 K))
    (hα : ∀ x ∈ fixedBy (Subgroup.zpowers (fieldAut 3 K σ)), α x = x) :
    α ∈ Subgroup.zpowers (fieldAut 3 K σ) := by
  have hk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  rw [← CFSG.RankThree.PartOne.fixingSubgroup_range_linearSubfieldInclusion (n := 3) hk
      (by norm_num),
    mem_fixingSubgroup_iff]
  intro y hy
  have hy' : y ∈ fixedBy (Subgroup.zpowers (fieldAut 3 K σ)) := by
    rw [fixedBy_zpowers_fieldAut_eq_range σ hσ h7]
    exact hy
  simpa [MulAut.smul_def] using hα y hy'

theorem fixedBy_sup_conj_eq_top {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (hσ : orderOf σ = 7) (hK : Nat.card K = Nat.card (semilinearFixedSubfield σ) ^ 7)
    (h7 : ¬ 7 ∣ Nat.card (projectiveSL 3 K)) (x : projectiveSL 3 K)
    (hne : (fixedBy (Subgroup.zpowers (fieldAut 3 K σ))).map (MulAut.conj x).toMonoidHom ≠
      fixedBy (Subgroup.zpowers (fieldAut 3 K σ))) :
    fixedBy (Subgroup.zpowers (fieldAut 3 K σ)) ⊔
      (fixedBy (Subgroup.zpowers (fieldAut 3 K σ))).map (MulAut.conj x).toMonoidHom = ⊤ := by
  obtain ⟨g, hg⟩ := proj_surjective 3 K x
  set M : GL (Fin 3) K := Matrix.SpecialLinearGroup.toGL g with hM
  have hconj : MulAut.conj x = conjAut 3 K M := by
    rw [hM, ← hg]
    exact (CFSG.LieType.SeitzGeneration.conjAut_toGL g).symm
  set k : Subfield K := semilinearFixedSubfield σ with hkdef
  have hF : fixedBy (Subgroup.zpowers (fieldAut 3 K σ)) =
      (linearSubfieldInclusion 3 k).range := by
    rw [hkdef]
    exact fixedBy_zpowers_fieldAut_eq_range σ hσ h7
  have hmap : (fixedBy (Subgroup.zpowers (fieldAut 3 K σ))).map
        (MulAut.conj x).toMonoidHom =
      ((slSub 3 k).map (slConjugation 3 K M).toMonoidHom).map (proj 3 K) := by
    rw [hF, hconj]
    exact map_conjAut_range_linearSubfieldInclusion k M
  have hne' : (slSub 3 k).map (slConjugation 3 K M).toMonoidHom ≠ slSub 3 k := by
    intro h
    apply hne
    rw [hmap, h, ← range_linearSubfieldInclusion_eq_map, ← hF]
  have hgen := CFSG.LieType.SeitzGeneration.pairSL_closure Nat.prime_seven (by norm_num)
      (by rw [hkdef]; exact hK) (by norm_num) M hne'
  have h4 := congrArg (Subgroup.map (proj 3 K)) hgen
  rw [CFSG.RankThree.PartOne.CTP.map_closure_union,
    Subgroup.map_top_of_surjective _ (proj_surjective 3 K)] at h4
  rw [hmap, hF, range_linearSubfieldInclusion_eq_map]
  rw [← Subgroup.sup_eq_closure] at h4
  exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
