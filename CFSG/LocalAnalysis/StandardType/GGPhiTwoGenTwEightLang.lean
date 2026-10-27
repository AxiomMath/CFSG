module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenTwEightDefs

import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame
import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionLang

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups
open CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.RankThree.Chevalley CFSG.StandardType.TableBExcTwoFusion

private lemma frameLangAux_permLattice_frameRoot : ∀ i : Fin 4,
    permLattice TwistTag.E6.perm (frameRoot i) = frameRoot i := by
  decide +kernel

private lemma frameLangAux_map_frameLangSL2 {K : Type} [Field K] [CharP K 2] {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (frameLangSL2 ζ hζ) =
      frameLangSL2 ζ hζ * nSL 1 := by
  have h3 : ζ ^ 3 = 1 := pow_three_of_sq_add hζ
  have h8 : ζ ^ 8 = ζ ^ 2 := by
    rw [show ζ ^ 8 = ζ ^ 2 * (ζ ^ 3) ^ 2 by ring, h3]
    ring
  have hσζ : σ ζ = ζ ^ 2 := by rw [hσ, h8]
  have hA : frameLangSL2 ζ hζ = nSL 1 * langP hζ := by
    ext i j
    change (!![ζ, ζ ^ 2; 1, 1] : Matrix (Fin 2) (Fin 2) K) i j =
      ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) *
        (!![1, 1; ζ, ζ ^ 2] : Matrix (Fin 2) (Fin 2) K)) i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  rw [hA, map_mul, map_nSL_one, map_langP hζ σ.toRingHom hσζ]
  group


section frameLangAux

private lemma frameLangAux_rootSL2_nSL_one {K : Type} [Field K] [CharP K 2]
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β) :
    rootSL2 TwistTag.E6.tag K β (nSL 1) =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection β) := by
  simpa [rootWeylSL2] using
    (CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := K) (τ := TwistTag.E6.tag) hβ)

theorem rootSL2_frameRoot_commute {K : Type} [Field K] {i j : Fin 4} (hij : i ≠ j)
    (A B : SL2 K) :
    rootSL2 TwistTag.E6.tag K (frameRoot i) A *
        rootSL2 TwistTag.E6.tag K (frameRoot j) B =
      rootSL2 TwistTag.E6.tag K (frameRoot j) B *
        rootSL2 TwistTag.E6.tag K (frameRoot i) A := by
  obtain ⟨hroot, hcheck⟩ := e6_four_roots_check
  obtain ⟨h0, hp, hm⟩ := hcheck i j hij
  refine commute_of_mem_rootPair_of_check (hroot i) (hroot j) h0 hp hm ?_ ?_
  · change (rootSL2 TwistTag.E6.tag K (frameRoot i)) A ∈
      rootSubgroup TwistTag.E6.tag K (frameRoot i) ⊔
        rootSubgroup TwistTag.E6.tag K (-(frameRoot i))
    rw [← range_rootSL2_of_isRoot (isRoot_frameRoot i)]
    exact ⟨A, rfl⟩
  · change (rootSL2 TwistTag.E6.tag K (frameRoot j)) B ∈
      rootSubgroup TwistTag.E6.tag K (frameRoot j) ⊔
        rootSubgroup TwistTag.E6.tag K (-(frameRoot j))
    rw [← range_rootSL2_of_isRoot (isRoot_frameRoot j)]
    exact ⟨B, rfl⟩

private lemma frameLangAux_rootReflection_prod {v : WeylGroup TwistTag.E6.tag}
    (hv : ExcIsLongest TwistTag.E6.tag v) :
    rootReflection (frameRoot 0) * rootReflection (frameRoot 1) *
      rootReflection (frameRoot 2) * rootReflection (frameRoot 3) = v := by
  refine ReversesSigns.eq ?_ ?_
  · apply height_smul_neg_of_forall_single
    intro i
    fin_cases i <;>
      simp only [mul_smul, rootReflection_smul (isRoot_frameRoot _)] <;>
      decide +kernel
  · intro α hα hpos
    exact (IsRoot.height_neg_iff (IsRoot.smul hα v)).2
      (hv α hα ((IsRoot.height_pos_iff hα).1 hpos))

end frameLangAux

theorem twistHom_frameLang {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 8) {ζ : K} (hζ : ζ ^ 2 + ζ + 1 = 0) {v : WeylGroup TwistTag.E6.tag}
    (hv : ExcIsLongest TwistTag.E6.tag v) :
    twistHom TwistTag.E6 K σ.toRingHom (frameLang ζ hζ) =
      frameLang ζ hζ * canonicalRep (coxeterSystem TwistTag.E6.tag) K v := by
  let M : SL2 K := frameLangSL2 ζ hζ
  let f : Fin 4 → ModGL TwistTag.E6.tag K :=
    fun i => rootSL2 TwistTag.E6.tag K (frameRoot i) M
  let g : Fin 4 → ModGL TwistTag.E6.tag K := fun i =>
    canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection (frameRoot i))
  have hmap : Matrix.SpecialLinearGroup.map σ.toRingHom M = M * nSL 1 :=
    frameLangAux_map_frameLangSL2 hσ hζ
  have hstep : ∀ i : Fin 4, twistHom TwistTag.E6 K σ.toRingHom (f i) = f i * g i := by
    intro i
    rw [show f i = rootSL2 TwistTag.E6.tag K (frameRoot i) M from rfl,
      CFSG.StandardType.TwE6CorootCore.twistHom_rootSL2_of_perm σ.toRingHom
        (isRoot_frameRoot i) (frameLangAux_permLattice_frameRoot i) M, hmap, map_mul,
      frameLangAux_rootSL2_nSL_one (isRoot_frameRoot i)]
  have hfg : ∀ i j : Fin 4, i ≠ j → Commute (f i) (g j) := by
    intro i j hij
    rw [show g j = rootSL2 TwistTag.E6.tag K (frameRoot j) (nSL 1) from
      (frameLangAux_rootSL2_nSL_one (isRoot_frameRoot j)).symm]
    exact rootSL2_frameRoot_commute hij M (nSL 1)
  have hprod := CFSG.StandardType.TableBExcTwoFusion.list_prod_ofFn_mul_of_ne f g hfg
  have hL : twistHom TwistTag.E6 K σ.toRingHom (frameLang ζ hζ) =
      (List.ofFn fun i => f i * g i).prod := by
    simp only [frameLang, map_mul]
    rw [hstep 0, hstep 1, hstep 2, hstep 3]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp [mul_assoc]
  have hfl : (List.ofFn f).prod = frameLang ζ hζ := by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
    simp [f, frameLang, mul_assoc]
    rfl
  have hgl : (List.ofFn g).prod =
      canonicalRep (coxeterSystem TwistTag.E6.tag) K v := by
    have h4 : (List.ofFn g).prod =
        canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection (frameRoot 0)) *
          canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection (frameRoot 1)) *
            canonicalRep (coxeterSystem TwistTag.E6.tag) K (rootReflection (frameRoot 2)) *
              canonicalRep (coxeterSystem TwistTag.E6.tag) K
                (rootReflection (frameRoot 3)) := by
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
      simp [g, mul_assoc]
    rw [h4,
      ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
      ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
      ← CFSG.RankThree.PartOne.Q1327T.canonicalRep_mul_charTwo,
      frameLangAux_rootReflection_prod hv]
  rw [hL, hprod, hfl, hgl]

end CFSG.StandardType.PhiTwoRootGen

end
