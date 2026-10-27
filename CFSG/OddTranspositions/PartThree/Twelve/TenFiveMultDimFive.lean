module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveMultModels
public import CFSG.ClassicalGroups.Symplectic.OrthogonalFiveModel
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSimilarity
public import CFSG.RankThree.CentralLift.ClassicalCenterTrivial
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU2
public import CFSG.ClassicalInvolution.Asc77.Lemma310
public import CFSG.ClassicalInvolution.Asc77.ThmEStatement
public import CFSG.ClassicalInvolution.Asc77.WP1Section18
public import CFSG.ClassicalInvolution.Asc77.WP1Section6
public import CFSG.ClassicalInvolution.Balance.QNineFuzzyFree
public import CFSG.ClassicalInvolution.Balance.Theorem5Models
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Conj
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Roots
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Ord
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Std
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltSmall
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36AltPerm
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix CFSG.Open CFSG.LieType.Universal.Spin

noncomputable def commutatorOrthogonalEquivOrthDerived {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (Q : QuadraticForm K V) :
    ↥(commutator (TauCeti.QuadraticMap.orthogonalGroup Q)) ≃*
      ↥(CFSG.RankThree.Classical2.orthDerived Q) :=
  (Subgroup.equivMapOfInjective (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))

noncomputable def statedProjQuadOddTwoEquiv :
    StatedProj (StatedOmega (StatedQuadOdd 2 (ZMod 5))) ≃*
      StatedProj (StatedSp 2 (ZMod 5)) := by
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have hodd : Odd (Nat.card (ZMod 5)) := by rw [Nat.card_zmod]; norm_num
  have hdim : Module.finrank (ZMod 5) (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5) = 5 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp [Fintype.card_sum]
  have hnd : (quadOdd 2 (ZMod 5)).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd 2 (ZMod 5) h2
  let e1 := (CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (K := ZMod 5) (Q := quadOdd 2 (ZMod 5)) (Q₀ := StatedQuadOdd 2 (ZMod 5))
    (CFSG.LieType.Universal.Spin.coe_quadOdd (n := 2) (K := ZMod 5))).some
  have hbot : (CFSG.ClassicalGroups.Orthogonal.scalars (ZMod 5)
        (Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5)).subgroupOf
      (CFSG.RankThree.Classical2.orthDerived (quadOdd 2 (ZMod 5))) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    exact CFSG.ComponentClassification.HarrisLit.T1.eq_one_of_mem_scalars_quadOdd
      x.2 (Subgroup.mem_subgroupOf.mp hx)
  let e2 : CFSG.RankThree.Classical2.ProjOrthDerived (quadOdd 2 (ZMod 5)) ≃*
      CFSG.RankThree.Classical2.orthDerived (quadOdd 2 (ZMod 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let eO := (CFSG.ClassicalGroups.Orthogonal.exists_five_dimensional_orthogonal_similarity
    (K := ZMod 5) (V := Fin 2 ⊕ Fin 2 ⊕ Unit → ZMod 5) hodd
      (quadOdd 2 (ZMod 5)) hnd hdim).choose_spec.choose_spec.choose
  let e3 : CFSG.RankThree.Classical2.orthDerived (quadOdd 2 (ZMod 5)) ≃*
      CFSG.RankThree.Classical2.orthDerived
        (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm (ZMod 5)) :=
    (commutatorOrthogonalEquivOrthDerived (quadOdd 2 (ZMod 5))).symm.trans
      ((MulEquiv.commutatorCongr eO).trans
        (commutatorOrthogonalEquivOrthDerived
          (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm (ZMod 5))))
  let e4 : CFSG.RankThree.Classical2.orthDerived
        (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm (ZMod 5)) ≃*
      StatedProj (StatedSp 2 (ZMod 5)) :=
    (commutatorOrthogonalEquivOrthDerived
        (CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm (ZMod 5))).symm.trans
      (CFSG.ClassicalGroups.Symplectic.pspFourEquivDerivedOrthogonal (K := ZMod 5) hodd).symm
  exact e1.trans (e2.trans (e3.trans e4))

theorem centralKernelTwoGroup_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (hY : CentralKernelTwoGroup Y) : CentralKernelTwoGroup X := by
  intro Γ _ _ φ hφ hcen hcomm
  have hφ' : Function.Surjective (e.toMonoidHom.comp φ) := e.surjective.comp hφ
  have hker : (e.toMonoidHom.comp φ).ker = φ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e e.injective
  have hcen' : (e.toMonoidHom.comp φ).ker ≤ Subgroup.center Γ := by rw [hker]; exact hcen
  have hcomm' : (e.toMonoidHom.comp φ).ker ≤ commutator Γ := by rw [hker]; exact hcomm
  have h := hY Γ (e.toMonoidHom.comp φ) hφ' hcen' hcomm'
  rwa [hker] at h

end CFSG.OddTranspositions.PartThree
