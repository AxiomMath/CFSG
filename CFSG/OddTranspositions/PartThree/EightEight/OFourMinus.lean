module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.HalphaNonsolvable
public import Mathlib.GroupTheory.Solvable
import CFSG.OddTranspositions.PartThree.EightNine.O4
import CFSG.OddTranspositions.TheoremTwo.WCover
public import CFSG.OddTranspositions.O4PairTenThreeTranspositions
import CFSG.CGT.T75E.Lemma26
import CFSG.CGT.Timmesfeld75.Sec3TenCaseA
import CFSG.CGT.Timmesfeld75.Sec4CaseIBasic
import CFSG.CGT.Timmesfeld75.Sec4CaseIIIFour
import CFSG.CGT.Timmesfeld75.Sec4CaseIJFamily
import CFSG.CGT.Timmesfeld75.Sec4CaseIJIdent
import CFSG.CGT.Timmesfeld75.Sec4CaseIPGroup
import CFSG.CGT.Timmesfeld75.Sec4CaseIPartition4
import CFSG.CGT.Timmesfeld75.Sec4Three
import CFSG.CGT.Timmesfeld75.Sec5FiveEng
import CFSG.CGT.Timmesfeld75.Step511Card
import CFSG.CGT.Timmesfeld75.Step57Reduction
import CFSG.Combinatorics.AperiodicCentralInvolution
import CFSG.Combinatorics.AperiodicFiveOfSix
import CFSG.Combinatorics.AperiodicOppositeComponents
import CFSG.Combinatorics.AperiodicSixteenGraphDistances
import CFSG.Combinatorics.OuterLayerPredecessors
import CFSG.GH74.Uniqueness.Bender.OddCentralizer
import CFSG.GH74.Uniqueness.Bender.Unitary
import CFSG.GroupTheory.PerfectLeOfPGroupQuotient
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.AlmostSimple
import CFSG.OddTranspositions.Disconnected
import CFSG.OddTranspositions.Reduction
import CFSG.OddTranspositions.WidthTwoNoProduct
import CFSG.OddTranspositions.WreathQuotient
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.OddTranspositions.QZ

theorem eq_one_or_eq_inr_frob25_of_leftHomYten_eq_one {w : Yten}
    (hw : leftHomYten w = 1) :
    (w : PSigmaL225) = 1 ∨ (w : PSigmaL225) = SemidirectProduct.inr frob25 := by
  have hleft : (w : PSigmaL225).left = 1 := congrArg Subtype.val hw
  rcases right_mem_of_mem w.2 with hr | hr
  · exact Or.inl (SemidirectProduct.ext hleft hr)
  · exact Or.inr (SemidirectProduct.ext hleft hr)

theorem isSolvable_ker_leftHomYten : Group.IsSolvable leftHomYten.ker := by
  have hmem : ∀ x : leftHomYten.ker,
      ((x : Yten) : PSigmaL225) = 1 ∨
        ((x : Yten) : PSigmaL225) = SemidirectProduct.inr frob25 :=
    fun x => eq_one_or_eq_inr_frob25_of_leftHomYten_eq_one x.2
  refine Group.isSolvable_of_comm fun x y => ?_
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rcases hmem x with hx | hx <;> rcases hmem y with hy | hy <;> rw [hx, hy] <;> simp

theorem isSolvable_ker_comp_leftHomYten_comp {H : Type} [Group H] (ψ : H ≃* Yten)
    (e : FixK ≃* Equiv.Perm (Fin 5)) :
    Group.IsSolvable ((e : FixK →* Equiv.Perm (Fin 5)).comp
      (leftHomYten.comp (ψ : H →* Yten))).ker := by
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, MonoidHom.ker_comp_mulEquiv]
  have hK : Group.IsSolvable leftHomYten.ker := isSolvable_ker_leftHomYten
  exact Group.isSolvable_of_surjective
    (MonoidHom.subgroupMap_surjective (ψ.symm : Yten →* H) leftHomYten.ker)

theorem solvableRadical_le_ker_comp_leftHomYten_comp {H : Type} [Group H] [Finite H]
    (ψ : H ≃* Yten) (e : FixK ≃* Equiv.Perm (Fin 5)) :
    CFSG.solvableRadical H ≤ ((e : FixK →* Equiv.Perm (Fin 5)).comp
      (leftHomYten.comp (ψ : H →* Yten))).ker := by
  let φ : H →* Equiv.Perm (Fin 5) :=
    (e : FixK →* Equiv.Perm (Fin 5)).comp (leftHomYten.comp (ψ : H →* Yten))
  change CFSG.solvableRadical H ≤ φ.ker
  have hφ : Function.Surjective φ :=
    e.surjective.comp (leftHomYten_surjective.comp ψ.surjective)
  have hRsolv : Group.IsSolvable (CFSG.solvableRadical H) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have hmap_solv : Group.IsSolvable ((CFSG.solvableRadical H).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (CFSG.solvableRadical H))
  have hmap_norm : ((CFSG.solvableRadical H).map φ).Normal :=
    (CFSG.SignalizerFunctorTheorem.Nonsolvable.instNormalSolvableRadical
      (G := H)).map φ hφ
  have hbot : (CFSG.solvableRadical H).map φ = ⊥ :=
    CFSG.OddTranspositions.eq_bot_of_normal_of_isSolvable_perm_five _ hmap_solv
  exact (Subgroup.map_eq_bot_iff _).mp hbot

theorem derivedSeries_perm_five_one_eq_two :
    derivedSeries (Equiv.Perm (Fin 5)) 1 = derivedSeries (Equiv.Perm (Fin 5)) 2 := by
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  rw [derivedSeries_one, show (2 : ℕ) = 1 + 1 from rfl, derivedSeries_succ, derivedSeries_one,
    alternatingGroup.commutator_perm_eq h5, commutator_alternatingGroup_eq_self h5]

theorem derivedSeries_quot_solvableRadical_Halpha_of_o4PairData {G : Type} [Group G] [Finite G]
    {D : Set G} (hC : HypothesisC D) (hO4 : CFSG.OddTranspositions.QZ.O4PairData G D) :
    derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 =
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2 := by
  classical
  obtain ⟨ψ⟩ := CFSG.OddTranspositions.PartThree.nonempty_Halpha_equiv_Yten hC hO4
  obtain ⟨e, -⟩ := CFSG.OddTranspositions.QZ.fixK_equiv_s5
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let φ : H →* Equiv.Perm (Fin 5) :=
    (e : FixK →* Equiv.Perm (Fin 5)).comp (leftHomYten.comp (ψ : H →* Yten))
  have hφ : Function.Surjective φ :=
    e.surjective.comp (leftHomYten_surjective.comp ψ.surjective)
  have hker : Group.IsSolvable φ.ker :=
    isSolvable_ker_comp_leftHomYten_comp ψ e
  have hKle : φ.ker ≤ R :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (MonoidHom.normal_ker φ) hker
  have hRle : R ≤ φ.ker := solvableRadical_le_ker_comp_leftHomYten_comp ψ e
  have hRK : R = φ.ker := le_antisymm hRle hKle
  let eQ : (H ⧸ R) ≃* Equiv.Perm (Fin 5) :=
    QuotientGroup.liftEquiv R hφ hRK
  have hS5 : derivedSeries (Equiv.Perm (Fin 5)) 1 =
      derivedSeries (Equiv.Perm (Fin 5)) 2 :=
    derivedSeries_perm_five_one_eq_two
  have hmain : derivedSeries (H ⧸ R) 1 = derivedSeries (H ⧸ R) 2 := by
    calc derivedSeries (H ⧸ R) 1
        = (derivedSeries (Equiv.Perm (Fin 5)) 1).map
            (eQ.symm : Equiv.Perm (Fin 5) →* (H ⧸ R)) :=
          (map_derivedSeries_eq (f := (eQ.symm : Equiv.Perm (Fin 5) →* (H ⧸ R)))
            eQ.symm.surjective 1).symm
      _ = (derivedSeries (Equiv.Perm (Fin 5)) 2).map
            (eQ.symm : Equiv.Perm (Fin 5) →* (H ⧸ R)) := by rw [hS5]
      _ = derivedSeries (H ⧸ R) 2 :=
          map_derivedSeries_eq (f := (eQ.symm : Equiv.Perm (Fin 5) →* (H ⧸ R)))
            eQ.symm.surjective 2
  exact hmain

end CFSG.OddTranspositions.PartThree.EightEight

end
