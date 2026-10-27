module

public import CFSG.OddTranspositions.PartFour.Statements
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.PartThree.Eleven.Statements
public import CFSG.OddTranspositions.PartThree.FiveReflection
public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.OddTranspositions.WidthSylow
import CFSG.OddTranspositions.PartThree.Ten.WreathRigidity
import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.OddTranspositions.PartThree.FiveReflectionFischerConverse
import CFSG.OddTranspositions.PartThree.FiveReflectionRescale
import CFSG.OddTranspositions.PartFour.Fourteen.ModelBender
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Plus
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus
import CFSG.OddTranspositions.PartFour.Fourteen.ModelUnitary
import CFSG.OddTranspositions.PartFour.Fourteen.ModelBenderDistinct
import CFSG.OddTranspositions.PartFour.Fourteen.ModelTwelveOne
import CFSG.OddTranspositions.PartFour.Fourteen.Table
public import CFSG.CGT.Timmesfeld75.Cfg214Gen
public import CFSG.LargeExtraspecial.S9TIXC
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
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
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvUnitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderAutE4Unitary
import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderONan
import CFSG.OddTranspositions.O4PairTenWidth
import CFSG.OddTranspositions.Width
import CFSG.RankThree.GF2n.Tim79aSec2
import CFSG.RankThree.GF2n.Tim79aSec23Inputs
import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Defs

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.OddTranspositions.PartFour
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def TwelveOneShape (hC : HypothesisC D) : Prop :=
  (∃ s ∈ imageClass hC, ∃ m f : ℕ, 4 ≤ m ∧ 2 ≤ f ∧
      (IsSymplecticTransvection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
          m f s ∨
        IsUnitaryTransvection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
          m f s ∨
        (6 ≤ m ∧ IsOrthReflection
          (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s))) ∨
    ∃ (k : ℕ) (ε π : Bool), 4 ≤ k ∧ PartThree.IsFiveReflectionModel k ε π (imageClass hC)

@[expose] def TheoremFourConclusion (hC : HypothesisC D) : Prop :=
  (∃ s ∈ imageClass hC, ∃ m f : ℕ, 2 ≤ m ∧ 2 ≤ f ∧
      IsSymplecticTransvection
        (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s ∧
      ∃ t ∈ D, IsOrthReflection G (m + 2) f t) ∨
    (∃ (k : ℕ) (ε π : Bool), 3 ≤ k ∧
      PartThree.IsFiveReflectionModel k (ε == π) π (imageClass hC) ∧
      PartThree.IsFiveReflectionModel (k + 1) ε π D) ∨
    (∃ f n : ℕ, 2 ≤ f ∧ 5 ≤ n ∧
      Nonempty (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha) ≃* L2Wreath f n) ∧
      Nonempty (G ≃* L2Wreath f (n + 2)))


theorem twelveOne
    (h91 : Theorem9_1) (h101 : Theorem10_1)
    (h111 : Theorem11_1) (h112 : Theorem11_2)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hE : PartFour.HypothesisE hC)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hO4 : ¬ ∃ s ∈ imageClass hC, ∃ f : ℕ, 2 ≤ f ∧
      IsOrthReflection (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 4 f s) :
    TheoremFourConclusion hC ∨ TwelveOneShape hC := by
  classical
  have hrc : CFSG.solvableRadical (Halpha D hC.alpha) = Subgroup.center (Halpha D hC.alpha) :=
    le_antisymm hMZ (center_le_solvableRadical _)
  let φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) :=
    QuotientGroup.quotientMulEquivOfEq hrc
  have hZ : Subgroup.center (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) = ⊥ := by
    have h := center_le_solvableRadical
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
    rw [solvableRadical_quotient_H hC] at h
    exact le_bot_iff.mp h
  have hinv : ¬ Group.IsSolvable (Halpha D hC.alpha) →
      ∀ s ∈ imageClass hC, s * s = 1 ∧ s ≠ 1 := fun hHns s hs => by
    have h2 := imageClass_involutions hC hHns s hs
    refine ⟨?_, fun h1 => by rw [h1, orderOf_one] at h2; omega⟩
    have := pow_orderOf_eq_one s
    rwa [h2, pow_two] at this
  have hBφ : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) →
      CFSG.BenderSuzuki.IsBenderGroup
        (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) := by
    rintro (⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩)
    · exact .isPSL2 n hn (φ.symm.trans e)
    · exact .isSuzuki n hn (φ.symm.trans e)
    · exact .isPSU3 n hn (φ.symm.trans e)
  have hcen : ∀ {f : ℕ}, 2 ≤ f → (↥(commutator G) ≃* CFSG.Theory.Comparator.PSL2Model (2 * f)) →
      Subgroup.centralizer (commutator G : Set G) = ⊥ := by
    intro f hf e
    have hZc : Subgroup.center (↥(commutator G)) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : e x ∈ Subgroup.center (CFSG.Theory.Comparator.PSL2Model (2 * f)) := by
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro y
        obtain ⟨z, rfl⟩ := e.surjective y
        rw [← map_mul, ← map_mul, hx z]
      rw [center_psl2Model_eq_bot (by omega), Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (e.injective (hx'.trans e.map_one.symm))
    have hCG : ∀ x ∈ Subgroup.centralizer (commutator G : Set G), x ∈ commutator G → x = 1 := by
      intro x hxC hxG
      have hmem : (⟨x, hxG⟩ : commutator G) ∈ Subgroup.center (commutator G) := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
      rw [hZc, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    refine hrad _ inferInstance (isSolvable_of_comm fun a b => Subtype.ext ?_)
    have hC' : ⁅(a : G), (b : G)⁆ ∈ Subgroup.centralizer (commutator G : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ a.2 b.2)
        (Subgroup.inv_mem _ a.2)) (Subgroup.inv_mem _ b.2)
    have hG' : ⁅(a : G), (b : G)⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top (a : G)) (Subgroup.mem_top (b : G))
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hCG _ hC' hG')
  have hBen : CFSG.BenderSuzuki.IsBenderGroup
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) →
      ∃ f' : ℕ, 2 ≤ f' ∧ Nonempty (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)
        ≃* CFSG.Theory.Comparator.PSL2Model f') ∧ TheoremFourConclusion hC := by
    intro hB
    obtain ⟨f', hf', ⟨eH⟩, hG⟩ := h91 G D hC hrad hrc (hBφ hB)
    have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) := fun hsol => by
      have hs' : Group.IsSolvable (CFSG.Theory.Comparator.PSL2Model f') :=
        solvable_of_surjective (f := eH.toMonoidHom.comp
          (QuotientGroup.mk' (Subgroup.center (Halpha D hC.alpha))))
          (eH.surjective.comp (QuotientGroup.mk'_surjective _))
      have hP := SetupQ.isPerfect_psl2Model hf'
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model f') :=
        CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup
          (CFSG.BenderSuzuki.IsBenderGroup.isPSL2 f' hf' (MulEquiv.refl _))
      have : Nontrivial (CFSG.Theory.Comparator.PSL2Model f') := IsSimpleGroup.toNontrivial
      have hlt := IsSolvable.commutator_lt_top_of_nontrivial (CFSG.Theory.Comparator.PSL2Model f')
      rw [Group.isPerfect_def.mp hP] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨s, hs⟩ := imageClass_nonempty hC
    refine ⟨f', hf', ⟨φ.trans eH⟩, Or.inl ⟨s, hs, 2, f', le_rfl, hf',
      isSymplecticTransvection_of_mulEquiv_psl2Model hf' (φ.trans eH) (hinv hHns s hs).1
        (hinv hHns s hs).2, ?_⟩⟩
    rcases hG with ⟨⟨eG⟩⟩ | ⟨⟨eG'⟩, hidx⟩
    · exact exists_isOrthReflection_of_mulEquiv_l2Wreath_two hC.setup hf' eG
    · exact exists_isOrthReflection_of_commutator_psl2Model hC.setup (hcen hf' eG') hf' eG' hidx
  rcases hE with ⟨s, hs, m, f, hm, hf, hsp | hun | hor⟩ | ⟨n, hn, b, hsym, hnd, hM⟩ |
      ⟨s, hs, f, m, hm5, hW⟩ | ⟨f, hSz⟩
  ·
    obtain ⟨k, hk, -⟩ := id hsp
    by_cases hm2 : m = 2
    · subst hm2
      obtain ⟨-, -, -, h⟩ := hBen (isBenderGroup_of_isSymplecticTransvection_two hZ hf hsp)
      exact Or.inl h
    · exact Or.inr (Or.inl ⟨s, hs, m, f, by omega, hf, Or.inl hsp⟩)
  ·
    rcases (show m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | hm4
    · obtain ⟨-, -, -, h⟩ := hBen (isBenderGroup_of_isUnitaryTransvection_two hZ hf hun)
      exact Or.inl h
    · obtain ⟨f', hf', ⟨e2⟩, -⟩ := hBen (isBenderGroup_of_isUnitaryTransvection_three hZ hf hun)
      obtain ⟨e3⟩ := nonempty_mulEquiv_psu3Model_of_isUnitaryTransvection_three hZ hf hun
      exact (false_of_mulEquiv_psu3Model_of_mulEquiv_psl2Model hf e3 e2).elim
    · exact Or.inr (Or.inl ⟨s, hs, m, f, hm4, hf, Or.inr (Or.inl hun)⟩)
  ·
    have hm46 : m = 4 ∨ 6 ≤ m := by
      rcases id hor with ⟨k, hk, hmk, -⟩ | ⟨k, hk, hmk, -⟩ <;> omega
    rcases hm46 with rfl | hm6
    · exact (hO4 ⟨s, hs, f, hf, hor⟩).elim
    · exact Or.inr (Or.inl ⟨s, hs, m, f, by omega, hf, Or.inr (Or.inr ⟨hm6, hor⟩)⟩)
  ·
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨ε, hε⟩ := exists_isFiveReflectionModel_of_fischerModel
      (X := Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))
      (E := imageClass hC) (k := k) (b := b) hsym hnd hM
    by_cases hk3 : k = 3
    · subst hk3
      cases ε
      · have hG : PartThree.IsFiveReflectionModel 4 true false D :=
          h112 G D hC hrad hrc ⟨true, hε⟩
        have hG' : PartThree.IsFiveReflectionModel 4 false true D :=
          IsFiveReflectionModel.four_not (ε := true) (π := false) hG
        exact Or.inl (Or.inr (Or.inl ⟨3, false, true, le_rfl, hε, hG'⟩))
      · have hG : PartThree.IsFiveReflectionModel 4 true true D :=
          h111 G D hC hrad hrc ⟨true, hε⟩
        exact Or.inl (Or.inr (Or.inl ⟨3, true, true, le_rfl, hε, hG⟩))
    · exact Or.inr (Or.inr ⟨k, ε, true, by omega, hε⟩)
  ·
    obtain ⟨eW⟩ := nonempty_mulEquiv_l2Wreath_of_isWreathTransposition hZ hW
    have hf : 2 ≤ f := hW.1
    obtain ⟨eG⟩ := h101 G D hC hrad hrc f m hf hm5 ⟨φ.symm.trans eW⟩
    exact Or.inl (Or.inr (Or.inr ⟨f, m, hf, hm5, ⟨eW⟩, ⟨eG⟩⟩))
  ·
    obtain ⟨f', hf', ⟨e2⟩, -⟩ := hBen (isBenderGroup_of_isSz hSz)
    exact (false_of_isSz_of_mulEquiv_psl2Model hSz e2).elim

end CFSG.OddTranspositions.PartThree

end
