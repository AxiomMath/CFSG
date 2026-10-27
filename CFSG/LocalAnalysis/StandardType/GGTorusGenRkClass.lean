module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUBlock
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input183
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CGT.PushingUpLit.BHS.NaturalDefs
public import CFSG.CGT.PushingUpLit.BHS.SymNatDefs
public import CFSG.CGT.PushingUpLit.Statements
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.AltCentre
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenGivenNatural
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightTenSplit
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.TwoGroupExtension
public import CFSG.HardMathSupport.Solomon.Coordinator.I2_5
public import CFSG.LieType.ChevTwo.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Containment
public import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12c
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1920Quot
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Lift
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.RankThree.PartTwo.KFacts.K72OutL2
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.Walter.Bender1970.S3.Setup
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private theorem isQuasisimple_or_isSolvable_blockSU
    {d n : ℕ} {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 n K)
    {S : Finset (Fin d)} (hS : 2 ≤ S.card) :
    CFSG.IsQuasisimple ↥(TableBUE.blockSU (K := K) (n := n) S) ∨
      Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := n) S) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn1 : n = 1 := by have := hKd.one_le; omega
    subst hn1
    rcases Nat.lt_or_ge S.card 4 with h4 | h4
    · right
      haveI : Group.IsSolvable ↥(unitarySU 2 1 K S.card) :=
        WitSU.isSolvable_unitarySU_two_one hKd (by omega) (by omega)
      exact Group.isSolvable_of_surjective (f := (TableBUE.blockSUEquiv S hKd).toMonoidHom)
        (TableBUE.blockSUEquiv S hKd).surjective
    · left
      refine TableBUE.isQuasisimple_blockSU S hKd hKd.card_eq_sq (by omega) ?_
      intro h
      have : S.card = 3 := by simpa using congrArg Prod.fst h
      omega
  · left
    exact SURepair.isQuasisimple_blockSU_of_two_le (f := n) (n := d) hKd hn hS

private theorem not_isSolvable_of_isQuasisimple_native {Q : Type*} [Group Q]
    (hQ : CFSG.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hsimple.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  haveI : Group.IsPerfect Q := hperf
  exact Group.IsPerfect.not_isSolvable Q

private theorem blockSU_empty_eq_bot {d n : ℕ} {K : Type} [Field K] :
    TableBUE.blockSU (K := K) (n := n) (∅ : Finset (Fin d)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hM := TableBUE.mem_blockSU.mp hx
  apply Subtype.ext
  apply Units.ext
  ext i j
  simpa using hM i j (Or.inl (by simp))

private theorem blockSU_eq_bot_of_card_le_one {d n : ℕ} {K : Type} [Field K]
    [Finite K] (hKd : UnitaryFieldData 2 n K) {S : Finset (Fin d)} (hS : S.card ≤ 1) :
    TableBUE.blockSU (K := K) (n := n) S = ⊥ := by
  rcases eq_or_ne S.card 0 with h0 | h0
  · rw [Finset.card_eq_zero.mp h0]
    exact blockSU_empty_eq_bot
  · have h1 : S.card = 1 := by omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h1
    exact SUTorus.blockSU_singleton (f := n) (n := d) hKd i

open Classical in
private theorem exists_le_blockSU_of_isComponentOf
    {d n : ℕ} {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 n K)
    {t : Fin d → K} (ht : ∀ i, t i ≠ 0) (δ : MulAut ↥(unitarySU 2 n K d))
    (hδ : ∀ s : ↥(unitarySU 2 n K d),
      (((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    {Q : Subgroup ↥(unitarySU 2 n K d)} (hQ : IsComponentOf Q (ggFix δ)) :
    ∃ i₀ : Fin d, Q ≤ TableBUE.blockSU (K := K) (n := n)
      (Finset.univ.filter fun i => t i = t i₀) := by
  classical
  obtain ⟨hfix, hcomm, hder⟩ := ggFix_diag_block_structure hKd ht δ hδ
  have hperf : ⁅Q, Q⁆ = Q := by
    have h := congrArg (Subgroup.map Q.subtype) hQ.2.2.1
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  have hQle : Q ≤ ⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n)
      (Finset.univ.filter fun i => t i = t i₀) := by
    calc Q = ⁅Q, Q⁆ := hperf.symm
      _ ≤ ⁅ggFix δ, ggFix δ⁆ := Subgroup.commutator_mono hQ.1 hQ.1
      _ ≤ ⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n)
            (Finset.univ.filter fun i => t i = t i₀) := hder
  by_contra hcontr
  have hnot : ∀ i₀ : Fin d, ¬ Q ≤ TableBUE.blockSU (K := K) (n := n)
      (Finset.univ.filter fun i => t i = t i₀) := fun i₀ hi => hcontr ⟨i₀, hi⟩
  have hcomm_all : ∀ i₀ : Fin d,
      ⁅Q, TableBUE.blockSU (K := K) (n := n)
        (Finset.univ.filter fun i => t i = t i₀)⁆ = ⊥ := by
    intro i₀
    exact (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input183.comp_le_or_comm hQ (hfix i₀).1
      ((Subgroup.le_normalizer_iff).2 (hfix i₀).2)).resolve_left (hnot i₀)
  have hcentral : (⨆ i₀ : Fin d, TableBUE.blockSU (K := K) (n := n)
      (Finset.univ.filter fun i => t i = t i₀)) ≤
      Subgroup.centralizer (Q : Set ↥(unitarySU 2 n K d)) := by
    refine iSup_le fun i₀ => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm_all i₀
  have hQcent : Q ≤ Subgroup.centralizer (Q : Set ↥(unitarySU 2 n K d)) := hQle.trans hcentral
  have hQopen : CFSG.Open.IsComponentOf Q (ggFix δ) := (CFSG.Assembly.isComponentOf_iff_open).1 hQ
  obtain ⟨r, hr, s, hs, hrs⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input183.exists_noncomm_of_isComponentOf hQopen
  exact hrs (Subgroup.mem_centralizer_iff.1 (hQcent hr) s hs).symm

private theorem eq_of_le_blockSU
    {d n : ℕ} {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 n K)
    {S : Finset (Fin d)} (hS : 2 ≤ S.card)
    {δ : MulAut ↥(unitarySU 2 n K d)}
    {Q : Subgroup ↥(unitarySU 2 n K d)} (hQ : IsComponentOf Q (ggFix δ))
    (hBA : TableBUE.blockSU (K := K) (n := n) S ≤ ggFix δ)
    (hle : Q ≤ TableBUE.blockSU (K := K) (n := n) S) :
    Q = TableBUE.blockSU (K := K) (n := n) S := by
  classical
  have hQB : IsComponentOf Q (TableBUE.blockSU (K := K) (n := n) S) :=
    hQ.of_le_of_le hle hBA
  have hsub : (Q.subgroupOf (TableBUE.blockSU (K := K) (n := n) S)).IsSubnormal :=
    hQB.2.1.subgroupOf
  rcases isQuasisimple_or_isSolvable_blockSU hKd hS with hBq | hBsol
  · rcases quasisimple_subnormal_subgroups hBq hsub with htop | hcen
    · have hBleQ : TableBUE.blockSU (K := K) (n := n) S ≤ Q :=
        Subgroup.subgroupOf_eq_top.1 htop
      exact le_antisymm hQB.1 hBleQ
    · exfalso
      obtain ⟨r, hr, s, hs, hrs⟩ :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input183.exists_noncomm_of_isComponentOf
          ((CFSG.Assembly.isComponentOf_iff_open).1 hQB)
      have hrB : (⟨r, hQB.1 hr⟩ : ↥(TableBUE.blockSU (K := K) (n := n) S)) ∈
          Q.subgroupOf (TableBUE.blockSU (K := K) (n := n) S) := hr
      have hsB : (⟨s, hQB.1 hs⟩ : ↥(TableBUE.blockSU (K := K) (n := n) S)) ∈
          Q.subgroupOf (TableBUE.blockSU (K := K) (n := n) S) := hs
      have hcomm := Subgroup.mem_center_iff.1 (hcen hrB)
        (⟨s, hQB.1 hs⟩ : ↥(TableBUE.blockSU (K := K) (n := n) S))
      apply hrs
      simpa using (congrArg
        (fun z : ↥(TableBUE.blockSU (K := K) (n := n) S) => (z : ↥(unitarySU 2 n K d)))
        hcomm).symm
  · exfalso
    haveI : Group.IsSolvable ↥(TableBUE.blockSU (K := K) (n := n) S) := hBsol
    have hQq : CFSG.IsQuasisimple
        ↥(Q.subgroupOf (TableBUE.blockSU (K := K) (n := n) S)) :=
      (isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hQB.1)).2
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native Q).1 hQB.2.2)
    exact (not_isSolvable_of_isQuasisimple_native hQq) inferInstance

open Classical in
theorem eq_blockSU_of_isComponentOf_ggFix_diag
    {d n : ℕ} {K : Type} [Field K] [Finite K] (hKd : UnitaryFieldData 2 n K)
    {t : Fin d → K} (ht : ∀ i, t i ≠ 0) (δ : MulAut ↥(unitarySU 2 n K d))
    (hδ : ∀ s : ↥(unitarySU 2 n K d),
      (((δ s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) * diagonal t =
        diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K))
    {Q : Subgroup ↥(unitarySU 2 n K d)} (hQ : IsComponentOf Q (ggFix δ)) :
    ∃ i₀ : Fin d, 2 ≤ (Finset.univ.filter fun i => t i = t i₀).card ∧
      Q = TableBUE.blockSU (K := K) (n := n) (Finset.univ.filter fun i => t i = t i₀) := by
  obtain ⟨hfix, -, -⟩ := ggFix_diag_block_structure hKd ht δ hδ
  obtain ⟨i₀, hle⟩ := exists_le_blockSU_of_isComponentOf hKd ht δ hδ hQ
  by_cases hS2 : 2 ≤ (Finset.univ.filter fun i => t i = t i₀).card
  · exact ⟨i₀, hS2, eq_of_le_blockSU hKd hS2 hQ (hfix i₀).1 hle⟩
  · exfalso
    have hS1 : (Finset.univ.filter fun i => t i = t i₀).card ≤ 1 := by omega
    have hbot : TableBUE.blockSU (K := K) (n := n)
        (Finset.univ.filter fun i => t i = t i₀) = ⊥ :=
      blockSU_eq_bot_of_card_le_one hKd hS1
    have hQbot : Q ≤ ⊥ := hle.trans (le_of_eq hbot)
    have hQopen : CFSG.Open.IsComponentOf Q (ggFix δ) := (CFSG.Assembly.isComponentOf_iff_open).1 hQ
    obtain ⟨r, hr, s, hs, hrs⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input183.exists_noncomm_of_isComponentOf hQopen
    have hr1 : r = 1 := Subgroup.mem_bot.mp (hQbot hr)
    have hs1 : s = 1 := Subgroup.mem_bot.mp (hQbot hs)
    exact hrs (by rw [hr1, hs1])

end CFSG.StandardType
