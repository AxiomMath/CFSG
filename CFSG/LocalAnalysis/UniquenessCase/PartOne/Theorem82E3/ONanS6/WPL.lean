module

public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.RankThree.LocalRank.ThetaCoreQuotients
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.SuzOddCore.ExtModel

public section

namespace CFSG.RankThree.GroupTheory
section
open CFSG
open CFSG.RankThree.LocalRank

theorem le_solvableCore_of_centralizes_pCore_three_and_components
    {H : Type*} [Group H] [Finite H] {W : Subgroup H}
    (hW2 : IsPGroup 2 W)
    (hO3 : W.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤
      Subgroup.centralizer
        ((CFSG.pCore 3 (H ⧸ aschbacherSolvableCore 3 H) : Subgroup _) : Set _))
    (hcomp : ∀ J : Subgroup (H ⧸ aschbacherSolvableCore 3 H), CFSG.IsComponent J →
      W.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≤
        Subgroup.centralizer (J : Set _)) :
    W ≤ aschbacherSolvableCore 3 H := by
  classical
  let N : Subgroup H := aschbacherSolvableCore 3 H
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let X := H ⧸ N
  let WX : Subgroup X := W.map π
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWX2 : IsPGroup 2 WX := hW2.map π
  obtain ⟨hNsol, -, hNp, hNmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := H) Nat.prime_three
  have hθX : aschbacherSolvableCore 3 X = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers Nat.prime_three N hNsol hNp).2.2.1
  have hlayer : WX ≤ Subgroup.centralizer (CFSG.layer X : Set X) := by
    rw [CFSG.layer.eq_sSup, sSup_eq_iSup']
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
      (fun J : {J : Subgroup X // CFSG.IsComponent J} => ((J : Subgroup X) : Subgroup X)) ?_
    intro J
    simpa [X, WX, π, N] using hcomp J.1 J.2
  have hfit : WX ≤ Subgroup.centralizer (CFSG.fittingSubgroup X : Set X) := by
    refine CFSG.subgroup_le_centralizer_fitting_of_le_centralizer_pCores ?_
    intro q
    by_cases hq3 : q.1.1 = 3
    · rw [hq3]
      simpa [X, WX, π, N] using hO3
    · have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hcore : CFSG.pCore q.1.1 X ≤ aschbacherSolvableCore 3 X :=
        (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.2.2.2
          q.1.1 hqprime hq3
      rw [hθX] at hcore
      have hbot : CFSG.pCore q.1.1 X = ⊥ := le_bot_iff.mp hcore
      rw [hbot, Subgroup.le_centralizer_iff]
      exact bot_le
  have hgen : WX ≤ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [CFSG.generalizedFitting.eq_sup]
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hfit) (Subgroup.le_centralizer_iff.mp hlayer)
  have hWXle : WX ≤ CFSG.generalizedFitting X :=
    hgen.trans (CFSG.centralizer_generalizedFitting_le X)
  set F : Subgroup X := CFSG.generalizedFitting X with hF
  set Z : Subgroup ↥F := Subgroup.center ↥F with hZ
  set Ω : Subgroup ↥Z := CFSG.pCore 2 ↥Z with hΩ
  set V : Subgroup ↥F := Ω.map Z.subtype with hV
  set U : Subgroup X := V.map F.subtype with hU
  haveI hZchar : Z.Characteristic := Subgroup.centerCharacteristic
  haveI hΩchar : Ω.Characteristic := CFSG.pCore_characteristic
  haveI hVchar : V.Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  haveI hFchar : F.Characteristic := CFSG.LocalCores.generalized_fitting_characteristic.1
  haveI hUchar : U.Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  have hV2 : IsPGroup 2 V := (CFSG.pCore_isPGroup (p := 2) (G := ↥Z)).map Z.subtype
  have hU2 : IsPGroup 2 U := hV2.map F.subtype
  have hUle : U ≤ CFSG.pCore 2 X := le_sSup ⟨inferInstance, hU2⟩
  have hcore2 : CFSG.pCore 2 X = ⊥ := by
    apply le_bot_iff.mp
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := X)).isNilpotent
    haveI : Group.IsSolvable ↥(CFSG.pCore 2 X) := inferInstance
    have hmaxX := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.1
    exact (hmaxX (CFSG.pCore 2 X) inferInstance inferInstance
      (CFSG.GroupTheory.not_dvd_card_of_isPGroup
        (CFSG.pCore_isPGroup (p := 2) (G := X)) Nat.prime_three (by norm_num))).trans
      (le_of_eq hθX)
  have hUbot : U = ⊥ := le_bot_iff.mp (hUle.trans (le_of_eq hcore2))
  have hVbot : V = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective V F.subtype_injective).mp
      (by simpa [U] using hUbot)
  have hΩbot : Ω = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective Ω Z.subtype_injective).mp
      (by simpa [V] using hVbot)
  have hWsubF : WX.subgroupOf F ≤ Z := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro f
    apply Subtype.ext
    have hw' : ((w : ↥F) : X) ∈ WX := by
      simpa [Subgroup.mem_subgroupOf] using hw
    exact Subgroup.mem_centralizer_iff.mp (hgen hw') (f : X) f.2
  have hWsubF2 : IsPGroup 2 (WX.subgroupOf F) :=
    hWX2.of_equiv (Subgroup.subgroupOfEquivOfLe hWXle).symm
  have hWsubZ : (WX.subgroupOf F).subgroupOf Z ≤ Ω := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact hWsubF2.of_equiv (Subgroup.subgroupOfEquivOfLe hWsubF).symm
  have hWsubZbot : (WX.subgroupOf F).subgroupOf Z = ⊥ :=
    le_bot_iff.mp (hWsubZ.trans (le_of_eq hΩbot))
  have hWsubFbot : WX.subgroupOf F = ⊥ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWsubF, hWsubZbot, Subgroup.map_bot]
  have hWXbot : WX = ⊥ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hWXle, hWsubFbot, Subgroup.map_bot]
  have hleN : W ≤ N := by
    simpa [π, N] using (Subgroup.map_eq_bot_iff (f := π) W).mp hWXbot
  exact hleN

end
end CFSG.RankThree.GroupTheory
