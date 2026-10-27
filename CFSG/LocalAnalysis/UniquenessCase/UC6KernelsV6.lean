module

public import CFSG.LocalAnalysis.UniquenessCase.UC6KernelsW
public import CFSG.LocalAnalysis.UniquenessCase.UC6S25b
public import CFSG.LocalAnalysis.UniquenessCase.UC6Star36b
public import CFSG.LocalAnalysis.UniquenessCase.UC6P6c
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B15
public import CFSG.LocalAnalysis.UniquenessCase.UC6Disp633
public import CFSG.LocalAnalysis.UniquenessCase.UC6Disp626
public import CFSG.LocalAnalysis.UniquenessCase.UC6KMultL2
public import CFSG.LocalAnalysis.UniquenessCase.UC6L34Twist
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E9
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332THolds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cDirect
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35OmDirect
public import CFSG.LocalAnalysis.UniquenessCase.UC6K323
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossMain
public import CFSG.LocalAnalysis.UniquenessCase.UC6K620ExcAHolds
public import CFSG.LocalAnalysis.UniquenessCase.UCK461Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Main
public import CFSG.LocalAnalysis.UniquenessCase.UC6K324Holds
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

structure UC6KernelsV6 : Prop where
  k315Spor : UCK.K315Spor

section

theorem UC6KernelsV6.toKernelsW
    (h : UC6KernelsV6) : UC6KernelsW := by
  have hmult : UCK.KMult := UCK.kMult_holds
  have hsch : UCK.KSch := UCK.kSch_holds
  have hl620 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.L620 :=
    UC6.l620_field_of_inputs hmult UCK.kMult3_holds hsch UCK.K35Ω_holds
      UCK.k620exc_holds
  have hk322 : UCK.K322 := UCK.k322_holds
  have hk323 : UCK.K323 := UCK.k323_holds
  have hkpt : UCK.KProjRepTits := fun J _ _ hq N _ hN h q hq' hq5 d hd f =>
    UCK.kProjRep_Tits J hq N hN h q hq' hq5 d hd f
  have hkpa : UCK.KProjRepA10 := fun J _ _ hq N _ hN h q hq' hq5 d hd f =>
    UCK.kProjRep_A10 J hq N hN h q hq' hq5 d hd f
  have hkp620 : UCK.KProjRep620 := UCK.kProjRep620_of_clauses UCK.kProjRepL2_holds hkpt hkpa
  have hkml620 : UCK.KMultList620 := UCK.kMultList620_of_kMultL2 UCK.kMultL2_holds
  have hc622 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C622 :=
    fun G _ _ m h67 h69 =>
      Mz614.c622_direct m h69 (m.six19 h69 (hl620 G m h67 h69).1) (hl620 G m h67 h69)
  have hc621 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.r ≠ 3 →
        m.C621 := fun G _ _ m h67 h69 hr3 => by
    have hL := hl620 G m h67 h69
    exact m.c621_of_L620_of_ne_three hr3 hkml620 h67 (m.six19 h69 hL.1)
      ((hc622 G m h67 h69).quasisimple_of_ne_three hr3) hL
  have hc626 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C626gen :=
    fun G _ _ m h67 h69 => by
    have hL := hl620 G m h67 h69
    have h619 : m.C619 := m.six19 h69 hL.1
    exact m.c626gen_of_L620 hkml620 h67 h619
      (fun hr3 => (Mz614.c622_direct m h69 h619 hL).quasisimple_of_ne_three hr3) hL
      (fun hr3 hL34 _ => m.c626gen_of_l34_any h619 hL.1 hr3 hL34)
  have hc623A10 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C619 → m.C620 →
        m.r = 5 → CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt ↥m.L 10 → m.C623 :=
    fun G _ _ m h67 h69 h619 h620 hr5 hA =>
      Mz614.c623_of_A10 hk322 UCK.k324_holds m h67 h69 h619 h620 hr5 hA
  have hc623 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → 3 < m.r →
        m.C623 := fun G _ _ m h67 h69 hr => by
    have hL := hl620 G m h67 h69
    have h619 : m.C619 := m.six19 h69 hL.1
    have hq : CFSG.Open.IsQuasisimple ↥m.L :=
      (hc622 G m h67 h69).quasisimple_of_ne_three (by omega)
    exact m.c623_of_L620 hr hk322 hk323 hkml620
      (fun hr5 hA => hc623A10 G m h67 h69 h619 hL.1 hr5 hA) h67 h69 h619 hq hL
  have hc624 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C624 :=
    fun G _ _ m h67 h69 hr3 => by
    have hr : 3 < m.r := by
      have := m.hr.two_le
      have := m.d.odd
      omega
    have hL := hl620 G m h67 h69
    have h620 : m.C620 := hL.1
    have h619 : m.C619 := m.six19 h69 h620
    have hq : CFSG.Open.IsQuasisimple ↥m.L := (hc622 G m h67 h69).quasisimple_of_ne_three hr3
    have hcen : Subgroup.center ↥m.L = ⊥ :=
      m.center_L_eq_bot h67 h619 (m.hmult_of_kMultList620 hkml620 hL hq hr)
    exact Mz614.c624_of_k332' (UCK.K332'_of_inputs hmult UCK.kOutP_holds UCK.kqs_holds) hsch m h67 h69
      h619 h620 (hc623 G m h67 h69 hr) (m.isSimpleGroup_L hq hcen)
      (m.hL3_of_kProjRep620 hkp620 hL hq hr) hr3
  exact
    { k332three := UCK.k332Three_holds
      k36 := UCK.k36_of_eqlStar
          (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
              UCK.k36OddDefChar_holds h.k315Spor UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree
      star36 := star36_holds
      l620 := hl620
      c621 := hc621
      c622 := hc622
      c624 := hc624
      c625 := fun G _ _ m h67 h69 hr =>
        m.c625_of_k332' (UCK.K332'_of_inputs hmult UCK.kOutP_holds UCK.kqs_holds) h69
          (hc623 G m h67 h69 hr) hr
      c626gen := hc626
      k35c := UCK.k35c_holds
      k631 := UCK.k631_holds
      ksz := UCK.kSz_holds
      kc633 := fun G _ _ m hL => m.kc633_of_L620 hL
      kn633 := fun G _ _ m hL => m.kn633_of_L620 hL
      kinv633 := fun G _ _ m hL => m.kinv633_of_L620 hL
      k461 := UCK.k461_holds }

theorem uc_theorem_6_14_four_of_kernelsV6
    (h : UC6KernelsV6) : Theorem614Four :=
  uc_theorem_6_14_four_of_kernelsW h.toKernelsW

end

end CFSG.LocalAnalysis.UniquenessCase.UC6
