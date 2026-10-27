module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.KernelsW
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K318Main
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588B15
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588C5
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588E9
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.S25b
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.L34Twist
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Disp626
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Disp633
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.P6b
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.P6c
public import CFSG.LocalAnalysis.UniquenessCase.UC6DispMult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

structure KFacts : Prop where
  kMult : UCK.KMult
  kMult3 : UCK.KMult3
  kSch : UCK.KSch
  k35Om : UCK.K35Ω
  k620exc : UCK.K620Exc
  k322 : UCK.K322
  k323 : UCK.K323
  kProjRepTits : UCK.KProjRepTits
  kProjRepA10 : UCK.KProjRepA10
  kProjRepL2 : UCK.KProjRepL2
  kMultL2 : UCK.KMultL2
  k324 : UCK.K324
  kOutP : UCK.KOutP
  kqs : UCK.KQS
  k332three : UCK.K332Three
  k35c : UCK.K35c
  k631 : UCK.K631
  ksz : UCK.KSz
  k461 : UCK.K461

section

theorem KernelsW.of_facts {G : Type} [Group G] [Finite G] {Dat : Data G} (F : KFacts) :
    KernelsW Dat := by
  have hl620 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.L620 :=
    l620_field_of_inputs F.kMult F.kMult3 F.kSch F.k35Om F.k620exc
  have hkp620 : UCK.KProjRep620 :=
    UCK.kProjRep620_of_clauses F.kProjRepL2 F.kProjRepTits F.kProjRepA10
  have hkml620 : UCK.KMultList620 := UCK.kMultList620_of_kMultL2 F.kMultL2
  have hK332 : UCK.K332' := UCK.K332'_of_inputs F.kMult F.kOutP F.kqs
  have hc622 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C622 :=
    fun m h67 h69 => Mz614.c622_direct m h69 (m.six19 h69 (hl620 m h67 h69).1) (hl620 m h67 h69)
  have hc621 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.r ≠ 3 → m.C621 :=
    fun m h67 h69 hr3 => by
    have hL := hl620 m h67 h69
    exact m.c621_of_L620_of_ne_three hr3 hkml620 h67 (m.six19 h69 hL.1)
      ((hc622 m h67 h69).quasisimple_of_ne_three hr3) hL
  have hc626 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C626gen :=
    fun m h67 h69 => by
    have hL := hl620 m h67 h69
    have h619 : m.C619 := m.six19 h69 hL.1
    exact m.c626gen_of_L620 hkml620 h67 h619
      (fun hr3 => (Mz614.c622_direct m h69 h619 hL).quasisimple_of_ne_three hr3) hL
      (fun hr3 hL34 _ => m.c626gen_of_l34_any h619 hL.1 hr3 hL34)
  have hc623A10 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C619 → m.C620 → m.r = 5 →
      CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt ↥m.L 10 → m.C623 :=
    fun m h67 h69 h619 h620 hr5 hA => Mz614.c623_of_A10 F.k322 F.k324 m h67 h69 h619 h620 hr5 hA
  have hc623 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → 3 < m.r → m.C623 :=
    fun m h67 h69 hr => by
    have hL := hl620 m h67 h69
    have h619 : m.C619 := m.six19 h69 hL.1
    have hq : CFSG.Open.IsQuasisimple ↥m.L :=
      (hc622 m h67 h69).quasisimple_of_ne_three (by omega)
    exact m.c623_of_L620 hr F.k322 F.k323 hkml620
      (fun hr5 hA => hc623A10 m h67 h69 h619 hL.1 hr5 hA) h67 h69 h619 hq hL
  have hc624 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C624 :=
    fun m h67 h69 hr3 => by
    have hr : 3 < m.r := by
      have := m.hr.two_le
      have := m.d.odd
      omega
    have hL := hl620 m h67 h69
    have h620 : m.C620 := hL.1
    have h619 : m.C619 := m.six19 h69 h620
    have hq : CFSG.Open.IsQuasisimple ↥m.L := (hc622 m h67 h69).quasisimple_of_ne_three hr3
    have hcen : Subgroup.center ↥m.L = ⊥ :=
      m.center_L_eq_bot h67 h619 (m.hmult_of_kMultList620 hkml620 hL hq hr)
    exact Mz614.c624_of_k332' hK332 F.kSch m h67 h69 h619 h620 (hc623 m h67 h69 hr)
      (m.isSimpleGroup_L hq hcen) (m.hL3_of_kProjRep620 hkp620 hL hq hr) hr3
  exact
    { k332three := F.k332three
      l620 := hl620
      c621 := hc621
      c622 := hc622
      c624 := hc624
      c625 := fun m h67 h69 hr => m.c625_of_k332' hK332 h69 (hc623 m h67 h69 hr) hr
      c626gen := hc626
      k35c := F.k35c
      k631 := F.k631
      ksz := F.ksz
      kc633 := fun m hL => m.kc633_of_L620 hL
      kn633 := fun m hL => m.kn633_of_L620 hL
      kinv633 := fun m hL => m.kinv633_of_L620 hL
      k461 := F.k461 }

end

end CFSG.LocalAnalysis.UniquenessCase.UC6G
