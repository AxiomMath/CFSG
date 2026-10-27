module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C621Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C623c
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632e
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C634Q
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C634c
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.K332T3
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591K
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591V
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591Db
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Da
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Dd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

structure KernelsW {G : Type} [Group G] [Finite G] (Dat : Data G) : Prop where
  k332three : UCK.K332Three
  l620 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.L620
  c621 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.r ≠ 3 → m.C621
  c622 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C622
  c624 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C624
  c625 : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → 3 < m.r → m.C625
  c626gen : ∀ m : Mz614 Dat, R6_7 Dat → R6_9 Dat → m.C626gen
  k35c : UCK.K35c
  k631 : UCK.K631
  ksz : UCK.KSz
  kc633 : ∀ m : Mz614 Dat, m.L620 → m.KC633
  kn633 : ∀ m : Mz614 Dat, m.L620 → m.KN633
  kinv633 : ∀ m : Mz614 Dat, m.L620 → m.KInv633
  k461 : UCK.K461

namespace KernelsW

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (h : KernelsW Dat) (m : Mz614 Dat)
  (h67 : R6_7 Dat) (h69 : R6_9 Dat)

include h h67 h69

theorem C620 : m.C620 := (h.l620 m h67 h69).1

theorem C619 : m.C619 := m.six19 h69 (h.C620 m h67 h69)

theorem C621 : m.C621 := by
  by_cases hr3 : m.r = 3
  · exact m.c621_of_L620 hr3 (h.l620 m h67 h69)
  · exact h.c621 m h67 h69 hr3

theorem C623 (hr3 : m.r = 3) : m.C623 :=
  m.c623_of_kernels hr3 h69 (h.C620 m h67 h69) (h.C621 m h67 h69)
    (m.c621x_of_L620 hr3 (h.l620 m h67 h69))

theorem C625 : m.C625 := by
  by_cases hr3 : m.r = 3
  · exact m.six25_of_K332Three h.k332three h69 hr3 (h.C623 m h67 h69 hr3)
  · exact h.c625 m h67 h69 (by have := m.hr.two_le; have := m.d.odd; omega)

theorem C626 : m.C626 := m.c626_of_kernels (h.c626gen m h67 h69) (h.C619 m h67 h69)

theorem C628b : m.C628b := m.six28b k47_uc6 h69 (h.C626 m h67 h69) m.c627

theorem C629 : m.C629 :=
  m.six29 (h.C625 m h67 h69) (h.C626 m h67 h69) (h.C628b m h67 h69)

theorem C631 : m.C631 :=
  m.c631_of_K631 h.k631 (h.C620 m h67 h69) (h.C621 m h67 h69) (h.C625 m h67 h69)
    (h.C629 m h67 h69)

theorem C632 : m.C632 :=
  m.c632_of_kernels h.k35c (h.C625 m h67 h69) (h.C626 m h67 h69) (h.C628b m h67 h69)
    (h.C631 m h67 h69)

theorem C634 (hr3 : m.r = 3) : m.C634 := by
  intro hex
  have hVC := m.vtrivial_of_inverts' hr3 (r6_3_of_theoremC Dat m.hC) h67 h69
    (h.C619 m h67 h69) (h.C620 m h67 h69) (h.C621 m h67 h69) (h.C625 m h67 h69)
    (h.C632 m h67 h69) (h.kc633 m (h.l620 m h67 h69)) (h.kn633 m (h.l620 m h67 h69))
    (h.kinv633 m (h.l620 m h67 h69)) hex
  have halt1 : ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K :=
    m.c628a'_of hr3 k42_uc6 (UCK.lemmaC_of_KSz h.ksz) hVC
  exact m.tail_false hr3 (UCK.k634_of_k461 h.k461) (m.c634Q_of_inputs (h.C629 m h67 h69) halt1)
    (h.C625 m h67 h69) (h.C626 m h67 h69) hVC

theorem C635 : m.C635 :=
  m.three_lt_r' (fun _ => h.C625 m h67 h69) (h.C629 m h67 h69)
    (fun hr3 => h.C634 m h67 h69 hr3)

theorem C636 : m.C636 :=
  m.c636_of_r_gt_3 (h.C635 m h67 h69) (r6_3_of_theoremC Dat m.hC) h69
    (h.C619 m h67 h69) (h.C620 m h67 h69) (h.C621 m h67 h69) (h.c622 m h67 h69)
    (h.C625 m h67 h69) (h.C632 m h67 h69) (h.kc633 m (h.l620 m h67 h69))
    (h.kn633 m (h.l620 m h67 h69))

end KernelsW

theorem KernelsW.toInputs {G : Type} [Group G] [Finite G]
    {Dat : Data G} (h : KernelsW Dat) (hC : TheoremCAt Dat.M) (h67 : R6_7 Dat) : UC6Inputs Dat := by
  have h69 : R6_9 Dat := r6_9_of_K47 k47_uc6 hC h67
  exact
    { r67 := fun _ => h67
      c619 := fun m => h.C619 m h67 h69
      c620 := fun m => h.C620 m h67 h69
      c624 := fun m => h.c624 m h67 h69
      c629 := fun m => h.C629 m h67 h69
      c632 := fun m => h.C632 m h67 h69
      c635 := fun m => h.C635 m h67 h69
      c636 := fun m => h.C636 m h67 h69 }

theorem r6_14_of_kernelsW {G : Type} [Group G] [Finite G]
    {Dat : Data G} (hk : Hooks Dat) (hC : TheoremCAt Dat.M) (h67 : R6_7 Dat) (h : KernelsW Dat) :
    R6_14 Dat :=
  r6_14_of_inputs hk hC (h.toInputs hC h67)

end CFSG.LocalAnalysis.UniquenessCase.UC6G
