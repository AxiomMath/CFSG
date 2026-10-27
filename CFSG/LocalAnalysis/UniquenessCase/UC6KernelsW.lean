module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C623c
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632e
public import CFSG.LocalAnalysis.UniquenessCase.UC6C634c
public import CFSG.LocalAnalysis.UniquenessCase.UC6C634Q
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixSeven
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6K42j
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591K
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591V
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Da
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Db
public import CFSG.LocalAnalysis.UniquenessCase.UC6M591Dd
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt Theorem614Four)

structure UC6KernelsW : Prop where
  k332three : UCK.K332Three
  k36 : UCK.K36
  star36 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G), S.InMSigma → TheoremCAt S.M →
      PartTwo.Star36At (dataOfSetup4 hS hU S)
  l620 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.L620
  c621 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.r ≠ 3 → m.C621
  c622 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C622
  c624 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C624
  c625 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → 3 < m.r → m.C625
  c626gen : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
    R6_7 (dataOfSetup4 m.hS m.hU m.S) → R6_9 (dataOfSetup4 m.hS m.hU m.S) → m.C626gen
  k35c : UCK.K35c
  k631 : UCK.K631
  ksz : UCK.KSz
  kc633 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.L620 → m.KC633
  kn633 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.L620 → m.KN633
  kinv633 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G), m.L620 → m.KInv633
  k461 : UCK.K461

namespace UC6KernelsW

variable (h : UC6KernelsW) {G : Type} [Group G] [Finite G] (m : Mz614 G)
  (h67 : R6_7 (dataOfSetup4 m.hS m.hU m.S)) (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S))

include h h67 h69

theorem C620 : m.C620 := (h.l620 G m h67 h69).1

theorem C619 : m.C619 := m.six19 h69 (h.C620 m h67 h69)

theorem C621 : m.C621 := by
  by_cases hr3 : m.r = 3
  · exact m.c621_of_L620 hr3 (h.l620 G m h67 h69)
  · exact h.c621 G m h67 h69 hr3

theorem C623 (hr3 : m.r = 3) : m.C623 :=
  m.c623_of_kernels hr3 h69 (h.C620 m h67 h69) (h.C621 m h67 h69)
    (m.c621x_of_L620 hr3 (h.l620 G m h67 h69))

theorem C625 : m.C625 := by
  by_cases hr3 : m.r = 3
  · exact m.six25_of_K332Three h.k332three h69 hr3 (h.C623 m h67 h69 hr3)
  · exact h.c625 G m h67 h69 (by have := m.hr.two_le; have := m.d.odd; omega)

theorem C626 : m.C626 := m.c626_of_kernels (h.c626gen G m h67 h69) (h.C619 m h67 h69)

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
  have hVC := m.vtrivial_of_inverts' hr3 (r6_3_dataOfSetup4 m.hS m.hU m.S m.hC) h67 h69
    (h.C619 m h67 h69) (h.C620 m h67 h69) (h.C621 m h67 h69) (h.C625 m h67 h69)
    (h.C632 m h67 h69) (h.kc633 G m (h.l620 G m h67 h69)) (h.kn633 G m (h.l620 G m h67 h69))
    (h.kinv633 G m (h.l620 G m h67 h69)) hex
  have halt1 : ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K :=
    m.c628a'_of hr3 k42_uc6 (UCK.lemmaC_of_KSz h.ksz) hVC
  exact m.tail_false hr3 (UCK.k634_of_k461 h.k461) (m.c634Q_of_inputs (h.C629 m h67 h69) halt1)
    (h.C625 m h67 h69) (h.C626 m h67 h69) hVC

theorem C635 : m.C635 :=
  m.three_lt_r' (fun _ => h.C625 m h67 h69) (h.C629 m h67 h69)
    (fun hr3 => h.C634 m h67 h69 hr3)

theorem C636 : m.C636 :=
  m.c636_of_r_gt_3 (h.C635 m h67 h69) (r6_3_dataOfSetup4 m.hS m.hU m.S m.hC) h69
    (h.C619 m h67 h69) (h.C620 m h67 h69) (h.C621 m h67 h69) (h.c622 G m h67 h69)
    (h.C625 m h67 h69) (h.C632 m h67 h69) (h.kc633 G m (h.l620 G m h67 h69))
    (h.kn633 G m (h.l620 G m h67 h69))

end UC6KernelsW

theorem UC6KernelsW.toInputs (h : UC6KernelsW) : UC6Inputs := by
  have r67 : ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
      (S : Setup4 G), S.InMSigma → TheoremCAt S.M → R6_7 (dataOfSetup4 hS hU S) :=
    fun G _ _ hS hU S hMS hC => PartTwo.r6_7_of_K36_at (dataOfSetup4 hS hU S) h.k36
      (r6_3_dataOfSetup4 hS hU S hC) (h.star36 G hS hU S hMS hC)
  have h67 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_7 (dataOfSetup4 m.hS m.hU m.S) := fun G _ _ m => r67 G m.hS m.hU m.S m.hMS m.hC
  have h69 : ∀ (G : Type) [Group G] [Finite G] (m : Mz614 G),
      R6_9 (dataOfSetup4 m.hS m.hU m.S) := fun G _ _ m =>
    r6_9_of_K47 m.hS m.hU m.S k47_uc6 m.hC (h67 G m)
  exact
    { r67 := r67
      c619 := fun G _ _ m => h.C619 m (h67 G m) (h69 G m)
      c620 := fun G _ _ m => h.C620 m (h67 G m) (h69 G m)
      c624 := fun G _ _ m => h.c624 G m (h67 G m) (h69 G m)
      c629 := fun G _ _ m => h.C629 m (h67 G m) (h69 G m)
      c632 := fun G _ _ m => h.C632 m (h67 G m) (h69 G m)
      c635 := fun G _ _ m => h.C635 m (h67 G m) (h69 G m)
      c636 := fun G _ _ m => h.C636 m (h67 G m) (h69 G m) }

theorem uc_theorem_6_14_four_of_kernelsW (h : UC6KernelsW) :
    Theorem614Four :=
  uc_theorem_6_14_four_of_inputs h.toInputs

end CFSG.LocalAnalysis.UniquenessCase.UC6
