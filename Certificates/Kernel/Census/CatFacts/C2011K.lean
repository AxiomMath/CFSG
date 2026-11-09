
module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallL34RankInputs
public import CFSG.GH74.KGroups.Checks3
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Kernel.Census.CatFacts.C2011KP
public import CFSG.Certificates.Kernel.SporSch.MOCChain
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData
import Mathlib.Tactic.IntervalCases

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelCatFacts

open CFSG.ComponentClassification.CatFactsSmall.L34 CFSG.ComponentClassification.PSL3Four
  CFSG.Certificates.Kernel.PkEnum CFSG.GH74.KGroups

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu
  CertificateChecks.KernelCatFacts.C2011KP in
theorem chainQS11 : ChainK 42 6 [tab g₁, tab g₂, tab g₃] wQS11 (#v[0, 1, 5, 2] : Vector (Fin 42) 4)
    QC11.S QC11.SI QC11.LR QC11.TR QC11.TRI 14 QC11.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, QC11.head, QC11.hl,
    by norm_num, .inl QC11.hs⟩
  have hj' : j < 3 := by simpa using hj
  interval_cases j
  · simp only [List.getD_cons_zero, tab_eq]
    decide +kernel
  · simp only [List.getD_cons_succ, List.getD_cons_zero, tab_eq]
    decide +kernel
  · simp only [List.getD_cons_succ, List.getD_cons_zero, tab_eq]
    decide +kernel

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CertificateChecks.KernelCatFacts.C2011KP in
theorem qs_2011K : QS.check = true ∧ QS.orderCertificate = 20160 := by
  obtain ⟨a1, a2⟩ := chainK_check (by decide) (by decide) chainQS11
  have ho : ordK QC11.LR 4 = 20160 := Nat.eq_of_beq_eq_true (by decide +kernel)
  exact ⟨a1, a2.trans ho⟩

theorem qe_2011K : schP QE = true ∧ orderV QE = 16 := by
  constructor <;> decide +kernel

theorem sq_2011K : sqOneCheck (elemsV QE) = true ∧ indepCheck g₂ g₃ c₁ = true := by
  constructor <;> decide +kernel

end CertificateChecks.KernelCatFacts
