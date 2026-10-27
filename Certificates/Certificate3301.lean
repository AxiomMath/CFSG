module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPresData
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPresData
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.U6Pres
public import CFSG.Certificates.CosetTableColumns
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelData
public import Mathlib
meta import CFSG.Certificates.CosetTableColumns
meta import CFSG.Certificates.CosetTableShort
meta import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParModelData
meta import Mathlib

public section

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.CosetTable CFSG.KC.MiscCoset

namespace CertificateChecks.Batch3301

open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.CosetTable CFSG.KC.MiscCoset

set_option maxRecDepth 100000

theorem uWS_eq : uWS.map encW = CFSG.KBRoute.U6Pres.rels := by decide +kernel

theorem uPres_card_0 : Finite (PG 5 uWS) ∧ Nat.card (PG 5 uWS) ≤ 51840 := by
  have h1 := CertificateChecks.KernelMiscCoset.U6Pres.t1
  unfold CFSG.KBRoute.U6Pres.T1.ok at h1
  exact card_le_of_tableOk uWS uWS_eq h1 (by decide) CFSG.KBRoute.U6Pres.top rfl

private theorem uRelCheck_eq_true_1 : uRelCheck = true := by
  decide +kernel

private theorem uGenCheck_eq_true_2 : uGenCheck = true := by
  decide +kernel

end CertificateChecks.Batch3301

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.UnitarySix.YamadaPar in
theorem certificate3301 : (Finite (CFSG.CosetTable.PG 5 uWS) ∧ Nat.card (CFSG.CosetTable.PG 5 uWS) ≤ 51840) ∧
    (uRelCheck = true) ∧ (uGenCheck = true) :=
  ⟨CertificateChecks.Batch3301.uPres_card_0, CertificateChecks.Batch3301.uRelCheck_eq_true_1, CertificateChecks.Batch3301.uGenCheck_eq_true_2⟩

end Certificates
