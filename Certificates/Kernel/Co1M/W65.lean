module

public import Certificates.Kernel.Co1M.K65
public import Certificates.Kernel.Co1M.Orb98280
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.CoTwoAutGraphLitInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.Co1.Module.InvFam

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.InvFam CFSG.KC.SortTree
  CFSG.KC.Graph65 CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.CoTwoAut
  CFSG.Sporadic.SmallF2.Native

@[expose] noncomputable def w65 : GraphW where
  R := R65
  RT := RT65
  P := P65
  G := G65
  KS := recT ksL65 6 36

theorem c65_beq {a b : Nat} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem inO_eq : inO = fun w => CFSG.KC.Co1M.orbMemK 98280
    (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
  funext fun w => cm_orb_inPts w

theorem labG_eq : labG = labK65 := by
  funext w
  unfold labG Pairs.tyLab labK65
  have e : Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w =
      CFSG.KC.Co1M.orbMemK 98280 (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.S 32) 17 w :=
    cm_orb_inPts w
  rw [e]

theorem w65_prog : progK 24 R65 P65 2 = true := by quickRfl

theorem w65_small : andB (Nat.beq (getL 0 R65 0) CertificateChecks.KernelCo1Cover.R0)
    (andB (Nat.beq (getL 0 R65 1) CertificateChecks.KernelCo1Cover.R1)
    (andB (allN (lenL R65) (fun i => Nat.beq (trK 24 (getL 0 R65 i)) (getL 0 RT65 i)))
    (andB (Nat.beq (lenL G65) 2) (andB (bndK (lenL R65) G65) (andB (fixAllK RT65 G65 [2])
    (andB (Nat.beq (lenL CFSG.Sporadic.Co2Cert.co2G0) 2300)
      (Nat.beq (lenL CFSG.Sporadic.Co2Cert.co2G1) 2300))))))) = true := by quickRfl

theorem ok65 : GraphOK w65 := by
  obtain ⟨a0, r⟩ := andB_true_iff.1 w65_small
  obtain ⟨a1, r⟩ := andB_true_iff.1 r
  obtain ⟨tr, r⟩ := andB_true_iff.1 r
  obtain ⟨lg, r⟩ := andB_true_iff.1 r
  obtain ⟨ix, r⟩ := andB_true_iff.1 r
  obtain ⟨fx, r⟩ := andB_true_iff.1 r
  obtain ⟨l0, l1⟩ := andB_true_iff.1 r
  obtain ⟨d3, d1⟩ := andB_true_iff.1 k65_adj
  exact {
    rA := by
      rw [CertificateChecks.KernelCo1Cover.rowsA_eq, ← c65_beq a0]
      rfl
    rB := by
      rw [CertificateChecks.KernelCo1Cover.rowsB_eq, ← c65_beq a1]
      rfl
    prog := w65_prog
    tr := tr
    lenG := c65_beq lg
    idx := ix
    fix := fx
    len := ⟨c65_beq l0, c65_beq l1⟩
    eqv0 := k65_eqv0
    eqv1 := k65_eqv1
    vert := by
      rw [inO_eq]
      exact k65_vert
    dist := k65_dist
    adj3 := by
      rw [labG_eq]
      exact d3
    adj1 := by
      rw [labG_eq]
      exact InvFam.notB_true d1 }

end CertificateChecks.KernelCo1M

end
