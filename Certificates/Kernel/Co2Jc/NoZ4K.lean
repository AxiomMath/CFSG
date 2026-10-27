module

public import Certificates.Kernel.Co2Jc.NoZ4Defs
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.Enum CFSG.Sporadic.Co2Jc.Data CFSG.Sporadic.Co2Jc.Native.NoZ4

@[expose] def toM (X : Nat) : M2 := CFSG.Sporadic.SmallF2.rowsMatrix 10 (CFSG.KC.Co1F2.unpackR 10 X)

@[expose] def toM4 (A : List (List Nat)) : M4 := Matrix.of fun i j => (eL A i.val j.val : ZMod 4)

theorem chain_ok : (List.range 2).all (fun t => (wOf t).all (· < 3) &&
    Nat.beq (PR t 0) (CFSG.KC.M1F2.idF 10) && Nat.beq (SF t (wOf t).length) (CFSG.KC.M1F2.idF 10) &&
    (List.range (wOf t).length).all fun i =>
      Nat.beq (PR t (i + 1)) (CFSG.KC.M1F2.mulF 10 (PR t i) (GK (wOf t)[i]!)) &&
      Nat.beq (SF t i) (CFSG.KC.M1F2.mulF 10 (GK (wOf t)[i]!) (SF t (i + 1)))) = true := by
  decide +kernel

theorem coeff_ok : (List.range 3).all (fun k => Nat.beq (coeffK k) 0) = true := by
  decide +kernel

theorem gen_ok : ((List.range 3).all fun k => (List.finRange 10).all fun j =>
    (List.finRange 10).all fun i => decide (G2 k j i = toM (GK k) j i)) = true := by
  decide +kernel

theorem csel_ok : (noZ4Rels.all fun r => (List.finRange 10).all fun a =>
    (List.finRange 10).all fun b =>
      decide ((if (r, a.val, b.val) ∈ noZ4Sel then 1 else 0 : ZMod 2) = toM (CS r) a b)) = true := by
  decide +kernel

theorem g4_ok : ((List.range 3).all fun k => (List.finRange 10).all fun j =>
    (List.finRange 10).all fun i => decide (G4 k j i = toM4 (G4L k) j i)) = true := by
  decide +kernel

theorem id4_ok : ((List.finRange 10).all fun i => (List.finRange 10).all fun j =>
    decide ((1 : M4) i j = toM4 id4 i j)) = true := by
  decide +kernel

theorem q_ok : (P4 (wOf 0) == QL 0 && P4 (wOf 1) == QL 1) = true := by
  decide +kernel

@[expose] noncomputable def eokK : Bool :=
  noZ4Sel.all (fun p =>
    p.1 ∈ noZ4Rels && p.2.1 < 10 && p.2.2 < 10 &&
      qE p.1 p.2.1 p.2.2 = (idEntry p.2.1 p.2.2 : ZMod 4) +
        2 * (if qE p.1 p.2.1 p.2.2 = (idEntry p.2.1 p.2.2 : ZMod 4) then 0 else 1)) &&
    (noZ4Rels.map fun r =>
      Finset.univ.sum fun a : Fin 10 =>
        Finset.univ.sum fun b : Fin 10 =>
          (Csel r).toMat a b * ((((if qE r a.val b.val = (idEntry a.val b.val : ZMod 4) then 0
            else 1 : ZMod 4)).val : ℕ) : ZMod 2)).sum == 1

theorem eok_ok : eokK = true := by decide +kernel

end CertificateChecks.KernelCo2Jc
