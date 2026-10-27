module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.LocalAnalysis.SectionRank.QTK.CoverBRealCheck
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.KC.OpsReal

open CFSG.SectionRank.Native CFSG.SectionRank.QTK.CoverB CFSG.KC.OpsK CFSG.KC.OpsMN
  CFSG.KC.OpsV4

variable {V : Type}

@[expose] noncomputable def realG (O : Ops Nat V) (pw : Nat → Nat → Nat) (D : RealData)
    (g : Nat → Nat) : Bool :=
  O.eq (O.mul (g D.t₁) (g D.t₁)) O.one && O.eq (O.mul (g D.t₂) (g D.t₂)) O.one &&
    O.commOK (g D.t₁) (g D.t₂) &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) (g D.t₁)) (O.unit k)) &&
    conjG O (g D.x) (g D.t₁) (g D.t₁) (g D.t₂) (O.mul (g D.t₁) (g D.t₂)) &&
    conjG O (g D.x) (g D.t₂) (g D.t₁) (g D.t₂) (O.mul (g D.t₁) (g D.t₂)) &&
    O.eq (O.mul (O.mul (g D.x) (g D.x)) (g D.x)) O.one &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) (g D.x)) (O.unit k)) &&
    decide (0 < D.dord) && O.eq (pw (g D.d) D.dord) O.one &&
    O.eq (O.mul (g D.d) (g D.x)) (O.mul (O.mul (g D.x) (g D.x)) (g D.d))

@[expose] noncomputable def realN (O : Ops Nat V) (A B : Nat) (D : RealData) : Bool :=
  D.base.prog.all (Op.lt D.base.nregs) &&
    [D.t₁, D.t₂, D.x, D.d].all (decide <| · < D.base.nregs) &&
    regsN O A B D.base.nregs D.base.prog fun R =>
      realG O (fun X e => powN O (e + 1) X e) D (getN R)

end CFSG.KC.OpsReal

end
