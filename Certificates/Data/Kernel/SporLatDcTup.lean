module

public import Certificates.Data.Kernel.SporLatDc
public import Certificates.Data.Kernel.LocalQT.Pipe

public noncomputable section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def tupW (w P : Nat) (t : List Nat) : List Nat := t.map (CFSG.KC.LQT.PW.imgW w P)

@[expose] def otIdxOK (w m : Nat) (Ps : List Nat) (O : OmegaData (List Nat)) : Bool :=
  omOKG (fun l t => tupW w (Ps.getD l 0) t) (List.range m) Ps.length O

@[expose] def tupLbl {Lab : Type} [Inhabited Lab] (Om : OmegaData Lab) (O : OmegaData (List Nat)) :
    OmegaData (List Lab) :=
  ⟨O.lbl.map (fun t => t.map (fun k => Om.lbl[k]!)), O.pn, O.par, O.via⟩

end CFSG.KC.SLDc

end
