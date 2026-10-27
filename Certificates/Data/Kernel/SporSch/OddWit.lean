module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.SporSch.MathieuCls

public section

namespace CFSG.KS.SporSch.OddWit

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.M11 CFSG.KS.SporSch.MOC

@[expose] noncomputable def cw2 (n w m x c₁ c₂ : Nat) : Nat :=
  pcomp n w m (cw1 n w m x c₁) (pcomp n w m c₂ (pcomp n w m x (pinvS n w m c₂)))

@[expose] noncomputable def powNe (n w e y : Nat) : Bool :=
  !Nat.beq (powK n w (mask w) (pidn n w) y e) (pidn n w)

@[expose] noncomputable def witPK (n w : Nat) (OG : List Nat) (e x : Nat) : Bool :=
  OG.any (fun c => powNe n w e (cw1 n w (mask w) x c)) ||
    OG.any fun c₁ => OG.any fun c₂ => powNe n w e (cw2 n w (mask w) x c₁ c₂)

@[expose] noncomputable def rowsPK (n w : Nat) (rows : List (Nat × Nat × List Nat)) (x : Nat) :
    Bool :=
  strictB (ordC n w (mask w) x) fun o =>
    rows.all fun r => !Nat.beq o r.1 || witPK n w r.2.2 r.2.1 x

@[expose] noncomputable def invCandK (n w : Nat) (rows : List (Nat × Nat × List Nat)) (Ui : Nat)
    (d : ClsD) : Bool :=
  rowsPK n w rows Ui && allN d.c fun k => rowsPK n w rows (pcomp n w (mask w) Ui (d.ST k))

@[expose] noncomputable def powCommK (n w B e X : Nat) : Bool :=
  !Nat.beq (pcomp n w (mask w) X B) (pcomp n w (mask w) B X) ||
    Nat.beq (powK n w (mask w) (pidn n w) X e) (pidn n w)

end CFSG.KS.SporSch.OddWit

end
