module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.CF67K

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.MOC

@[expose] noncomputable def inGenK (n w r A B C : Nat) : Bool :=
  !allN r fun i => allN r fun j => !Nat.beq C
    (pcomp n w (mask w) (powK n w (mask w) (pidn n w) A i) (powK n w (mask w) (pidn n w) B j))

@[expose] noncomputable def isPairK (n w r A B : Nat) : Bool :=
  Nat.beq (powK n w (mask w) (pidn n w) A r) (pidn n w) &&
    Nat.beq (powK n w (mask w) (pidn n w) B r) (pidn n w) && !Nat.beq A (pidn n w) &&
    allN r (fun i => !Nat.beq B (powK n w (mask w) (pidn n w) A i)) &&
    Nat.beq (pcomp n w (mask w) A B) (pcomp n w (mask w) B A)

@[expose] noncomputable def sylK (n w r m c : Nat) (P E₁ E₂ : Nat → Nat) : Bool :=
  allN m (fun i => allN i fun j => !Nat.beq (P i) (P j)) &&
    !allN m (fun i => !Nat.beq (pidn n w) (P i)) &&
    allN m (fun i => !allN m fun j => !Nat.beq (pcomp n w (mask w) (P i) (P j)) (pidn n w)) &&
    allN m (fun i => allN m fun j => strictB (pcomp n w (mask w) (P i) (P j)) fun Z =>
      !allN m fun k => !Nat.beq Z (P k)) &&
    allN m (fun i => allN m fun j => !isPairK n w r (P i) (P j) ||
      !allN c fun e => !(inGenK n w r (P i) (P j) (E₁ e) && inGenK n w r (P i) (P j) (E₂ e)))

end CFSG.KS.SporSch.CF67K

end
