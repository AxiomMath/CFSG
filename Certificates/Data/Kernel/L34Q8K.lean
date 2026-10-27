module

public import Certificates.Data.Kernel.BfsPin
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.LocalCompUnpack
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.L34Q8Data
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KD.L34Q8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.PSL3Four.Native CFSG.EvenSporadicStandard.L34Q8

@[expose] noncomputable def P1 : Nat := packA 6 g₁T.toList
@[expose] noncomputable def P2 : Nat := packA 6 g₂T.toList
@[expose] noncomputable def P3 : Nat := packA 6 g₃T.toList
@[expose] noncomputable def P5 : Nat := packA 6 g₅T.toList
@[expose] noncomputable def P6 : Nat := packA 6 g₆T.toList

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 42 6 (mask 6) p q

@[expose] noncomputable def pi (p : Nat) : Nat := pinvS 42 6 (mask 6) p

@[expose] noncomputable def LQ (j : Nat) : Nat := [P1, P2, P3, pi P1, pi P2, pi P3].getD j 0

@[expose] noncomputable def wK (wd : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 42 6) (fun j _ acc => pcomp 42 6 (mask 6) (LQ j) acc) wd

@[expose] noncomputable def bindQ8 : Bool :=
  szOK 42 6 && bindArrK g₁T 42 6 P1 && bindArrK g₂T 42 6 P2 && bindArrK g₃T 42 6 P3 &&
    bindArrK g₅T 42 6 P5 && bindArrK g₆T 42 6 P6 &&
    permOK 42 6 (mask 6) (42 * 6) P1 (pi P1) && permOK 42 6 (mask 6) (42 * 6) P2 (pi P2) &&
    permOK 42 6 (mask 6) (42 * 6) P3 (pi P3) && permOK 42 6 (mask 6) (42 * 6) P5 (pi P5) &&
    permOK 42 6 (mask 6) (42 * 6) P6 (pi P6)

@[expose] noncomputable def q8K : Bool :=
  Nat.beq (pc (LQ 3) (LQ 0)) (pidn 42 6) && Nat.beq (pc (LQ 4) (LQ 1)) (pidn 42 6) &&
    Nat.beq (pc (LQ 5) (LQ 2)) (pidn 42 6) &&
  (Nat.beq (pc (wK wX1) (wK wX1)) (pc (pc (pc P1 P1) P2) P1) &&
    Nat.beq (pc (wK wY1) (wK wY1)) (pc (pc (pc P1 P1) P2) P1) &&
    !Nat.beq (pc (pc (pc P1 P1) P2) P1) (pidn 42 6) &&
    Nat.beq (pc (pc (wK wX1) (wK wY1)) (wK wX1)) (wK wY1)) &&
  (Nat.beq (pc (wK wX4) (wK wX4)) (pc (wK wY4) (wK wY4)) &&
    !Nat.beq (pc (wK wX4) (wK wX4)) (pidn 42 6) &&
    Nat.beq (pc (pc (wK wX4) (wK wY4)) (wK wX4)) (wK wY4) &&
    Nat.beq (pc (wK wX4) (pc P5 P6)) (pc (pc P5 P6) (wK wX4)) &&
    Nat.beq (pc (wK wY4) (pc P5 P6)) (pc (pc P5 P6) (wK wY4)))

end CFSG.KD.L34Q8

end
