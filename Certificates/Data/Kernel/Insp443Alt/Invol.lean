module

public import Certificates.Data.Kernel.PermCent.AllPermsC
public import Certificates.Data.AltInsp443

public section

namespace CFSG.Certificates.Kernel.Insp443Alt

open CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.PkEnum CFSG.KC.Enum
  CFSG.SectionRank.QTK.Insp443.Alt CFSG.Quasithin.KGC31

@[expose] noncomputable def invP : (m : Nat) → Small m → List (CV m × Bool)
  | 0, _ => [(1, false)]
  | m + 1, hs =>
    have : Small m := small_pred hs
    forcePL (invP m this) fun L => (List.finRange (m + 1)).flatMap fun p =>
      (L.filter fun x => Nat.beq p.1 0 || Nat.beq (img m x.1.1 (p.1 - 1)) (p.1 - 1)).map
        fun x => (liftC p x.1, xor (p.1 != 0) x.2)

@[expose] def forceBL {β : Sort _} : List Bool → (List Bool → β) → β
  | [], k => k []
  | b :: l, k => forceB b fun b => forceBL l fun l => k (b :: l)

variable {n : Nat} [Small n]

@[expose] noncomputable def powL (c : CV n) (p : Nat) : List (CV n) :=
  (List.range (p + 1)).map fun i => c ^ i

@[expose] noncomputable def conjL (P : List (CV n)) (p : Nat) (s : CV n) : List (CV n) :=
  (List.range p).map fun i => P.getD i 1 * s * P.getD (p - i) 1

@[expose] noncomputable def commL (s : CV n) (Q : List (CV n)) : List Bool :=
  Q.map fun q => eq22C s q q s

@[expose] noncomputable def badB (p : Nat) (s : CV n) (Q : List (CV n)) (B : List Bool) (k : Nat) :
    Bool :=
  !Nat.beq (Q.getD k 1).1 s.1 && (List.range p).all fun j => B.getD (k * j % p) false

@[expose] def e8 : List (Fin 3 → ZMod 2) :=
  [![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0], ![1, 1, 1]]

@[expose] noncomputable def regB (s : CV n) (Q : List (CV n)) (k : Nat) : Bool :=
  decide ((e8.map fun c => img n (eElt ![s, Q.getD k 1, Q.getD (k * 2 % 7) 1] c).1 0).Nodup)

@[expose] noncomputable def okS (P5 P7 : List (CV n)) (s : CV n) : Bool :=
  forceCL (conjL P5 5 s) fun Q5 => forceCL (conjL P7 7 s) fun Q7 =>
    forceBL (commL s Q5) fun B5 => forceBL (commL s Q7) fun B7 =>
      ((List.range 5).all fun k => !badB 5 s Q5 B5 k) &&
        (List.range 7).all fun k => !badB 7 s Q7 B7 k || regB s Q7 k

@[expose] noncomputable def chkI (n : Nat) [Small n] [NeZero n] : Bool :=
  forceCL (powL (cOf (cyc5 n)) 5) fun P5 => forceCL (powL (cOf (cyc7 n)) 7) fun P7 =>
    (invP n inferInstance).all fun x => x.2 || forceC x.1 fun s => okS P5 P7 s

end CFSG.Certificates.Kernel.Insp443Alt

end
