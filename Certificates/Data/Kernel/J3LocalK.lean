module

public import Certificates.Data.Kernel.OpsMcertN
public import CFSG.RankThree.Asc83Table.J3Defs

public section

namespace CFSG.KC.J3Loc

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Loop CFSG.KLie.CT CFSG.KC.M1F2

@[expose] noncomputable def lanesT (P : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => P lo)
    (fun _ ih lo len => nIf(Nat.ble len 1, P lo,
      Nat.lor (ih lo (Nat.div len 2))
        (Nat.shiftLeft (ih (Nat.add lo (Nat.div len 2)) (Nat.sub len (Nat.div len 2)))
          (Nat.mul 128 (Nat.div len 2))))) f

@[expose] noncomputable def lanesP (P : Nat → Nat) (N : Nat) : Nat := lanesT P 16 0 N

@[expose] noncomputable def onesL (N : Nat) : Nat :=
  Nat.div (Nat.sub (pw2 (Nat.mul 128 N)) 1) (Nat.sub (pw2 128) 1)

@[expose] noncomputable def colAllR (T L E : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc =>
    Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight L j) E) (fget T j 80)))

@[expose] noncomputable def movedL (T L E : Nat) : Nat :=
  Nat.land (Nat.shiftRight (Nat.add (Nat.xor (colAllR T L E 80) L) (Nat.mul E (maskN 80))) 80) E

@[expose] noncomputable def xsMask (xs : List Nat) : Nat :=
  xs.foldl (fun acc i => Nat.lor acc (pw2 (Nat.mul 128 i))) 0

@[expose] noncomputable def tcol (X j : Nat) : Nat :=
  orN 80 fun i => nIf(bit X (Nat.add (Nat.mul 80 i) j), pw2 i, 0)

@[expose] noncomputable def tF (X : Nat) : Nat :=
  orN 80 fun j => Nat.shiftLeft (tcol X j) (Nat.mul 80 j)

@[expose] noncomputable def colK (X v : Nat) : Nat := vmF 80 (tF X) v

@[expose] def rangeK (J : J3Cert) : Bool :=
  Nat.blt J.rb.1 J.nregs && Nat.blt J.rb.2.1 J.nregs && Nat.blt J.rb.2.2 J.nregs &&
    Nat.blt J.rh.1 J.nregs && Nat.blt J.rh.2.1 J.nregs &&
    J.ss.all (fun s => Nat.blt s.1 J.nregs) && J.cs.all (fun c => Nat.blt c J.nregs)

@[expose] noncomputable def extraK (J : J3Cert) (root L E : Nat) (R : List Nat) : Bool :=
  let O := opsF2K 80
  let bw := fun k => evalWN O R (basisW J.rb k)
  let C := J.cs.map (getN R)
  let C2 := C.map fun X => powN O 3 X 2
  rangeK J &&
    (List.range 26).all (fun k =>
      Nat.beq (Nat.lor (movedL (tF (bw (k + 1))) L E) (xsMask J.xs)) E) &&
    Nat.beq (colK (getN R J.rb.1) root) root &&
    (List.range 24).all (fun k => O.vne (colK (bw (k + 3)) root) root) &&
    (List.range 26).all (fun k => !O.eq (bw (k + 1)) O.one) &&
    J.ss.all (fun s => Nat.beq (colK (getN R s.1) root) root) &&
    C.zipIdx.all (fun p => (C.zip C2).zipIdx.all fun q =>
      Nat.beq p.2 q.2 || (!O.eq p.1 q.1.1 && !O.eq p.1 q.1.2)) &&
    (List.range 27).all (fun k => (List.range 8).all fun m =>
      !O.eq (powN O 4 (evalWN O R (basisW J.rb k ++ hW J.rh (m + 1))) 3) O.one) &&
    Nat.beq J.ss.length J.cs.length

@[expose] noncomputable def fullK (A B : Nat) (P : Nat → Nat) (N : Nat) (J : J3Cert) : Bool :=
  strictB (lanesP P N) fun L => strictB (onesL N) fun E =>
    regsN (opsF2K 80) A B J.nregs J.prog fun R =>
      certN (opsF2K 80) R J.mcert && extraK J (P 0) L E R

end CFSG.KC.J3Loc

end
