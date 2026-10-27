module

public import Certificates.Data.Kernel.WrPack
public import Certificates.Data.Kernel.AE117Adj
public import Certificates.Data.WsubMembersE64

public section

namespace CFSG.KD.WsubE64

open CFSG.KC.WrTwin CFSG.KC.WrPack CFSG.ClassicalInvolution.Q3.AE Certificates.Kernel.AE117Adj

abbrev Lab := (Fin 6 × Fin 6 × Fin 6 × Fin 6) × Bool

@[expose] def labels : List Lab := (quads 6).flatMap fun q => [(q, true), (q, false)]

@[expose] def encI (L : List (Wr 6)) : List (Nat × Nat) := L.map fun x => (enc x, enc x⁻¹)

@[expose] def LM (_ : Unit := ()) : List (Lab × List (Nat × Nat)) :=
  labels.map fun l => (l, encI (memQ l.1 l.2))

@[expose] def memP (x : Nat) (B : List Nat) : Bool := B.any (Nat.beq x)

@[expose] def subP (X Y : List (Nat × Nat)) : Bool := X.all fun x => (Y.map (·.1)).any (Nat.beq x.1)

@[expose] def nodupP : List Nat → Bool
  | [] => true
  | x :: l => !memP x l && nodupP l

@[expose] def e64P (e : Nat) (A : List Nat) : Bool :=
  nodupP A && A.all (fun a => A.all fun b => memP (pm 6 a b) A && Nat.beq (pm 6 a b) (pm 6 b a)) &&
    A.all fun a => Nat.beq (pm 6 a a) e

@[expose] def conjP (s si : Nat) (X Y : List (Nat × Nat)) : Bool :=
  X.all fun x => (Y.map (·.1)).any (Nat.beq (pm 6 (pm 6 s x.1) si))

@[expose] def subL (I : List Nat) (X : List (Nat × Nat)) : Bool :=
  I.all fun z => (X.map (·.1)).any (Nat.beq z)

@[expose] def permP (M : List (Lab × List (Nat × Nat))) (s si : Nat) : Bool :=
  M.all fun Y => (fun I => M.any fun X => subL I X.2 && conjP s si X.2 Y.2)
    (Y.2.map fun y => pm 6 (pm 6 si y.1) s)

@[expose] def distinctP (M : List (Lab × List (Nat × Nat))) : Bool :=
  M.all fun X => M.all fun Y => !subP X.2 Y.2 || decide (X.1 = Y.1)

@[expose] def normP (A : List Nat) (X : List (Nat × Nat)) : Bool :=
  X.all fun x => A.all fun a => memP (pm 6 (pm 6 x.1 a) x.2) A && memP (pm 6 (pm 6 x.2 a) x.1) A

@[expose] def countP (A : List Nat) (M : List (Lab × List (Nat × Nat))) (six : List Lab) : Bool :=
  M.all fun X => normP A X.2 == decide (X.1 ∈ six)

@[expose] def six : List Lab :=
  [((0, 1, 2, 5), true), ((0, 1, 2, 5), false), ((0, 1, 3, 4), true), ((0, 1, 3, 4), false),
    ((2, 3, 4, 5), true), ((2, 3, 4, 5), false)]

@[expose] def conjs (_ : Unit := ()) : List (Wr 6) :=
  VevenW 6 ++ (List.finRange 5).map fun i => ⟨0, Equiv.swap i.castSucc i.succ⟩

@[expose] def wsubK (_ : Unit := ()) : Bool :=
  let A := (Certificates.WsubMembersE64.a0List ()).map enc
  let M := LM ()
  e64P (enc (1 : Wr 6)) A && (conjs ()).all (fun s => permP M (enc s) (enc s⁻¹)) && distinctP M &&
    countP A M six

end CFSG.KD.WsubE64
