module

public import Certificates.Data.Kernel.S1277KMod

public section

namespace CFSG.KC.S1277Lat

open CFSG.KC.S1277Mod CFSG.KC.Enum

@[expose] noncomputable def allL (l : List ℕ) (f : ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => f a && ih) l

structure Mdl where
  nb : ℕ
  AP : ℕ
  CP : ℕ
  IP : ℕ
  one : ℕ

@[expose] def Mdl.mul (M : Mdl) (x y : ℕ) : ℕ := mulP M.nb M.AP M.CP x y

@[expose] def Mdl.inv (M : Mdl) (x : ℕ) : ℕ := invP M.AP M.IP x

@[expose] def Mdl.conj (M : Mdl) (k x : ℕ) : ℕ := M.mul (M.mul k x) (M.inv k)

@[expose] def treeStep (M : Mdl) (gs : List ℕ) (s t : ℕ) : ℕ :=
  bif s.testBit ((t >>> 12) % 4096) && !s.testBit (t % 4096) && Nat.blt (t % 4096) (M.nb * 64) &&
      Nat.blt (t >>> 24) gs.length &&
      Nat.beq (M.mul ((t >>> 12) % 4096) (gs.getD (t >>> 24) 0)) (t % 4096)
    then s ||| 1 <<< (t % 4096) else 0

@[expose] noncomputable def treeF (M : Mdl) (gs ts : List ℕ) (s : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun s => s) (fun t _ ih s => strictN (treeStep M gs s t) ih)
    ts s

@[expose] def idM (M : Mdl) : ℕ := 1 <<< (M.one * 64)

@[expose] noncomputable def genChk (M : Mdl) (kg kt : List ℕ) : Bool :=
  allL kg (fun k => Nat.blt k (M.nb * 64)) &&
    Nat.beq (treeF M kg kt (idM M)) (2 ^ (M.nb * 64) - 1)

@[expose] noncomputable def nodeChk (M : Mdl) (kg : List ℕ) (m : ℕ) (gs ts : List ℕ) (e : ℕ) :
    Bool :=
  m.testBit (M.one * 64) && Nat.beq (treeF M gs ts (idM M)) m && Nat.beq (ts.length + 1) (2 ^ e) &&
    allL gs (fun g => m.testBit g && allL kg fun k => m.testBit (M.conj k g)) &&
    allL (M.one * 64 :: ts.map (· % 4096)) fun x => allL gs fun g => m.testBit (M.mul x g)

@[expose] noncomputable def nodesChk (M : Mdl) (kg : List ℕ) :
    List ℕ → List (List ℕ) → List (List ℕ) → List ℕ → Bool
  | m :: ms, gs :: gss, ts :: tss, e :: es => nodeChk M kg m gs ts e && nodesChk M kg ms gss tss es
  | [], [], [], [] => true
  | _, _, _, _ => false

@[expose] noncomputable def clsChk1 (M : Mdl) (nm : List ℕ) (c : ℕ) (gs ks ts : List ℕ) : Bool :=
  Nat.blt (c >>> 12) nm.length && Nat.blt (c % 4096) (M.nb * 64) &&
    Nat.beq (treeF M gs ts (idM M)) (nm.getD (c >>> 12) 0) &&
    (nm.getD (c >>> 12) 0).testBit (c % 4096) &&
    Nat.beq gs.length ks.length &&
    allL (List.range gs.length) fun i =>
      Nat.blt (ks.getD i 0) (M.nb * 64) && Nat.blt (gs.getD i 0) (M.nb * 64) &&
        Nat.beq (M.mul (ks.getD i 0) (c % 4096)) (M.mul (gs.getD i 0) (ks.getD i 0))

@[expose] noncomputable def clsChk (M : Mdl) (nm : List ℕ) :
    List ℕ → List (List ℕ) → List (List ℕ) → List (List ℕ) → Bool
  | c :: cs, gs :: gss, ks :: kss, ts :: tss => clsChk1 M nm c gs ks ts && clsChk M nm cs gss kss tss
  | [], [], [], [] => true
  | _, _, _, _ => false

@[expose] def oxStep (M : Mdl) (nm cr : List ℕ) (s t : ℕ) : ℕ :=
  bif Nat.blt (t % 4096) (M.nb * 64) && Nat.ble (s % 4096) (t % 4096) &&
      Nat.blt (t >>> 24) (M.nb * 64) && Nat.blt ((t >>> 12) % 4096) cr.length &&
      Nat.beq (M.mul (t >>> 24) (cr.getD ((t >>> 12) % 4096) 0 % 4096))
        (M.mul (t % 4096) (t >>> 24)) &&
      (nm.getD (cr.getD ((t >>> 12) % 4096) 0 >>> 12) 0).testBit (t % 4096)
    then ((s >>> 12) ||| 1 <<< (t % 4096)) <<< 12 ||| (t % 4096) else 0

@[expose] noncomputable def oxF (M : Mdl) (nm cr ts : List ℕ) (s : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun s => s)
    (fun t _ ih s => strictN (oxStep M nm cr s t) ih) ts s

@[expose] noncomputable def oxChk (M : Mdl) (nm cr ox : List ℕ) (ol : ℕ) : Bool :=
  Nat.beq (oxF M nm cr ox 0 >>> 12) (nm.getD ol 0)

@[expose] noncomputable def join1(M : Mdl) (nm : List ℕ) (ngs : List (List ℕ)) (m c : ℕ) (d : List ℕ) : Bool :=
  bif Nat.beq (nm.getD (c >>> 12) 0 ||| m) m then true else
    match d with
    | [] => false
    | J :: ds =>
      Nat.blt J nm.length && Nat.beq (m ||| nm.getD (c >>> 12) 0 ||| nm.getD J 0) (nm.getD J 0) &&
        Nat.beq ds.length (ngs.getD J []).length &&
        allL (List.range ds.length) fun t =>
          m.testBit (ds.getD t 0 % 4096) && (nm.getD (c >>> 12) 0).testBit (ds.getD t 0 >>> 12) &&
            Nat.beq (M.mul (ds.getD t 0 % 4096) (ds.getD t 0 >>> 12)) ((ngs.getD J []).getD t 0)

@[expose] noncomputable def joinRow(M : Mdl) (nm : List ℕ) (ngs : List (List ℕ)) (m : ℕ) :
    List ℕ → List (List ℕ) → Bool
  | c :: cs, d :: ds => join1 M nm ngs m c d && joinRow M nm ngs m cs ds
  | [], [] => true
  | _, _ => false

@[expose] noncomputable def joinChk (M : Mdl) (nm : List ℕ) (ngs : List (List ℕ)) (cr : List ℕ) :
    List ℕ → List (List (List ℕ)) → Bool
  | m :: ms, r :: rs => joinRow M nm ngs m cr r && joinChk M nm ngs cr ms rs
  | [], [] => true
  | _, _ => false

@[expose] def botChk (M : Mdl) (nm : List ℕ) : Bool := Nat.beq (nm.getD 0 0) (idM M)

@[expose] noncomputable def quotChk (M : Mdl) (nm ne : List ℕ) (ol a b : ℕ) : Bool :=
  Nat.blt ol nm.length && Nat.beq (M.nb * 64) (6 * 2 ^ ne.getD ol 0) &&
    Nat.blt a (M.nb * 64) && Nat.blt b (M.nb * 64) &&
    !(nm.getD ol 0).testBit (M.mul (M.mul (M.mul a b) (M.inv a)) (M.inv b))

end CFSG.KC.S1277Lat

end
