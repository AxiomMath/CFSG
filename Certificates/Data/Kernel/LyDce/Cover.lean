module

public import Certificates.Data.Kernel.LyDce.Chain

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm CFSG.KC.LyBase CFSG.KC.LyReplay

@[expose] def nL : Nat := 15400

@[expose] noncomputable def strictBN (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def fldW (w T l : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul w l)) (ones w)

@[expose] noncomputable def keyOf (P M : Nat) : Nat := Nat.mod (Nat.land M (ones 66825)) P

@[expose] noncomputable def maskOf (O : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun a _ ih => strictN ih fun x => Nat.lor x (Nat.shiftLeft 1 a)) O

@[expose] noncomputable def netP (N X : Nat) : Nat := netsApply 17 131072 1 [N] X

@[expose] noncomputable def fixOK (NS : Nat → Nat) (M₀ : Nat) (G : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih => andB (Nat.beq (netsApply 17 131072 1 ((jwOf g).map NS) M₀) M₀) ih) G

@[expose] noncomputable def lineOK (P K Tc Td l M Mc Md : Nat) : Bool :=
  andB (Nat.beq (keyOf P M) (fldW 48 K l))
    (strictBN (fldW 16 Tc l) fun a => strictBN (fldW 16 Td l) fun b =>
      andB (andB (Nat.blt a nL) (Nat.blt b nL))
        (andB (Nat.beq (keyOf P Mc) (fldW 48 K a)) (Nat.beq (keyOf P Md) (fldW 48 K b))))

@[expose] noncomputable def selG (g : Nat) (t : Nat × Nat × Nat) : Nat :=
  nIf(Nat.beq g 0, t.2.1, nIf(Nat.beq g 1, t.2.2, t.1))

@[expose] noncomputable def popG (g : Nat) (st : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) :=
  Bool.rec (motive := fun _ => List (Nat × Nat × Nat)) st st.tail (Nat.beq g 2)

@[expose] noncomputable def walkOK (Nc Nd P K Tc Td : Nat) (es : List (Nat × Nat × Nat))
    (st : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool) (fun _ => true)
    (fun e _ ih st =>
      List.rec (motive := fun _ => Bool) false
        (fun top rest _ =>
          strictBN (selG e.2.2 top) fun M =>
            strictBN (netP Nc M) fun Mc => strictBN (netP Nd M) fun Md =>
              andB (lineOK P K Tc Td e.1 M Mc Md) (ih ((M, Mc, Md) :: popG e.2.2 (top :: rest))))
        (st.drop e.2.1)) es st

@[expose] noncomputable def walkFrom (Nc Nd P K Tc Td M₀ : Nat) (es : List (Nat × Nat × Nat)) :
    Bool :=
  walkOK Nc Nd P K Tc Td es [(M₀, netP Nc M₀, netP Nd M₀)]

@[expose] noncomputable def labMask (ws : List (List (Nat × Nat × Nat))) (R : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun R => R)
    (fun es _ ih R => ih (List.rec (motive := fun _ => Nat → Nat) (fun R => R)
      (fun e _ ih' R => strictN (Nat.lor R (Nat.shiftLeft 1 e.1)) ih') es R)) ws R

@[expose] noncomputable def covOK (ws : List (List (Nat × Nat × Nat))) : Bool :=
  Nat.beq (Nat.land (labMask ws 0) (ones nL)) (ones nL)

@[expose] noncomputable def incOK (K : Nat) : Bool :=
  allBelow (Nat.sub nL 1) 241 fun l => Nat.blt (fldW 48 K l) (fldW 48 K (Nat.succ l))

@[expose] noncomputable def mvX (Tc Td x l : Nat) : Nat :=
  nIf(Nat.blt x 2, fldW 16 Tc l,
    nIf(Nat.beq x 2, strictN (fldW 16 Td l) fun m => fldW 16 Td m, fldW 16 Td l))

@[expose] noncomputable def mvC (Tc Td : Nat) (cs : List Nat) (l : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) l (fun x _ ih => strictN ih fun m => mvX Tc Td x m) cs

@[expose] noncomputable def tabOK (Tc Td Ta Tb Te : Nat) : Bool :=
  allBelow nL 241 fun l =>
    andB (Nat.beq (fldW 16 Ta l) (mvC Tc Td (jC 3) l))
      (andB (Nat.beq (fldW 16 Tb l) (mvC Tc Td (jC 4) l))
        (Nat.beq (fldW 16 Te l) (mvC Tc Td (jC 5) l)))

structure Tabs where
  c : Nat
  d : Nat
  a : Nat
  b : Nat
  e : Nat

@[expose] noncomputable def mvL (T : Tabs) (j l : Nat) : Nat :=
  nIf(Nat.beq j 0, fldW 16 T.c l,
    nIf(Nat.beq j 1, strictN (fldW 16 T.d l) fun m => fldW 16 T.d m,
      nIf(Nat.beq j 2, fldW 16 T.d l,
        nIf(Nat.beq j 3, fldW 16 T.a l, nIf(Nat.beq j 4, fldW 16 T.b l, fldW 16 T.e l)))))

@[expose] noncomputable def mvJ (T : Tabs) (w : List Nat) (l : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) l (fun j _ ih => strictN ih fun m => mvL T j m) w

@[expose] noncomputable def frEntOK (T : Tabs) (nt : List (Nat × Nat)) (rep : List (List Nat))
    (G : List (List Nat)) (node root R : Nat) (e : Nat × Nat × Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (Nat.beq (Nat.land (Nat.shiftRight R e.2.1) 1) 1)
      (Nat.beq e.1 (mvJ T (jwOf (G.getD (Nat.sub e.2.2 1) [])) e.2.1)))
    (andB (Nat.beq (nt.getD e.2.1 (0, 0)).1 node)
      (Nat.beq e.1 (mvJ T (jwOf (rep.getD e.2.1 [])) root)))
    (Nat.beq e.2.2 0)

@[expose] noncomputable def frOK (T : Tabs) (nt : List (Nat × Nat)) (rep : List (List Nat))
    (G : List (List Nat)) (node root : Nat) (es : List (Nat × Nat × Nat)) (R : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun R => Nat.beq (Nat.land R (ones nL)) (ones nL))
    (fun e _ ih R => andB (frEntOK T nt rep G node root R e)
      (strictBN (Nat.lor R (Nat.shiftLeft 1 e.1)) ih)) es R

end CFSG.KC.LyDce

end
