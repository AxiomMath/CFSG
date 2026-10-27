module

public import Certificates.Data.Kernel.LyDce.Cover

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def salt0 : Nat := Nat.mod (Nat.pow 3 82713) (Nat.shiftLeft 1 131072)

@[expose] noncomputable def saltOf (M : Nat) : Nat := Nat.lor (Nat.shiftLeft M 131072) salt0

@[expose] noncomputable def net2 (N X : Nat) : Nat := netsApply 17 131072 (repU 131072 2) [N] X

@[expose] noncomputable def keyS (P X : Nat) : Nat := Nat.mod (Nat.shiftRight X 131072) P

@[expose] noncomputable def lineS (P K Tc Td l X Xc Xd : Nat) : Bool :=
  andB (Nat.beq (keyS P X) (fldW 48 K l))
    (strictBN (fldW 16 Tc l) fun a => strictBN (fldW 16 Td l) fun b =>
      andB (andB (Nat.blt a nL) (Nat.blt b nL))
        (andB (Nat.beq (keyS P Xc) (fldW 48 K a)) (Nat.beq (keyS P Xd) (fldW 48 K b))))

@[expose] noncomputable def walkS (Nc Nd P K Tc Td : Nat) (es : List (Nat × Nat × Nat))
    (st : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool) (fun _ => true)
    (fun e _ ih st =>
      List.rec (motive := fun _ => Bool) false
        (fun top rest _ =>
          strictBN (selG e.2.2 top) fun X =>
            strictBN (net2 Nc X) fun Xc => strictBN (net2 Nd X) fun Xd =>
              andB (lineS P K Tc Td e.1 X Xc Xd) (ih ((X, Xc, Xd) :: popG e.2.2 (top :: rest))))
        (st.drop e.2.1)) es st

@[expose] noncomputable def walkSFrom (Nc Nd P K Tc Td M₀ : Nat) (es : List (Nat × Nat × Nat)) :
    Bool :=
  strictBN (saltOf M₀) fun X => walkS Nc Nd P K Tc Td es [(X, net2 Nc X, net2 Nd X)]

end CFSG.KC.LyDce

end
