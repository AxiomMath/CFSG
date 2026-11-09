module

public import Certificates.Data.Kernel.LyDce.CoverWalk

public section

namespace CFSG.KC.LyDce

open CFSG.KC CFSG.KC.Loop CFSG.KC.MonsterConv.Perm

@[expose] noncomputable def tri (Nc Nd X : Nat) : Nat × Nat × Nat := (X, net2 Nc X, net2 Nd X)

@[expose] noncomputable def eqNL : List Nat → List Nat → Bool
  | [], [] => true
  | a :: as, b :: bs => andB (Nat.beq a b) (eqNL as bs)
  | _, _ => false

@[expose] noncomputable def walkSTo (Nc Nd P K Tc Td : Nat) (es : List (Nat × Nat × Nat))
    (st : List (Nat × Nat × Nat)) (Xs : List Nat) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun st => eqNL (st.map Prod.fst) Xs)
    (fun e _ ih st =>
      List.rec (motive := fun _ => Bool) false
        (fun top rest _ =>
          strictBN (selG e.2.2 top) fun X =>
            strictBN (net2 Nc X) fun Xc => strictBN (net2 Nd X) fun Xd =>
              andB (lineS P K Tc Td e.1 X Xc Xd) (ih ((X, Xc, Xd) :: popG e.2.2 (top :: rest))))
        (st.drop e.2.1)) es st

@[expose] noncomputable def walkSFromTo (Nc Nd P K Tc Td M₀ : Nat) (es : List (Nat × Nat × Nat))
    (Xs : List Nat) : Bool :=
  strictBN (saltOf M₀) fun X => walkSTo Nc Nd P K Tc Td es [(X, net2 Nc X, net2 Nd X)] Xs

end CFSG.KC.LyDce

end
