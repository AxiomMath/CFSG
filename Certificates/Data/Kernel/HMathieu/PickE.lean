module

public import Certificates.Data.Kernel.HMathieu.PickK
public import Certificates.Data.Kernel.HMathieu.FixTab
public import Certificates.Data.Kernel.HMathieu.Tab
public import CFSG.Quasithin.AppendixH.H15.CocodeTwoOffDefs22

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.ASVolI.AppH CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def stepK (st : List Nat × List Nat) (v : Nat) : List Nat × List Nat :=
  bif Nat.beq (reduceK st.1 v) 0 then st else (insK (reduceK st.1 v) st.1, v :: st.2)

@[expose] noncomputable def pickEFrom (n : Nat) (vs : List Nat) (st : List Nat × List Nat) :
    List Nat × List Nat :=
  List.rec (motive := fun _ => List Nat × List Nat → List Nat × List Nat) (fun st => st)
    (fun v _ ih st => bif Nat.beq st.1.length n then st else ih (stepK st v)) vs st

@[expose] noncomputable def pickE (n : Nat) (vs : List Nat) : List Nat × List Nat :=
  pickEFrom n vs ([], [])

@[expose] def ladderB : Nat → List Nat → Bool
  | 0, [] => true
  | n + 1, b :: bs => Nat.ble (2 ^ n) b && Nat.blt b (2 ^ (n + 1)) && ladderB n bs
  | _, _ => false

@[expose] noncomputable def testE (n r : Nat) (vs : List Nat) : Bool :=
  (!(Nat.beq (pickE n vs).1.length n) || ladderB n (pickE n vs).1) && indepK r vs (pickE n vs).2

@[expose] noncomputable def pairCandsL (Mc F : List (List Nat)) (S' : List Nat) : List Nat :=
  S'.flatMap fun s => (S'.filter (· != s)).flatMap fun t =>
    (F.getD s []).filter fun x => actK (Mc.getD t []) x == x

@[expose] noncomputable def pairCandsT (Mc F : List (List Nat)) (m : Nat) (S : List Nat) :
    List Nat :=
  pairCandsL Mc F (S.filter (· != m))

@[expose] noncomputable def pred22E (r4 : Nat) (Mc F : List (List Nat)) (m : Nat) (L S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || (decide (L.length ≤ 5) &&
    (!decide (10 - Nat.log 2 st.2.length ≤ L.length + 1) || o2OK o2Masks22 st.2) &&
    (L.length != 1 || decide (3 ≤ 10 - Nat.log 2 st.2.length)) &&
    (L.length != 4 || testE 10 r4 (xiCandsT F m S)) &&
    (L.length != 5 || (testE 10 10 (xiCandsT F m S) && testE 10 10 (pairCandsT Mc F m S))))

@[expose] noncomputable def predOffK (P L _S : List Nat) (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || (decide (L.length ≤ 5) &&
    (!decide (10 - Nat.log 2 st.2.length ≤ L.length + 1) ||
      (L.length == 4 && L.all fun a => offPts22.all fun i => pg 5 (mask 5) (P.getD a 0) i == i)))

@[expose] def pred23K (c : Nat) (L _S : List Nat) (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || (decide (L.length ≤ 4) &&
    (!decide (11 - Nat.log 2 st.2.length ≤ L.length + 1) || o2OK o2Masks23 st.2) &&
    (L.length != 1 || decide (11 - Nat.log 2 st.2.length = c)))

end CFSG.KC.HMathieu

end
