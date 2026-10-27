module

public import Certificates.Data.Kernel.Co2Smith.Rows

public section

namespace CFSG.KC.Co2Smith

open CFSG.KC.Co2InvS

@[expose] noncomputable def tabK (R i j : Nat) : Bool := Nat.testBit R (15 * i + j)

@[expose] noncomputable def pathK (R C a b c d e : Nat) : Bool :=
  tabK R a b && tabK R b c && tabK R c d && tabK R d e && tabK C a c && tabK C a d && tabK C a e &&
    tabK C b d && tabK C b e && tabK C c e

@[expose] noncomputable def coxLoopK (R C : Nat) (cox : List (List Nat × List Nat)) : Bool :=
  (List.range 15).all fun a => (List.range 15).all fun b => (List.range 15).all fun c =>
    (List.range 15).all fun d => (List.range 15).all fun e =>
      !pathK R C a b c d e || cox.any fun p => p.1 == [a, b, c, d, e]

@[expose] noncomputable def conjPathK (T : Nat → Nat) (G : Nat) (p : List Nat) : Bool :=
  p.length == 5 && (List.range 5).all fun i =>
    decide (p[i]! < 15) && eqK (mulV G (T i)) (mulV (T p[i]!) G)

end CFSG.KC.Co2Smith
