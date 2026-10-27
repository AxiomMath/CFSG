module

public import Certificates.Data.Kernel.SmithEKE
public import Certificates.Data.Kernel.SmithEKCd
public import Certificates.Data.Kernel.SmithEKR

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def nthK {α : Type} (d : α) (L : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun h _ ih n => Nat.rec (motive := fun _ => α) h (fun m _ => ih m) n) L

@[expose] noncomputable def allK (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => f g && ih) L

@[expose] noncomputable def apR (A : List Nat) (x : Nat) : Nat := c8ap A x

@[expose] noncomputable def parQ (x : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k acc => xor acc (bitK x (Nat.mul 2 k))) 10

@[expose] noncomputable def fRK (u v : Nat) : Bool :=
  parQ (Nat.xor (Nat.land u (Nat.shiftRight v 1)) (Nat.land (Nat.shiftRight u 1) v))

@[expose] noncomputable def al16 (n : Nat) : Bool := atLeastK 16 n

@[expose] noncomputable def projR (V U : List Nat) (w : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun v _ ih U => List.rec (motive := fun _ => Nat) 0
      (fun u U' _ => Nat.xor (bif fRK w u then v else 0) (ih U')) U) V U

@[expose] noncomputable def gV (g : Nat) : Nat := g % 1048576

@[expose] noncomputable def gP (g : Nat) : Nat := g / 1048576 % 1024

@[expose] noncomputable def gK (g : Nat) : Nat := g / 1073741824

@[expose] noncomputable def qaPairK (W P : List Nat) (C : List (List Nat)) (P0 g : Nat) : Bool :=
  Nat.blt (gP g) 693 && bitK P0 (gP g) && Nat.blt (gK g) 891 &&
    Nat.blt 0 (Nat.land P0 (nthK 0 P (gK g)) % 2 ^ 693) &&
    Nat.beq (gV g) (Nat.xor (apR (nthK [] C (gP g)) (nthK 0 W (gK g))) (nthK 0 W (gK g)) % 1048576)

@[expose] noncomputable def dualRowK (v s : Nat) (U : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun u _ ih t => (fRK v u == Nat.beq s t) && ih (Nat.succ t)) U

@[expose] noncomputable def dualQK (U G : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun g _ ih s => dualRowK g s U 0 && ih (Nat.succ s)) G

@[expose] noncomputable def adjK (M0 : Nat) (G U : List Nat) (W M : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun w _ ih M => List.rec (motive := fun _ => Bool) true
      (fun m M' _ => (al16 (Nat.land M0 m) ==
        Nat.beq (projR G U w % 1048576) (w % 1048576)) && ih M') M) W M

@[expose] noncomputable def qaChkE (W M P : List Nat) (C : List (List Nat)) (G U : List Nat) :
    Bool :=
  Nat.beq (lenK G) 10 && Nat.beq (lenK U) 10 && allK (qaPairK W P C (nthK 0 P 0)) G &&
    dualQK U G 0 && adjK (nthK 0 M 0) G U W M

@[expose] noncomputable def fixK (w : Nat) (C : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun A _ ih x => (bif Nat.beq (x % 2) 1 then Nat.beq (apR A w % 1048576) (w % 1048576)
      else true) && ih (x / 2)) C

@[expose] noncomputable def cvPairK (C : List (List Nat)) (P0 g : Nat) : Bool :=
  Nat.blt (gP g) 693 && bitK P0 (gP g) && Nat.blt (gK g) 20 &&
    Nat.beq (gV g) (Nat.xor (apR (nthK [] C (gP g)) (2 ^ gK g)) (2 ^ gK g) % 1048576)

@[expose] noncomputable def resK (U G : List Nat) (w : Nat) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m ih => ih && (Nat.beq (Nat.xor (2 ^ m) (projR U G (2 ^ m)) % 1048576) 0 ||
      Nat.beq (Nat.xor (2 ^ m) (projR U G (2 ^ m)) % 1048576) (w % 1048576))) n

@[expose] noncomputable def cvChkE (W P : List Nat) (C : List (List Nat)) (G U : List Nat) :
    Bool :=
  fixK (nthK 0 W 0) C (nthK 0 P 0) && allK (cvPairK C (nthK 0 P 0)) G &&
    resK U G (nthK 0 W 0) 20

end CFSG.SmithE.K
