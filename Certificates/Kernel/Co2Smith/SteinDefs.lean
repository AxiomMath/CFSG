module

public import CFSG.Sporadic.Co2Smith.GlU62SteinInputs
public import Certificates.Kernel.Co2Smith.Elems
public import Certificates.Data.Kernel.F2Word

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KC.F2W

@[expose] def mulC (x y : Nat) : Nat :=
  (x % 2 * (y % 2) + x / 2 * (y / 2)) % 2 +
    2 * ((x % 2 * (y / 2) + x / 2 * (y % 2) + x / 2 * (y / 2)) % 2)

@[expose] def mkF (x y : Bool) : CFSG.Fischer.F4 :=
  ⟨⟨x.toNat + 2 * y.toNat, by cases x <;> cases y <;> decide⟩⟩

@[expose] def decF (a : Nat) : Array CFSG.Fischer.F4 :=
  Array.ofFn fun k : Fin 36 => mkF (a.testBit k.val) (a.testBit (k.val + 36))

@[expose] def M36 : Nat := 68719476735

@[expose] def M72 : Nat := 4722366482869645213695

@[expose] def loF (a : Nat) : Nat := Nat.land a M36

@[expose] def hiF (a : Nat) : Nat := Nat.land (Nat.shiftRight a 36) M36

@[expose] noncomputable def mul4 (a b : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.xor (mulW 6 (loF a) (loF b)) (mulW 6 (hiF a) (hiF b))) M36)
    (Nat.shiftLeft (Nat.land (Nat.xor (Nat.xor (mulW 6 (loF a) (hiF b)) (mulW 6 (hiF a) (loF b)))
      (mulW 6 (hiF a) (hiF b))) M36) 36)

@[expose] def eqF (a b : Nat) : Bool := Nat.beq (Nat.land a M72) (Nat.land b M72)

@[expose] def oneF : Nat := 34630287489

@[expose] def putF (p x : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (x % 2) p) (Nat.shiftLeft (x / 2) (p + 36))

@[expose] def eltK (r c : Nat) : Nat :=
  let i := stPosI.getD r 0
  let j := stPosJ.getD r 0
  Nat.xor oneF (if r < 12 then Nat.xor (putF (6 * i + j) c) (putF (6 * (5 - j) + (5 - i)) (mulC c c))
    else if c = 0 then 0 else putF (6 * i + j) 1)

@[expose] noncomputable def gensK (B : List Nat) : List (Nat × Nat) :=
  B.flatMap fun t => (stParams t).map fun c => (eltK t c, rootK t c)

@[expose] noncomputable def dK : Nat × Nat := (oneF, IDP)

@[expose] noncomputable def stepG (p : Nat × Nat) (acc : List (Nat × Nat)) (g : Nat × Nat) :
    List (Nat × Nat) :=
  if acc.any (fun e => eqF e.1 (mul4 p.1 g.1)) then acc
  else acc ++ [(mul4 p.1 g.1, mulV p.2 g.2)]

@[expose] noncomputable def stepK (gens : List (Nat × Nat)) (acc : List (Nat × Nat))
    (p : Nat × Nat) : List (Nat × Nat) :=
  gens.foldl (stepG p) acc

@[expose] noncomputable def bfsK (gens : List (Nat × Nat)) :
    Nat → List (Nat × Nat) → Nat → List (Nat × Nat)
  | 0, acc, _ => acc
  | fuel + 1, acc, i =>
    if i < acc.length then bfsK gens fuel (stepK gens acc (acc.getD i dK)) (i + 1) else acc

@[expose] noncomputable def stCheckK (gens : List (Nat × Nat)) : Bool :=
  let L := bfsK gens 200 [dK] 0
  decide (0 < L.length) && eqF (L.getD 0 dK).1 oneF && eqK (L.getD 0 dK).2 IDP &&
    ((List.range L.length).all fun i => (List.range L.length).all fun j =>
      i == j || !eqF (L.getD i dK).1 (L.getD j dK).1) &&
    L.all fun x => gens.all fun g => L.any fun y =>
      eqF y.1 (mul4 x.1 g.1) && eqK y.2 (mulV x.2 g.2)

@[expose] noncomputable def stBlkK (k : Nat) : Bool :=
  stOpp (k / 18) (k % 18) || stCheckK (gensK (stBlock (k / 18) (k % 18)))

@[expose] noncomputable def stOppK : Bool :=
  [[3, 9], [5, 11], [14, 17]].all fun B => stCheckK (gensK B)

end CertificateChecks.KernelCo2Smith
