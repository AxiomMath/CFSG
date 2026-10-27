module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.S1277Gm

open CFSG.Quasithin.H13.S127.Mod

@[expose] def sVF (c v : ℕ) : ℕ := v * (c % 2) ^^^ wV v * ((c >>> 1) % 2)

@[expose] def appF (A : Mc) (v : ℕ) : ℕ :=
  sVF (v &&& 3) A.c0 ^^^ sVF ((v >>> 2) &&& 3) A.c1 ^^^ sVF ((v >>> 4) &&& 3) A.c2

@[expose] def mulF (A B : Mc) : Mc := ⟨appF A B.c0, appF A B.c1, appF A B.c2⟩

@[expose] def memS (s i : ℕ) : Bool := decide (i < 262144) && s.testBit (i + 64)

@[expose] def insS (s i : ℕ) : ℕ := (s ||| 1 <<< (i + 64)) ^^^ ((i + 1) % 18446744073709551616)

@[expose] def bfsAddK (gens : List Mc) (sn : ℕ × List Mc) (x : Mc) : ℕ × List Mc :=
  gens.foldl (fun sn g =>
    bif memS sn.1 (mcIdx (mulF x g)) then sn
    else (insS sn.1 (mcIdx (mulF x g)), mulF x g :: sn.2)) sn

@[expose] def bfsStepK (gens : List Mc) (st : ℕ × List Mc × List Mc) : ℕ × List Mc × List Mc :=
  let sn := st.2.2.foldl (bfsAddK gens) (st.1, [])
  (sn.1, st.2.1 ++ sn.2, sn.2)

@[expose] def bfsK (gens : List Mc) : ℕ → ℕ × List Mc × List Mc → List Mc
  | 0, st => st.2.1
  | n + 1, st => if st.2.2 = [] then st.2.1 else bfsK gens n (bfsStepK gens st)

@[expose] def gmK : List Mc := bfsK gmGens 64 (insS 0 (mcIdx Mc.one), [Mc.one], [Mc.one])

@[expose] def Mc.ofIdx (n : ℕ) : Mc := ⟨n % 64, n / 64 % 64, n / 4096 % 64⟩

@[expose] def B6.ofP (p : ℕ) : B6 :=
  ⟨p % 64, (p >>> 6) % 64, (p >>> 12) % 64, (p >>> 18) % 64, (p >>> 24) % 64, (p >>> 30) % 64⟩

@[expose] def eqMc : List Mc → List ℕ → Bool
  | [], [] => true
  | A :: L, n :: N =>
    Nat.beq A.c0 (n % 64) && Nat.beq A.c1 (n / 64 % 64) && Nat.beq A.c2 (n / 4096 % 64) && eqMc L N
  | _, _ => false

@[expose] def eqB6 : List B6 → List ℕ → Bool
  | [], [] => true
  | B :: L, p :: N =>
    Nat.beq B.c0 (p % 64) && Nat.beq B.c1 ((p >>> 6) % 64) && Nat.beq B.c2 ((p >>> 12) % 64) &&
      Nat.beq B.c3 ((p >>> 18) % 64) && Nat.beq B.c4 ((p >>> 24) % 64) &&
      Nat.beq B.c5 ((p >>> 30) % 64) && eqB6 L N
  | _, _ => false

@[expose] def appP (p v : ℕ) : ℕ :=
  p % 64 * (v % 2) ^^^ (p >>> 6) % 64 * ((v >>> 1) % 2) ^^^ (p >>> 12) % 64 * ((v >>> 2) % 2) ^^^
    (p >>> 18) % 64 * ((v >>> 3) % 2) ^^^ (p >>> 24) % 64 * ((v >>> 4) % 2) ^^^
    (p >>> 30) % 64 * ((v >>> 5) % 2)

@[expose] def maskL (l : List ℕ) : ℕ := l.foldl (fun m x => m ||| 1 <<< x) 0

@[expose] def pc64 (m : ℕ) : ℕ := ((List.range 64).filter fun i => m.testBit i).length

@[expose] noncomputable def orbChk (P : List ℕ) : Bool :=
  CFSG.KC.Enum.strictB (maskL (P.map fun p => appP p 5)) fun m5 =>
    Nat.beq (pc64 m5) 45 &&
      (List.range 64).all fun c => m5.testBit c || !Nat.beq (pc64 (maskL (P.map fun p => appP p c))) 45

end CFSG.KC.S1277Gm

end
