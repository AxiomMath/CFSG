module

public import Certificates.Data.CFSGNative.F3.Sep
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Monster.B.Fischer.Native

open CFSG.F3.Native CFSG.Monster.B.Co2.Native

@[inline, expose] def pairIdx (i j : Nat) : Nat := 77 * i - i * (i - 1) / 2 + (j - i)

@[inline, expose] def trit (b : ByteArray) (off k : Nat) : Nat :=
  ((b.get! (off + k / 4)).toNat - 40) / 3 ^ (k % 4) % 3

@[expose] def formRows (b : ByteArray) (off : Nat) : Array V :=
  Array.ofFn (n := 77) fun i =>
    V.ofFn 77 fun j => if i.val ≤ j then trit b off (pairIdx i.val j) else 0

@[expose] def polarRows (b : ByteArray) (off : Nat) : Array V :=
  let U := formRows b off
  let Ut := transpose 77 U
  Array.ofFn (n := 77) fun i => U[i.val]!.add Ut[i.val]!

@[inline, expose] def coefAt (C : Array V) (i j : Nat) : Nat :=
  if i = j then C[i]!.get i else (C[i]!.get j + C[j]!.get i) % 3

@[expose] def coefOK (C : Array V) (b : ByteArray) (off : Nat) : Bool :=
  allLt 77 fun i => allLt 77 fun j => !decide (i ≤ j) || coefAt C i j == trit b off (pairIdx i j)

@[expose] def pullbackOK (b : ByteArray) (off : Nat) (bTo : ByteArray) (offTo : Nat)
    (A At : Array V) : Bool :=
  coefOK (mul 77 At (mul 77 (formRows bTo offTo) A)) b off

@[expose] def actionOK (b : ByteArray) (gen : Array Nat) (A : Array V) (chunks : Nat) : Bool :=
  let At := transpose 77 A
  parLt 3510 chunks fun r =>
    decide (gen[r]! < 3510) && pullbackOK b (752 * r) b (752 * gen[r]!) A At

@[expose] def distinctOK (b : ByteArray) (chunks : Nat) : Bool :=
  parLt 3510 chunks fun r => allLt r fun r' =>
    Nat.any 77 fun i _ => Nat.any 77 fun j _ =>
      decide (i ≤ j) && trit b (752 * r) (pairIdx i j) != trit b (752 * r') (pairIdx i j)

@[expose] def linesOK (b : ByteArray) (n : Nat) : Bool :=
  b.size == 752 * n && allLt n fun r =>
    b.get! (752 * r + 751) == 10 && allLt 751 fun m =>
      decide (40 ≤ (b.get! (752 * r + m)).toNat) && decide ((b.get! (752 * r + m)).toNat < 121)

end CFSG.Monster.B.Fischer.Native
