module

public import Certificates.Data.SmithECheck
public import Certificates.Data.Kernel.SmithL6K

public section

namespace CFSG.SmithE.K

open CFSG.F4.Native CFSG.SmithE

@[expose] def mulsC (c : Nat) : List Nat := (List.range 4).map fun a => scaleC a c

@[expose] def vecMaskK (A B C : List Nat) : Nat :=
  (List.range 64).foldl (fun acc d =>
    acc ||| 2 ^ (A.getD (d % 4) 0 ^^^ B.getD (d / 4 % 4) 0 ^^^ C.getD (d / 16) 0)) 0

@[expose] def decW (x : Nat) : Nat × Nat × Nat := (x % 4096, x / 4096 % 4096, x / 4096 / 4096)

@[expose] def modelOKW (W : Nat × Nat × Nat) (m : Nat) : Bool :=
  hermC W.1 W.1 == 0 && hermC W.2.1 W.2.1 == 0 && hermC W.2.2 W.2.2 == 0 &&
    hermC W.1 W.2.1 == 0 && hermC W.1 W.2.2 == 0 && hermC W.2.1 W.2.2 == 0 &&
    atLeast 64 m && !atLeast 65 m && wedgeScalar W != 0 &&
    (List.range 10).all fun k =>
      f4sq (f4mul (wedgeScalar W) (pluck W k)) == f4mul (wedgeScalar W) (pluck W (19 - k))

@[expose] def pinRow (W : Nat × Nat × Nat) (w m : Nat) : Bool :=
  wedgeCode W == w && vecMaskK (mulsC W.1) (mulsC W.2.1) (mulsC W.2.2) == m && modelOKW W m

@[expose] noncomputable def pinsK : List Nat → List Nat → List Nat → Bool :=
  fun D => List.rec (motive := fun _ => List Nat → List Nat → Bool) (fun _ _ => true)
    (fun x _ ih W M => pinRow (decW x) (W.headD 0) (M.headD 0) && ih W.tail M.tail) D

@[expose] noncomputable def pinChunkK (D W M : List Nat) (a n : Nat) : Bool :=
  pinsK ((D.drop a).take n) ((W.drop a).take n) ((M.drop a).take n)

@[expose] def wBits (W : List Nat) : Nat := CFSG.SmithL6.K.maskOf W

@[expose] noncomputable def nodupK : List Nat → Nat → Bool :=
  fun l => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih S => !S.testBit w && ih (S ||| 2 ^ w)) l

@[expose] noncomputable def wListOK (W : List Nat) : Bool :=
  W.all (fun w => w != 0 && decide (w < 2 ^ 20)) && nodupK W 0

@[expose] noncomputable def rowK (B wi mi : Nat) : List Nat → List Nat → Bool → Bool :=
  fun W => List.rec (motive := fun _ => List Nat → Bool → Bool) (fun _ f => f)
    (fun wj _ ih M f => cond (B.testBit (wi ^^^ wj))
      (atLeast 16 (mi &&& M.headD 0) && ih M.tail (wj != wi || f)) (ih M.tail f)) W

@[expose] noncomputable def anyK (B wi mi : Nat) : List Nat → List Nat → Bool :=
  fun W => List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun wj _ ih M => (B.testBit (wi ^^^ wj) && atLeast 16 (mi &&& M.headD 0) && wj != wi) ||
      ih M.tail) W

@[expose] noncomputable def rowsK (B : Nat) (W M : List Nat) :
    List Nat → List Nat → List Nat → List Nat → Bool :=
  fun R => List.rec (motive := fun _ => List Nat → List Nat → List Nat → Bool) (fun _ _ _ => true)
    (fun wi _ ih S Wt Mt => rowK B wi (S.headD 0) Wt Mt (anyK B wi (S.headD 0) W M) &&
      ih S.tail Wt.tail Mt.tail) R

@[expose] noncomputable def chunkK (W M : List Nat) (a n : Nat) : Bool :=
  rowsK (wBits W) W M ((W.drop a).take n) ((M.drop a).take n) (W.drop (a + 1)) (M.drop (a + 1))

end CFSG.SmithE.K
