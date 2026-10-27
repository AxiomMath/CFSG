module

public import Certificates.Data.Kernel.Misc.O73
public import Certificates.Data.Kernel.SmithEKM

public section

namespace CFSG.SmithE.K

open CFSG.KC.Misc.O73

@[expose] noncomputable def packK : List Nat → Nat :=
  fun P => List.rec (motive := fun _ => Nat) 0
    (fun m _ ih => Nat.lor m (Nat.shiftLeft ih 693)) P

@[expose] noncomputable def bitK (M x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight M x) 1) 1

@[expose] noncomputable def maskK : List Nat → Nat :=
  fun l => List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.lor (Nat.shiftLeft 1 x) ih) l

@[expose] noncomputable def lenK : List Nat → Nat :=
  fun l => List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def ltK (n : Nat) : List Nat → Bool :=
  fun l => List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Nat.blt x n && ih) l

@[expose] noncomputable def plK : List Nat → List (List Nat) → Bool :=
  fun P => List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun PL => PL.isEmpty)
    (fun m _ ih PL => Nat.beq (lenK (PL.headD [])) 21 && ltK 693 (PL.headD []) &&
      Nat.beq (maskK (PL.headD [])) m && ih PL.tail) P

@[expose] noncomputable def imgK (M T : Nat) : List Nat → Bool :=
  fun l => List.rec (motive := fun _ => Bool) true
    (fun x _ ih => bitK M (at' 10 T x) && ih) l

@[expose] noncomputable def genImgK (PK T : Nat) : List (List Nat) → List Nat → Bool :=
  fun PL => List.rec (motive := fun _ => List Nat → Bool)
    (fun J => J.isEmpty)
    (fun l _ ih J => Nat.blt (J.headD 0) 891 && imgK (at' 693 PK (J.headD 0)) T l && ih J.tail)
    PL

@[expose] noncomputable def wImgK (M T₁ T₂ : Nat) : List Nat → Bool :=
  fun l => List.rec (motive := fun _ => Bool) true
    (fun x _ ih => bitK M (at' 10 T₁ (at' 10 T₂ x)) && ih) l

@[expose] noncomputable def stabK (TP : Nat → Nat) (M : Nat) (l : List Nat) : List Nat → Bool :=
  fun W => List.rec (motive := fun _ => Bool) true
    (fun w _ ih => wImgK M (TP (w % 1024)) (TP (w / 1024)) l && ih) W

@[expose] noncomputable def pack10 : List Nat → Nat :=
  fun l => List.rec (motive := fun _ => Nat) 0
    (fun x _ ih => Nat.add x (Nat.mul 1024 ih)) l

@[expose] noncomputable def jpK : List (List Nat) → List Nat → Bool :=
  fun J => List.rec (motive := fun _ => List Nat → Bool) (fun JP => JP.isEmpty)
    (fun l _ ih JP => Nat.beq (pack10 l) (JP.headD 0) && ih JP.tail) J

@[expose] noncomputable def decR (r : Nat) : Nat × Nat × Nat :=
  (r % 1024, r / 1024 % 1024, r / 1048576)

@[expose] noncomputable def edgeJ (JP : List Nat) (g p v : Nat) : Bool :=
  Nat.beq (at' 10 (JP.getD g 0) p) v

@[expose] noncomputable def memK (x : Nat) : List Nat → Bool :=
  fun l => List.rec (motive := fun _ => Bool) false (fun y _ ih => Nat.beq y x || ih) l

@[expose] noncomputable def sgK (TP : Nat → Nat) (l : List Nat) : List Nat → List (List Nat) → Bool :=
  fun W => List.rec (motive := fun _ => List (List Nat) → Bool) (fun SG => SG.isEmpty)
    (fun w _ ih SG => Nat.beq (lenK (SG.headD [])) 21 && ltK 21 (SG.headD []) &&
      Nat.rec (motive := fun _ => Bool) true (fun k acc => acc &&
        Nat.beq (l.getD ((SG.headD []).getD k 0) 0)
          (at' 10 (TP (w % 1024)) (at' 10 (TP (w / 1024)) (l.getD k 0)))) 21 &&
      ih SG.tail) W

@[expose] noncomputable def s2K (C : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun u acc => Nat.rec (motive := fun _ => Nat) acc
    (fun w acc2 => bif Nat.beq u w then acc2 else
      Nat.lor acc2 (Nat.shiftLeft 1 (Nat.xor (C.getD u 0) (C.getD w 0)))) 21) 21

@[expose] noncomputable def clsK (C : List Nat) (S2 v : Nat) : Nat :=
  bif Nat.beq v 0 then 0 else bif memK v C then 1 else bif bitK S2 v then 2 else 3

@[expose] noncomputable def rootU (c : Nat) : Nat :=
  bif Nat.beq c 1 then 1 else bif Nat.beq c 2 then 3 else bif Nat.beq c 3 then 19 else 0

@[expose] noncomputable def countK (C : List Nat) (S2 c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun v acc => bif Nat.beq (clsK C S2 v) c then Nat.succ acc else acc) 512

@[expose] noncomputable def clsChkK (C : List Nat) (S2 : Nat) : Bool :=
  Nat.beq (clsK C S2 1) 1 && Nat.beq (clsK C S2 3) 2 && Nat.beq (clsK C S2 19) 3 &&
    Nat.beq (countK C S2 1) 21 && Nat.beq (countK C S2 2) 210 && Nat.beq (countK C S2 3) 280

@[expose] noncomputable def amK (C s : List Nat) (a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (bif bitK a j then C.getD (s.getD j 0) 0 else 0)) 9

@[expose] noncomputable def rootUK (C : List Nat) (S2 v : Nat) : Bool :=
  Nat.beq v (rootU (clsK C S2 v))

@[expose] noncomputable def edgeU (C : List Nat) (S2 : Nat) (SG : List (List Nat)) (g u v : Nat) :
    Bool :=
  Nat.beq (clsK C S2 u) (clsK C S2 v) && Nat.beq (amK C (SG.getD g []) u) v

@[expose] noncomputable def plpK (PLP : Nat) : List (List Nat) → Nat → Bool :=
  fun PL => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun l _ ih i => Nat.beq (at' 210 PLP i) (pack10 l) && ih (Nat.succ i)) PL

@[expose] noncomputable def meetK (PK M₀ j : Nat) : Nat := cntK 21 (Nat.land M₀ (at' 693 PK j))

@[expose] noncomputable def dClsK (c : Nat) : Bool :=
  Nat.beq c 21 || Nat.beq c 5 || Nat.beq c 1 || Nat.beq c 0

@[expose] noncomputable def dsK (PK M₀ : Nat) (DS : List Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => acc && dClsK (meetK PK M₀ j)) 891 &&
  Nat.beq (lenK DS) 4 && ltK 891 DS &&
  (List.zip [21, 5, 1, 0] DS).all fun cd => Nat.beq (meetK PK M₀ cd.2) cd.1 &&
    Nat.rec (motive := fun _ => Bool) true (fun j acc => acc && !Nat.beq (meetK PK M₀ j) cd.1) cd.2

@[expose] noncomputable def dRootK (DS : List Nat) (c : Nat) : Nat :=
  bif Nat.beq c 21 then DS.getD 0 0 else bif Nat.beq c 5 then DS.getD 1 0 else
    bif Nat.beq c 1 then DS.getD 2 0 else DS.getD 3 0

@[expose] noncomputable def wImgP (M T₁ T₂ R : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun m acc => acc && bitK M (at' 10 T₁ (at' 10 T₂ (at' 10 R m)))) 21

@[expose] noncomputable def edgeD (TP : Nat → Nat) (PK PLP M₀ : Nat) (SW : List Nat) (g p v : Nat) :
    Bool :=
  Nat.beq (meetK PK M₀ p) (meetK PK M₀ v) &&
    wImgP (at' 693 PK v) (TP (SW.getD g 0 % 1024)) (TP (SW.getD g 0 / 1024)) (at' 210 PLP p)

end CFSG.SmithE.K
