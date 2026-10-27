module

public import Certificates.Data.Kernel.LocalQT.Cov

public section

namespace CFSG.KC.M22S

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.Syl CFSG.KC.LQT.Cov

@[expose] def rootsK : List Nat :=
  [7, 9, 24, 28, 79, 80, 88, 89, 94, 95, 101, 104, 105, 107, 109, 110, 115, 117, 118, 120]

@[expose] def aVK : List Nat := [79, 80, 89, 95, 101, 104, 105, 107, 109, 110, 115, 117]

@[expose] def hWK : List Nat := [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
  1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0]

@[expose] noncomputable def iffB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def sqWK (D : CD) (v₁ v₂ : Nat) : List (Nat × Bool) :=
  List.append (List.append (List.append (posK (getK D.words v₁ [])) (posK (getK D.words v₁ [])))
    (invWK (getK D.words v₂ []))) (invWK (getK D.words v₂ []))

@[expose] noncomputable def formsK (D : CD) (F : List Nat) : Bool :=
  allL F fun f => Nat.blt f (Nat.pow 2 (Nat.add (Nat.mul 3 D.nV) (Nat.mul 32 (lenK D.blocks))))

@[expose] noncomputable def hintK (D : CD) (F ks : List Nat) (t : Nat) : Bool :=
  andB (allL ks fun k => Nat.blt k (Nat.sub (lenK F) (lenK D.free))) (Nat.beq (xorK F ks) t)

@[expose] noncomputable def formsOf (D : CD) : List Nat := List.map (fun q => q.2) (eqnsK D)

@[expose] noncomputable def gensOf (cA cB : Nat) (D : CD) : List Nat := List.map (wP 22 cA cB) D.xw

@[expose] noncomputable def eltsOf (cA cB : Nat) (D : CD) : List Nat :=
  List.map (elK 22 (gensOf cA cB D)) D.words

@[expose] noncomputable def sqD (cA cB : Nat) (H : List Nat) (v₁ v₂ : Nat) (D : CD) : Bool :=
  letI r := walkK D 0 (sqWK D v₁ v₂)
  letB (mul 22 (getK (eltsOf cA cB D) v₁ 0) (getK (eltsOf cA cB D) v₁ 0)) fun s =>
  allBs [Nat.beq r.2 0, formsK D (formsOf D), hintK D (formsOf D) H (Nat.xor r.1 (Nat.pow 2 189)),
    Nat.blt v₁ D.nV, Nat.beq (mul 22 s s) (one 22), notB (Nat.beq s (one 22))]

@[expose] noncomputable def sqHK (cA cB : Nat) (cs : List Char) (H : List Nat) (v₁ v₂ : Nat) :
    Bool :=
  Option.rec (motive := fun _ => Bool) false (sqD cA cB H v₁ v₂) (parseCov cs)

@[expose] noncomputable def twWalkD (D : CD) (ks : List Nat) (v : Nat) : Bool :=
  letI r := walkK D 0 (sqWK D v 79)
  allBs [Nat.blt v D.nV, Nat.beq r.2 0, hintK D (formsOf D) ks r.1]

@[expose] noncomputable def twD (X E : List Nat) (H : List (List Nat)) (D : CD) (z : Nat) : Bool :=
  allBs [allLtK 3 (fun i => Nat.beq (mul 22 (getK X i (one 22)) (getK X i (one 22))) (one 22)),
    allLtK D.nV (fun v => letB (getK E v 0) fun e =>
      orB (notB (allLtK 3 fun i => Nat.beq (mul 22 e (getK X i (one 22)))
        (mul 22 (getK X i (one 22)) e))) (orB (Nat.beq e (one 22)) (Nat.beq e z))),
    allLtK D.nV (fun v => letB (getK E v 0) fun e => iffB (Nat.beq (mul 22 e e) z) (memL v rootsK)),
    formsK D (formsOf D), Nat.beq (lenK H) (lenK aVK),
    allLtK (lenK aVK) (fun j => twWalkD D (getK H j []) (getK aVK j 0)),
    Nat.blt 79 D.nV, Nat.beq (mul 22 z z) (one 22), notB (Nat.beq z (one 22)),
    allLtK D.nV (fun v => letB (getK E v 0) fun e => Nat.beq (mul 22 z e) (mul 22 e z))]

@[expose] noncomputable def twHK (cA cB : Nat) (cs : List Char) (H : List (List Nat)) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun D =>
    letB (mul 22 (getK (eltsOf cA cB D) 79 0) (getK (eltsOf cA cB D) 79 0)) fun z =>
      twD (gensOf cA cB D) (eltsOf cA cB D) H D z) (parseCov cs)

@[expose] noncomputable def cjK (u g v : Nat) : Nat := mul 22 (mul 22 u g) v

@[expose] noncomputable def coreK (E : List Nat) (h hi g : Nat) : Bool :=
  allBs [memL g E, memL (cjK hi g h) E, memL (cjK h g hi) E]

@[expose] noncomputable def i22D (X E : List Nat) (n h hi a z : Nat) : Bool :=
  allBs [Nat.beq n 128, Nat.beq (mul 22 h z) (mul 22 z h), Nat.beq (mul 22 (mul 22 h h) h) (one 22),
    notB (Nat.beq h (one 22)),
    allL aVK (fun v => Nat.beq (mul 22 (getK E v 0) (getK E v 0)) z),
    allL rootsK (fun v => orB (notB (memL (cjK hi (getK E v 0) h) E)) (memL v aVK)),
    coreK E h hi a,
    anyL aVK (fun w => Nat.beq (cjK (mul 22 a h) (inv 22 a) hi) (getK E w 0)),
    allLtK n (fun v => letB (getK E v 0) fun e => orB (notB (coreK E h hi e))
      (allLtK 3 fun i => coreK E h hi (cjK (getK X i (one 22)) e (inv 22 (getK X i (one 22))))))]

@[expose] noncomputable def i22K (cA cB : Nat) (cs : List Char) (hw : List Nat) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun D =>
    letB (wP 22 cA cB hw) fun h => letB (getK (eltsOf cA cB D) 79 0) fun a =>
      i22D (gensOf cA cB D) (eltsOf cA cB D) D.nV h (inv 22 h) a (mul 22 a a)) (parseCov cs)

end CFSG.KC.M22S

end
