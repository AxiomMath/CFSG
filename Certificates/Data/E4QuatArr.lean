module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E4A

open CFSG.Monster.B.Co2.Native

variable (n : Nat)

@[expose] def memA (L : List (Array Nat)) (x : Array Nat) : Bool := L.any fun y => eqA n x y

@[expose] def conjA (h x : Array Nat) : Array Nat := compA n (compA n h x) (invCand n h)

@[expose] def q8A (r i j : Array Nat) : List (Array Nat) :=
  [idA n, r, i, compA n i r, j, compA n j r, compA n i j, compA n (compA n i j) r]

@[expose] def normsA (L : List (Array Nat)) (i j h : Array Nat) : Bool :=
  memA n L (conjA n h i) && memA n L (conjA n h j)

@[expose] def closedA (L : List (Array Nat)) (i j : Array Nat) : Bool :=
  memA n L (idA n) && L.all fun x =>
    memA n L (compA n i x) && memA n L (compA n j x) && memA n L (compA n (invCand n i) x) &&
      memA n L (compA n (invCand n j) x)

@[expose] def lettersA (gens : List (Array Nat)) : List (Array Nat) := gens ++ gens.map (invCand n)

@[expose] def memberCheckA (gens L : List (Array Nat)) (i j : Array Nat) (ws : List (Array Nat))
    (σ : List (List Nat)) : Bool :=
  decide (0 < ws.length) && eqA n (ws.getD 0 (idA n)) (idA n) &&
    (List.range ws.length).all fun k =>
      (List.range (lettersA n gens).length).all fun l =>
        decide ((σ.getD k []).getD l 0 < ws.length) &&
          normsA n L i j (compA n (compA n (invCand n (ws.getD ((σ.getD k []).getD l 0) (idA n)))
            ((lettersA n gens).getD l (idA n))) (ws.getD k (idA n)))

@[expose] def treeStepA (L : List (Array Nat)) (i j u gp gk : Array Nat) (d : Bool) : Bool :=
  !normsA n L i j (compA n (invCand n gp) gk) &&
    (if d then normsA n L i j (compA n (compA n (invCand n gk) (conjA n gp u)) gk)
      else normsA n L i j (compA n (compA n (invCand n gp) (conjA n gk u)) gp))

@[expose] def treeCheckA (L U : List (Array Nat)) (i j : Array Nat) (ws : List (Array Nat))
    (tree : List (Nat × Bool × Nat)) : Bool :=
  U.all (fun u => memA n L u && !eqA n (compA n u u) (idA n) &&
      eqA n (compA n (compA n u u) (compA n u u)) (idA n)) &&
    (List.range ws.length).all fun k => k == 0 ||
      (decide ((tree.getD k (0, false, 0)).1 < k) &&
        decide ((tree.getD k (0, false, 0)).2.2 < U.length) &&
        treeStepA n L i j (U.getD (tree.getD k (0, false, 0)).2.2 (idA n))
          (ws.getD (tree.getD k (0, false, 0)).1 (idA n)) (ws.getD k (idA n))
          (tree.getD k (0, false, 0)).2.1)

@[expose] def nbrCheckA (L : List (Array Nat)) (i j : Array Nat) (ws : List (Array Nat))
    (allowed : List Nat) : Bool :=
  (List.range ws.length).all fun k => decide (k ∈ allowed) ||
    !(normsA n L i j (conjA n (ws.getD k (idA n)) i) &&
      normsA n L i j (conjA n (ws.getD k (idA n)) j))

@[expose] def edgeCheckA (L : List (Array Nat)) (i j g : Array Nat) : Bool :=
  !normsA n L i j g && normsA n L i j (conjA n g i) && normsA n L i j (conjA n g j)

@[expose] def violatesA (T : List (Array Nat)) (i j c : Array Nat) : Bool :=
  T.any (fun x => !memA n T (conjA n c x)) &&
    [i, j].any fun x => [conjA n c i, conjA n c j].any fun y =>
      !eqA n (compA n x y) (compA n y x)

@[expose] def sameSetA (A B : List (Array Nat)) : Bool :=
  A.all (fun x => memA n B x) && B.all (fun x => memA n A x)

@[expose] def badWitA (u w : Array Nat) : Bool :=
  !eqA n (compA n (conjA n w u) u) (compA n u (conjA n w u)) &&
    !eqA n (conjA n (conjA n w u) u) (invCand n u)

@[expose] def identSqCheckA (r : Array Nat) (S W : List (Array Nat))
    (Ls : List (List (Array Nat))) : Bool :=
  S.all fun u => W.any (badWitA n u) || S.all fun v => !eqA n (conjA n v u) (invCand n u) ||
    (Ls.any (sameSetA n (q8A n r u v)) || W.any (violatesA n (q8A n r u v) u v))

end CFSG.ClassicalInvolution.Q3.TL4.E4A
