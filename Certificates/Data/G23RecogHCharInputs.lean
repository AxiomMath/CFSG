module

public import Certificates.Data.G23RecogHFactsInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23.HCharData

open CFSG.GH74.QTGen4.Recog.G23 CFSG.GH74.QTGen4.Recog.G23.HFactsData

@[expose] def hcSize : Fin 20 → ℕ := ![1, 1, 6, 8, 8, 18, 6, 48, 8, 8, 48, 32, 32, 32, 32, 72, 72,
    36, 36, 72]

@[expose] def hcOrd : Fin 20 → ℕ := ![1, 2, 4, 3, 6, 2, 4, 12, 3, 6, 12, 3, 6, 3, 6, 2, 8, 4, 4, 8]

@[expose] def hcDfl : Fin 20 → Bool := ![false, true, true, true, true, false, true, true, true,
    true, true, true, true, true, true, false, true, false, false, true]

@[expose] def hcWords : Fin 20 → List (Fin 5 × Bool) :=
  ![[],
    [(0, true), (1, false), (1, false), (0, true), (1, false), (1, false)],
    [(4, false), (1, true), (1, true), (0, false), (4, true)],
    [(1, true), (1, true), (4, false), (1, true), (1, true), (0, false), (4, true)],
    [(1, true), (1, true), (4, false), (1, true), (1, true), (0, false), (4, true), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false)],
    [(4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false), (0, true), (1, false), (1, false)],
    [(4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
      (1, false)],
    [(4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false), (0, true), (4, false), (1, true), (1, true), (0, false),
      (4, true)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (1, true), (1, true),
      (0, false), (4, true)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true), (1, true),
      (1, true), (4, false), (1, true), (1, true), (0, false), (4, true)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true), (1, true),
      (1, true), (4, false), (1, true), (1, true), (0, false), (4, true), (0, true), (1, false),
      (1, false), (0, true), (1, false), (1, false)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true), (1, true),
      (1, true), (4, false), (1, true), (1, true), (0, false), (4, true), (1, true), (1, true),
      (4, false), (1, true), (1, true), (0, false), (4, true)],
    [(3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true), (1, true),
      (1, true), (4, false), (1, true), (1, true), (0, false), (4, true), (1, true), (1, true),
      (4, false), (1, true), (1, true), (0, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false)],
    [(4, true), (3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true),
      (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false)],
    [(4, true), (3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true),
      (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false), (4, false), (1, true), (1, true),
      (0, false), (4, true)],
    [(4, true), (3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true),
      (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false), (2, true), (3, false), (3, false),
      (4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (4, false), (1, true), (1, true), (0, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false)],
    [(4, true), (3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true),
      (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false), (2, true), (3, false), (3, false),
      (4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (4, false), (1, true), (1, true), (0, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false), (0, true), (1, false), (1, false), (0, true), (1, false),
      (1, false)],
    [(4, true), (3, true), (3, true), (4, false), (3, true), (3, true), (2, false), (4, true),
      (1, true), (1, true), (1, true), (1, true), (0, true), (1, false), (1, false), (0, true),
      (1, false), (1, false), (0, true), (1, false), (1, false), (2, true), (3, false), (3, false),
      (4, false), (3, true), (3, true), (2, false), (4, true), (0, true), (1, false), (1, false),
      (4, false), (1, true), (1, true), (0, false), (4, true), (0, true), (1, false), (1, false),
      (0, true), (1, false), (1, false), (4, false), (1, true), (1, true), (0, false), (4, true)]]

@[expose] def hcI : Fin 4 → Fin 20 := ![3, 8, 11, 17]

@[expose] def hcA : Fin 4 → Fin 20 → Fin 20 → ℕ :=
  ![![![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![8, 0, 4, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 8, 4, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 8, 8, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 1, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 3, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 1, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 3, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 0, 0, 0, 0, 0],
    ![8, 0, 0, 0, 0, 0, 4, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 8, 0, 0, 0, 0, 4, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 8, 0, 0, 8, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 0, 0, 1, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 0, 0, 3, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 9, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 12, 12, 12, 0, 0, 12, 12, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 0, 0, 0, 2, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 4, 0, 0, 2, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 0],
    ![0, 0, 0, 12, 12, 0, 0, 12, 0, 0, 0, 0, 0, 12, 12, 0, 0, 0, 0, 0],
    ![32, 0, 16, 0, 0, 16, 16, 0, 0, 0, 0, 10, 6, 0, 0, 0, 0, 0, 0, 0],
    ![0, 32, 16, 0, 0, 16, 16, 0, 0, 0, 0, 6, 10, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 4, 12, 0, 0, 8, 4, 12, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 12, 4, 0, 0, 8, 12, 4, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 8, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 8, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 8, 8]],
    ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 2, 1, 1, 2],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 1, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 8, 4, 4, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 4, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 4, 4, 4, 8],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 8, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 8, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 8, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 0, 8, 4],
    ![0, 0, 0, 0, 0, 16, 0, 12, 0, 0, 12, 9, 9, 9, 9, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 8, 24, 12, 18, 18, 6, 9, 9, 9, 9, 0, 0, 0, 0, 0],
    ![36, 0, 6, 0, 18, 2, 6, 3, 0, 18, 3, 9, 0, 9, 0, 0, 0, 0, 0, 0],
    ![0, 36, 6, 18, 0, 2, 6, 3, 18, 0, 3, 0, 9, 0, 9, 0, 0, 0, 0, 0],
    ![0, 0, 24, 18, 18, 8, 0, 6, 0, 0, 12, 9, 9, 9, 9, 0, 0, 0, 0, 0]]]

@[expose] def hcCt : Fin 20 → ℕ := ![91, 90, 36, 36, 36, 19, 36, 12, 36, 36, 12, 18, 18, 18, 18, 7,
    8, 16, 16, 8]

@[expose] def evalW (w : List (Fin 5 × Bool)) : ↥Hc :=
  (w.map fun p => cond p.2 (gA p.1) (gA p.1)⁻¹).prod

@[expose] def hcRep (j : Fin 20) : ↥Hc := evalW (hcWords j)

def hcRepTab : Array (List ℕ) := Array.ofFn fun j : Fin 20 => Lx (hcRep j)

def hcRepL (j : Fin 20) : List ℕ := hcRepTab[j.val]!

abbrev RepLOK : Prop := ∀ j : Fin 20, hcRepL j = Lx (hcRep j)

@[expose] def invL (l : List ℕ) : List ℕ := (List.range 32).map fun i => l.idxOf i

@[expose] def powL (l : List ℕ) : ℕ → List ℕ
  | 0 => idL
  | n + 1 => mulL l (powL l n)

def conjG (k : Fin 5) (b : Bool) (x : List ℕ) : List ℕ :=
  if b then mulL (mulL (Lst (gen k)) x) (Lst (gen k)⁻¹)
  else mulL (mulL (Lst (gen k)⁻¹) x) (Lst (gen k))

def conjC (k : Fin 5) (b : Bool) (c : List ℕ) : List ℕ :=
  if b then mulL (Lst (gen k)) c else mulL (Lst (gen k)⁻¹) c

def cjGens : List (Fin 5 × Bool) := (List.finRange 5).flatMap fun k => [(k, true), (k, false)]

def cjStep (seen fr : List (List ℕ × List ℕ)) :
    List (List ℕ × List ℕ) × List (List ℕ × List ℕ) :=
  fr.foldl (fun acc p => cjGens.foldl (fun acc' kb =>
    let x' := conjG kb.1 kb.2 p.1
    if acc'.1.any (fun q => q.1 == x') then acc' else
      let q' := (x', conjC kb.1 kb.2 p.2)
      (acc'.1 ++ [q'], acc'.2 ++ [q'])) acc) (seen, [])

def cjAux : ℕ → List (List ℕ × List ℕ) → List (List ℕ × List ℕ) → List (List ℕ × List ℕ)
  | 0, seen, _ => seen
  | n + 1, seen, fr =>
    if fr.isEmpty then seen else
      let r := cjStep seen fr
      cjAux n r.1 r.2

def cjClass (r : List ℕ) : List (List ℕ × List ℕ) := cjAux 100 [(r, idL)] [(r, idL)]

def KTab : Array (List (List ℕ × List ℕ)) := Array.ofFn fun j : Fin 20 => cjClass (hcRepL j)

def KC (j : Fin 20) : List (List ℕ × List ℕ) := KTab[j.val]!

def KFstTab : Array (List (List ℕ)) := KTab.map fun l => l.map Prod.fst

def KFst (j : Fin 20) : List (List ℕ) := KFstTab[j.val]!

abbrev KFstOK : Prop := ∀ j : Fin 20, KFst j = (KC j).map Prod.fst

abbrev RepOK : Prop := hcRepL 0 = idL ∧ hcRepL 1 = Lx zA

abbrev InvOK : Prop := ∀ l ∈ elts, invL l ∈ elts ∧ mulL (invL l) l = idL

abbrev OrdOK : Prop :=
  ∀ j : Fin 20, powL (hcRepL j) (hcOrd j) = idL ∧ ∀ m < hcOrd j, 0 < m → powL (hcRepL j) m ≠ idL

abbrev DOK : Prop :=
  ∀ j : Fin 20, hcDfl j = true ↔
    (hcOrd j = 3 ∨ (hcOrd j % 2 = 0 ∧ powL (hcRepL j) (hcOrd j / 2) = Lx zA))

abbrev ClassOK : Prop :=
  (∀ j : Fin 20, (hcRepL j, idL) ∈ KC j) ∧
  (∀ j : Fin 20, ∀ p ∈ KC j, p.1 ∈ elts ∧ p.2 ∈ elts ∧ mulL p.2 (hcRepL j) = mulL p.1 p.2) ∧
  (∀ j : Fin 20, ∀ p ∈ KC j, ∀ k : Fin 5,
      mulL (mulL (Lx (gA k)) p.1) (Lx (gA k)⁻¹) ∈ KFst j ∧
      mulL (mulL (Lx (gA k)⁻¹) p.1) (Lx (gA k)) ∈ KFst j) ∧
  (∀ x ∈ elts, ∃ j : Fin 20, x ∈ KFst j) ∧
  (∀ i j : Fin 20, i ≠ j → ∀ x ∈ KFst i, x ∉ KFst j) ∧
  (∀ j : Fin 20, (KFst j).Nodup ∧ (KFst j).length = hcSize j)

abbrev CtOK : Prop :=
  (elts.filter fun u => decide (mulL u u = idL ∧ u ≠ idL ∧ u ≠ Lx zA)).length = hcCt 1 ∧
  ∀ j : Fin 20, j ≠ 1 →
    (elts.filter fun u => decide (mulL u u = idL ∧ u ≠ idL ∧
      mulL u (hcRepL j) = mulL (invL (hcRepL j)) u)).length = hcCt j

abbrev AOK : Prop := ∀ r : Fin 4, ∀ k : Fin 20, ∀ j : Fin 20,
  ((KC (hcI r)).filter fun p => decide (mulL (invL p.1) (hcRepL k) ∈ KFst j)).length = hcA r j k

end CFSG.GH74.QTGen4.Recog.G23.HCharData
