module

public import Std.Data.HashMap
public import Std.Data.HashSet

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat

@[macro_inline] scoped instance (priority := high) decidableAndLazy {p q : Prop} [dp : Decidable p]
    [dq : Decidable q] : Decidable (p ∧ q) :=
  match dp with
  | isTrue hp =>
    match dq with
    | isTrue hq => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse (fun h => hq h.2)
  | isFalse hp => isFalse (fun h => hp h.1)

@[macro_inline] scoped instance (priority := high) decidableOrLazy {p q : Prop} [dp : Decidable p]
    [dq : Decidable q] : Decidable (p ∨ q) :=
  match dp with
  | isTrue hp => isTrue (Or.inl hp)
  | isFalse hp =>
    match dq with
    | isTrue hq => isTrue (Or.inr hq)
    | isFalse hq => isFalse (fun h => h.elim hp hq)

@[macro_inline] scoped instance (priority := high) decidableImpLazy {p q : Prop} [dp : Decidable p]
    [dq : Decidable q] : Decidable (p → q) :=
  match dp with
  | isTrue hp =>
    match dq with
    | isTrue hq => isTrue (fun _ => hq)
    | isFalse hq => isFalse (fun h => absurd (h hp) hq)
  | isFalse hp => isTrue (fun h => absurd h hp)

@[expose] def sortN (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

@[expose] def ptAct (t : Array Nat) (L : List Nat) : List Nat := sortN (L.map fun p => t.getD p 0)

@[expose] def distinctB {Lab : Type} [BEq Lab] [Hashable Lab] (a : Array Lab) : Bool :=
  (a.foldl (fun (acc : Bool × Std.HashSet Lab) x =>
    if acc.2.contains x then (false, acc.2) else (acc.1, acc.2.insert x)) (true, ∅)).1

structure OmegaData (Lab : Type) where
  lbl : Array Lab
  pn : Array (Array Nat)
  par : Array Nat
  via : Array Nat
  deriving Inhabited

section Omega

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def OmegaData.pathWord (O : OmegaData Lab) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, i => if i = 0 then [] else O.via[i]! :: O.pathWord f O.par[i]!

@[expose] def OmegaSpec (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (Δ : Lab)
    (O : OmegaData Lab) : Prop :=
  O.lbl[0]! = Δ ∧ 0 < O.lbl.size ∧
  (∀ l < letters.size, ∀ i < O.lbl.size,
    (O.pn[l]!)[i]! < O.lbl.size ∧ O.lbl[(O.pn[l]!)[i]!]! = act letters[l]! O.lbl[i]!) ∧
  (∀ i < O.lbl.size, 0 < i → O.par[i]! < i ∧ O.via[i]! < letters.size ∧
    (O.pn[O.via[i]!]!)[O.par[i]!]! = i) ∧
  distinctB O.lbl = true

instance (act : Array Nat → Lab → Lab) (letters : Array (Array Nat)) (Δ : Lab) (O : OmegaData Lab) :
    Decidable (OmegaSpec act letters Δ O) := by
  unfold OmegaSpec; infer_instance

structure ForestData where
  fpar : Array Nat
  fl : Array Nat
  fdep : Array Nat
  froot : Array Nat
  deriving Inhabited

@[expose] def ForestSpec (act : Array Nat → Lab → Lab) (lbl : Array Lab)
    (letters : Array (Array Nat)) (F : ForestData) : Prop :=
  ∀ i < lbl.size,
    (F.fdep[i]! = 0 ∧ F.froot[i]! = i) ∨
    (F.fpar[i]! < lbl.size ∧ F.fdep[F.fpar[i]!]! + 1 = F.fdep[i]! ∧ F.fl[i]! < letters.size ∧
      lbl[i]! = act letters[F.fl[i]!]! lbl[F.fpar[i]!]! ∧ F.froot[i]! = F.froot[F.fpar[i]!]!)

instance (act : Array Nat → Lab → Lab) (lbl : Array Lab) (letters : Array (Array Nat))
    (F : ForestData) : Decidable (ForestSpec act lbl letters F) := by
  unfold ForestSpec; infer_instance

end Omega

@[expose] def ForestData.roots (F : ForestData) (N : Nat) : List Nat :=
  (List.range N).filter fun i => F.fdep[i]! == 0

@[expose] def wordImg (tabs : Array (Array Nat)) (w : List Nat) (p : Nat) : Nat :=
  w.foldr (fun l q => (tabs.getD l #[]).getD q 0) p

@[expose] def wordTabA (tabs : Array (Array Nat)) (n : Nat) (w : List Nat) : Array Nat :=
  (Array.range n).map (wordImg tabs w)

@[expose] def labWord {Lab : Type} (act : Array Nat → Lab → Lab) (letters : Array (Array Nat))
    (Δ : Lab) (w : List Nat) : Lab :=
  w.foldr (fun l ℓ => act (letters.getD l #[]) ℓ) Δ

section Cert

structure AtomData (Lab : Type) where
  root : Nat
  cls : Nat
  mode : Nat
  oc : OmegaData Lab
  refPos : Nat
  refWord : List Nat
  refIdx : Nat
  deriving Inhabited

structure JoinData (Lab : Type) where
  j : Nat
  j' : Nat
  jj : Nat
  mode : Nat
  oj : OmegaData Lab
  refPos : Nat
  refWord : List Nat
  refIdx : Nat
  deriving Inhabited

structure LatData (Lab : Type) where
  O : OmegaData Lab
  F : ForestData
  sTabs : List (Array Nat)
  mw : Array (List (List Nat))
  mt : Array (List (Array Nat))
  Om : Array (OmegaData Lab)
  atoms : Array (AtomData Lab)
  joins : List (JoinData Lab)
  deriving Inhabited

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def MembersOK (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab)
    (D : LatData Lab) : Prop :=
  0 < D.mw.size ∧ D.mw[0]! = [] ∧ D.mt.size = D.mw.size ∧ D.Om.size = D.mw.size ∧
  ∀ j < D.mw.size, (∀ w ∈ D.mw[j]!, ∀ l ∈ w, l < 2) ∧
    D.mt[j]! = (D.mw[j]!).map (fun w => wordTabA #[ta, tb] n w) ∧
    OmegaSpec act (D.sTabs ++ D.mt[j]!).toArray Δ D.Om[j]!

instance (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab) (D : LatData Lab) :
    Decidable (MembersOK act n ta tb Δ D) := by
  unfold MembersOK; infer_instance

@[expose] def GensIn (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab)
    (j jj : Nat) : Prop :=
  ∀ t ∈ D.mt[j]!, ∃ x < D.Om[jj]!.lbl.size, D.Om[jj]!.lbl[x]! = act t Δ

instance (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (j jj : Nat) :
    Decidable (GensIn act Δ D j jj) := by
  unfold GensIn; infer_instance

@[expose] def rcLetters (n : Nat) (ta tb : Array Nat) (D : LatData Lab) (c : Nat) :
    List (Array Nat) :=
  D.sTabs ++ [wordTabA #[ta, tb] n (D.O.pathWord c c)]

@[expose] def AtomOK' (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (i : Nat)
    (d : AtomData Lab) (L : List (Array Nat)) : Prop :=
  d.root < D.O.lbl.size ∧ D.F.fdep[d.root]! = 0 ∧ d.cls ≤ D.mw.size ∧
  ((d.mode = 0 ∧
      (d.cls < D.mw.size → ∃ x < D.Om[d.cls]!.lbl.size, D.Om[d.cls]!.lbl[x]! = D.O.lbl[d.root]!) ∧
      OmegaSpec act L.toArray Δ d.oc ∧
      d.oc.lbl.size = (if d.cls < D.mw.size then D.Om[d.cls]!.lbl.size else D.O.lbl.size)) ∨
   (d.mode = 1 ∧ d.cls = D.mw.size ∧ d.refPos < i ∧ (D.atoms[d.refPos]!).cls = D.mw.size ∧
      d.refIdx < D.O.lbl.size ∧ D.F.froot[d.refIdx]! = (D.atoms[d.refPos]!).root ∧
      D.O.lbl[d.refIdx]! = labWord act L.toArray Δ d.refWord ∧ ∀ l ∈ d.refWord, l < L.length))

instance (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (i : Nat) (d : AtomData Lab)
    (L : List (Array Nat)) : Decidable (AtomOK' act Δ D i d L) := by
  unfold AtomOK'; infer_instance

@[expose] def AtomsOK (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab)
    (D : LatData Lab) : Prop :=
  (∀ r ∈ D.F.roots D.O.lbl.size, ∃ i < D.atoms.size, D.atoms[i]!.root = r) ∧
  ∀ i < D.atoms.size, AtomOK' act Δ D i D.atoms[i]! (rcLetters n ta tb D D.atoms[i]!.root)

instance (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab) (D : LatData Lab) :
    Decidable (AtomsOK act n ta tb Δ D) := by
  unfold AtomsOK; infer_instance

@[expose] def JoinOK' (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (e : JoinData Lab)
    (L : List (Array Nat)) : Prop :=
  e.j < D.mw.size ∧ e.j' < D.mw.size ∧ e.jj ≤ D.mw.size ∧
  ((e.mode = 0 ∧
      (e.jj < D.mw.size → GensIn act Δ D e.j e.jj ∧ GensIn act Δ D e.j' e.jj) ∧
      OmegaSpec act L.toArray Δ e.oj ∧
      e.oj.lbl.size = (if e.jj < D.mw.size then D.Om[e.jj]!.lbl.size else D.O.lbl.size)) ∨
   (e.mode = 1 ∧ e.jj = D.mw.size ∧ e.refPos < D.atoms.size ∧
      (D.atoms[e.refPos]!).cls = D.mw.size ∧
      e.refIdx < D.O.lbl.size ∧ D.F.froot[e.refIdx]! = (D.atoms[e.refPos]!).root ∧
      D.O.lbl[e.refIdx]! = labWord act L.toArray Δ e.refWord ∧ ∀ l ∈ e.refWord, l < L.length))

instance (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (e : JoinData Lab)
    (L : List (Array Nat)) : Decidable (JoinOK' act Δ D e L) := by
  unfold JoinOK'; infer_instance

@[expose] def joinLetters (D : LatData Lab) (e : JoinData Lab) : List (Array Nat) :=
  D.sTabs ++ D.mt[e.j]! ++ D.mt[e.j']!

@[expose] def JoinPairOK (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab)
    (j j' : Nat) : Prop :=
  GensIn act Δ D j j' ∨ GensIn act Δ D j' j ∨
    ∃ e ∈ D.joins, e.j = j ∧ e.j' = j' ∧ JoinOK' act Δ D e (joinLetters D e)

instance (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) (j j' : Nat) :
    Decidable (JoinPairOK act Δ D j j') := by
  unfold JoinPairOK; infer_instance

@[expose] def JoinsOK (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) : Prop :=
  ∀ j < D.mw.size, ∀ j' < D.mw.size, j < j' → JoinPairOK act Δ D j j'

instance (act : Array Nat → Lab → Lab) (Δ : Lab) (D : LatData Lab) :
    Decidable (JoinsOK act Δ D) := by
  unfold JoinsOK; infer_instance

@[expose] def LatOK (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab)
    (D : LatData Lab) : Prop :=
  OmegaSpec act #[ta, tb] Δ D.O ∧ (∀ t ∈ D.sTabs, act t Δ = Δ) ∧
  ForestSpec act D.O.lbl D.sTabs.toArray D.F ∧ MembersOK act n ta tb Δ D ∧
  AtomsOK act n ta tb Δ D ∧ JoinsOK act Δ D

instance (act : Array Nat → Lab → Lab) (n : Nat) (ta tb : Array Nat) (Δ : Lab) (D : LatData Lab) :
    Decidable (LatOK act n ta tb Δ D) := by
  unfold LatOK; infer_instance

end Cert

@[expose] def tupAct {Lab : Type} (act : Array Nat → Lab → Lab) (t : Array Nat) (L : List Lab) :
    List Lab :=
  L.map (act t)

section O2

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def O2OK (act : Array Nat → Lab → Lab) (D : LatData Lab)
    (Ot : Array (OmegaData (List Lab))) : Prop :=
  Ot.size = D.mw.size ∧ ∀ j < D.mw.size, D.Om[j]!.lbl.size % 2 = 1 ∧
    OmegaSpec (tupAct act) D.sTabs.toArray D.Om[j]!.lbl.toList Ot[j]!

instance (act : Array Nat → Lab → Lab) (D : LatData Lab) (Ot : Array (OmegaData (List Lab))) :
    Decidable (O2OK act D Ot) := by
  unfold O2OK; infer_instance

end O2

end CFSG.QuasithinUnique.Ch1.SporLat
