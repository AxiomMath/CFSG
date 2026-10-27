module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGDepASmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

inductive GGTWPos : Type
  | ends
  | adj
  deriving DecidableEq

instance : Fintype GGTWPos :=
  Fintype.ofList [GGTWPos.ends, GGTWPos.adj] (by intro x; cases x <;> simp)

inductive GGTWMode : Type
  | frame
  | other
  deriving DecidableEq

abbrev GGTWE (p N : ℕ) : Type := Fin (N - 1) → ZMod p

abbrev ggTWdot {p N : ℕ} (a v : GGTWE p N) : ZMod p := ggDepAdot (N := N - 1) a v

@[expose] def ggTWx (p N : ℕ) : GGTWE p N := fun j => if j.val + 2 = N then 1 else 0

@[expose] def ggTWh (p N : ℕ) (i : Fin (N - 1)) : GGTWE p N := fun j =>
  if j.val + 2 = N then 0
  else if i.val = 0 then -((j.val : ZMod p) + 2)
  else if j.val + 1 = i.val then 1 else 0

@[expose] def ggTWα (p N : ℕ) (i : Fin (N - 1)) : GGTWE p N := fun j =>
  if j.val + 2 = N then 0
  else if j.val + 1 = i.val then 2
  else if j.val + 2 = i.val ∨ j.val = i.val then -1 else 0

@[expose] def ggTWz (p N : ℕ) (pos : GGTWPos) : GGTWE p N := fun j =>
  match pos with
  | .ends => if j.val + 2 = N then 0 else (j.val : ZMod p) + 1
  | .adj => if j.val + 3 = N then 1 else 0

abbrev ggTWform {p N : ℕ} (f : GGTWE p N) : GGTWE p N →ₗ[ZMod p] ZMod p :=
  ggDepAform (N := N - 1) f

abbrev ggTWRefl {p N : ℕ} (c f : GGTWE p N) : Module.End (ZMod p) (GGTWE p N) :=
  ggDepARefl (N := N - 1) c f

@[expose] def GGTWIsRefl {p N : ℕ} (s : Module.End (ZMod p) (GGTWE p N)) : Prop :=
  ∃ c f : GGTWE p N, ggTWdot f c = 2 ∧ s = ggTWRefl c f

abbrev GGTWIsTv {p N : ℕ} (g : Module.End (ZMod p) (GGTWE p N)) : Prop :=
  GGDepAIsTv (N := N - 1) g

@[expose] def ggTWInJ (N : ℕ) : GGTWPos → ℕ → Prop
  | .ends, c => 1 ≤ c ∧ c + 3 ≤ N
  | .adj, c => c + 4 ≤ N

instance (N : ℕ) (pos : GGTWPos) (c : ℕ) : Decidable (ggTWInJ N pos c) := by
  cases pos <;> unfold ggTWInJ <;> infer_instance

@[expose] def ggTWPlace : GGTWPos → ℕ → ℕ
  | .ends, c => c - 1
  | .adj, c => c

@[expose] def GGTWPat1 (N : ℕ) (pos : GGTWPos) (c0 : ℕ) (m n : ℤ) : Prop :=
  ggTWInJ N pos c0 ∧
    (((ggTWPlace pos c0 = 0 ∨ ggTWPlace pos c0 + 1 = N - 3) ∧
        ((m = -1 ∧ n = -1) ∨ (m = -1 ∧ n = -2) ∨ (m = -2 ∧ n = -1))) ∨
      (3 ≤ N - 3 ∧ (ggTWPlace pos c0 = 1 ∨ ggTWPlace pos c0 + 2 = N - 3) ∧ m = -1 ∧ n = -1) ∨
      (5 ≤ N - 3 ∧ N - 3 ≤ 7 ∧ (ggTWPlace pos c0 = 2 ∨ ggTWPlace pos c0 + 3 = N - 3) ∧
        m = -1 ∧ n = -1))

@[expose] def GGTWPat2 (N : ℕ) (pos : GGTWPos) (c : ℕ) (c₂ : Option ℕ) : Prop :=
  ggTWInJ N pos c ∧ (ggTWPlace pos c = 0 ∨ ggTWPlace pos c + 1 = N - 3) ∧
    (match c₂ with
      | none => True
      | some c' => ggTWInJ N pos c' ∧
          ((ggTWPlace pos c = 0 ∧ ggTWPlace pos c' + 1 = N - 3) ∨
            (ggTWPlace pos c + 1 = N - 3 ∧ ggTWPlace pos c' = 0)))

@[expose] def GGTWPairs1 (p N : ℕ) (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ)
    (ha αa : GGTWE p N) : Prop :=
  ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
    ggTWdot αa (ggTWh p N c) = (if c = c0 then (m : ZMod p) else 0) ∧
      ggTWdot (ggTWα p N c) ha = (if c = c0 then (n : ZMod p) else 0)

@[expose] def GGTWPairs2 (p N : ℕ) (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1)))
    (ha1 αa1 ha2 αa2 : GGTWE p N) : Prop :=
  (∀ c' : Fin (N - 1), ggTWInJ N pos c'.val →
      ggTWdot αa1 (ggTWh p N c') = (if c' = c then -1 else 0) ∧
        ggTWdot (ggTWα p N c') ha1 = (if c' = c then -1 else 0) ∧
        ggTWdot αa2 (ggTWh p N c') = (if some c' = c₂ then -1 else 0) ∧
        ggTWdot (ggTWα p N c') ha2 = (if some c' = c₂ then -1 else 0)) ∧
    ggTWdot αa1 ha2 = (if c₂ = none then -1 else 0) ∧
      ggTWdot αa2 ha1 = (if c₂ = none then -1 else 0) ∧ ggTWdot αa1 ha1 = 2 ∧ ggTWdot αa2 ha2 = 2

@[expose] def ggTWFrameGens (p N : ℕ) : Set (Module.End (ZMod p) (GGTWE p N)) :=
  Set.range fun i : Fin (N - 1) => ggTWRefl (ggTWh p N i) (ggTWα p N i)

@[expose] def ggTWGens (p N : ℕ) (news : Set (GGTWE p N × GGTWE p N)) :
    Set (Module.End (ZMod p) (GGTWE p N)) :=
  ggTWFrameGens p N ∪ (fun t => ggTWRefl t.1 t.2) '' news

@[expose] def ggTWOGens (p N : ℕ) (pos : GGTWPos) (news : Set (GGTWE p N × GGTWE p N)) :
    Set (Module.End (ZMod p) (GGTWE p N)) :=
  (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
      ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ ∪ (fun t => ggTWRefl t.1 t.2) '' news

@[expose] def ggTWOCentres (p N : ℕ) (pos : GGTWPos) (news : Set (GGTWE p N × GGTWE p N)) :
    Set (GGTWE p N) :=
  (fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} => ggTWh p N i.1) '' Set.univ ∪
    Prod.fst '' news

@[expose] def ggTWRoots {p N : ℕ} (gens : Set (Module.End (ZMod p) (GGTWE p N)))
    (cs : Set (GGTWE p N)) : Set (GGTWE p N) :=
  {v | ∃ w ∈ Submonoid.closure gens, ∃ c ∈ cs, v = w c}

@[expose] def GGTWMovesLine {p N : ℕ} (R : Set (GGTWE p N)) (y : GGTWE p N)
    (s : Module.End (ZMod p) (GGTWE p N)) : Prop :=
  s y = y ∧ ∃ v ∈ R, ∀ w ∈ R, ∀ c d : ZMod p, c ≠ 0 → s v ≠ c • w + d • y

@[expose] def GGTWKill (mode : GGTWMode) (p N : ℕ) (pos : GGTWPos)
    (news : Set (GGTWE p N × GGTWE p N)) (y : GGTWE p N) : Prop :=
  (∃ g ∈ Submonoid.closure (ggTWGens p N news), GGTWIsTv g) ∨
    ∃ s ∈ Submonoid.closure (ggTWGens p N news), GGTWIsRefl s ∧
      match mode with
      | .frame => GGTWMovesLine (ggTWRoots (ggTWFrameGens p N) (Set.range (ggTWh p N)))
          (ggTWx p N) s
      | .other =>
          GGTWMovesLine (ggTWRoots (ggTWOGens p N pos news) (ggTWOCentres p N pos news)) y s

@[expose] def GGTWSurv1 (mode : GGTWMode) (p N : ℕ) : Prop :=
  ∃ (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ) (ha αa : GGTWE p N) (lam mu : ZMod p),
    GGTWPat1 N pos c0.val m n ∧ GGTWPairs1 p N pos c0 m n ha αa ∧ ggTWdot αa ha = 2 ∧
      ggTWdot αa (ggTWx p N) ≠ 0 ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ¬ GGTWKill mode p N pos {(ha, αa)} (lam • ggTWx p N + mu • ggTWz p N pos)

@[expose] def GGTWSurv2 (mode : GGTWMode) (p N : ℕ) : Prop :=
  ∃ (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))) (ha1 αa1 ha2 αa2 : GGTWE p N)
    (lam mu : ZMod p),
    GGTWPat2 N pos c.val (c₂.map Fin.val) ∧ GGTWPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 ∧
      (ggTWdot αa1 (ggTWx p N) ≠ 0 ∨ ggTWdot αa2 (ggTWx p N) ≠ 0) ∧ (lam ≠ 0 ∨ mu ≠ 0) ∧
      ggTWdot αa1 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ggTWdot αa2 (lam • ggTWx p N + mu • ggTWz p N pos) = 0 ∧
      ¬ GGTWKill mode p N pos {(ha1, αa1), (ha2, αa2)} (lam • ggTWx p N + mu • ggTWz p N pos)

@[expose] def GGTWCells (mode : GGTWMode) (p N : ℕ) : Prop :=
  ¬ GGTWSurv1 mode p N ∧ ¬ GGTWSurv2 mode p N

@[expose] def ggRowTwoNodeW1 (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNode p J X ∧ (X.rank = 6 ∨ X.rank = 9)

end CFSG.StandardType
