module

public import CFSG.LocalAnalysis.StandardType.GGResIConclX
public import CFSG.LocalAnalysis.StandardType.GGResIICert
public import CFSG.LocalAnalysis.StandardType.GGResIWStar
public import CFSG.LocalAnalysis.StandardType.GGResIWitness

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

inductive GGResLetter where
  | f (i : ℕ)
  | j (k : ℕ)
  deriving DecidableEq

inductive GGCellWitI (n : ℕ) where
  | tv (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (l₀ z : Fin (n + 2))
  | tvk (t₁ t₂ : Fin (n + 1) × List (Fin (n + 1))) (o₀ l : Fin (n + 1))
  | tri (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1))
  | triple (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1))
  | gram (t : Fin (n + 1) × List (Fin (n + 1))) (j' : Fin (n + 1))
  | wstar (typ : GGWTypeI) (ts : List (Fin (n + 1) × List (Fin (n + 1)))) (d : List ℕ)
      (lam : List (List ℕ)) (gw : List (List ℕ))
  | std (typ : GGWTypeI) (σ : List (Fin (n + 1)))
  | nospan (z₁ z₂ : List ℕ) (l₁ l₂ : Fin (n + 1))
  | q8 (O : List (List ℕ)) (ci : List (List (ℕ × ℕ))) (t : Fin (n + 1) × List (Fin (n + 1)))
      (x₀ : List ℕ)
  | line (T : GGResLineJType) (jl : List (Fin n)) (K : List (List ℕ)) (z w : List ℕ)
      (F : List (Fin (n + 1) × List (Fin (n + 1)))) (gens : List (List GGResLetter))
      (elts : List (List ℕ))
  | o2a (T : GGResLineJType) (jl : List (Fin n)) (K : List (List ℕ)) (z w : List ℕ)
      (F : List (Fin (n + 1) × List (Fin (n + 1)))) (gens : List (List GGResLetter))
      (elts : List (List ℕ))
  | o2b

section Check

variable {R : Type} [CommRing R] [DecidableEq R] {n : ℕ}

@[expose] def ggFMat {N : ℕ} (T : Fin N → Vector R (N + 1)) (ws : List (Fin N)) : List (List R) :=
  (List.finRange N).map fun l => (List.finRange N).map fun m =>
    (ggFWord T ws (ggFUnit l.castSucc)).get m.castSucc

@[expose] def ggFRefMat {N : ℕ} (T : Fin N → Vector R (N + 1)) (t : Fin N × List (Fin N)) :
    List (List R) :=
  (fun (c : Vector R N) (H : Vector R (N + 1)) => (List.finRange N).map fun l =>
    (fun a : R => (List.finRange N).map fun m => (if l = m then 1 else 0) - a * H.get m.castSucc)
      (ggFDualAt T c l)) (ggFC T t) (ggFH T t)

@[expose] def ggConjWord {N : ℕ} (t : Fin N × List (Fin N)) : List (Fin N) :=
  t.2 ++ t.1 :: t.2.reverse

@[expose] def ggFVec (z : List ℕ) : Vector R (n + 2) :=
  Vector.ofFn fun l => (z.getD l.val 0 : R)

@[expose] def ggTriLiftB (a : Fin 3 → Fin 3 → R) : Bool :=
  (List.finRange 3).all (fun i => (List.finRange 3).all fun k => decide ((a i k = 0) ↔ (a k i = 0))) &&
  (List.range 5).any fun P01 => (List.range 5).any fun P02 => (List.range 5).any fun P12 =>
    (List.range 17).any fun τ' =>
      (fun τ : ℤ => decide ((P01 : R) = a 0 1 * a 1 0) && decide ((P02 : R) = a 0 2 * a 2 0) &&
        decide ((P12 : R) = a 1 2 * a 2 1) && decide ((τ : R) = a 0 1 * a 1 2 * a 2 0) &&
        decide ((τ : R) = a 0 2 * a 2 1 * a 1 0) &&
        decide (τ * τ = (P01 : ℤ) * P02 * P12) &&
        decide (0 ≤ 4 - (P01 : ℤ) - P02 - P12 + τ)) ((τ' : ℤ) - 8)

@[expose] def ggFTriMat (T : Fin (n + 1) → Vector R (n + 2)) (t : Fin (n + 1) × List (Fin (n + 1)))
    (j' : Fin (n + 1)) : Fin 3 → Fin 3 → R :=
  fun i k => ![![(T t.1).get t.1.castSucc, (T t.1).get j'.castSucc, ggFA T t t.1],
    ![(T j').get t.1.castSucc, (T j').get j'.castSucc, ggFA T t j'],
    ![ggFDualAt T (ggFC T t) t.1, ggFDualAt T (ggFC T t) j',
      ggFDualAt T (ggFC T t) t.1 * 0 + 2]] i k

@[expose] def ggResLetterWord (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) : GGResLetter → List (Fin (n + 1))
  | .f i => ggConjWord (F.getD i (0, []))
  | .j k => [(jl.getD k d).castSucc]

@[expose] def ggResLettersWord (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) (ws : List GGResLetter) : List (Fin (n + 1)) :=
  (ws.map (ggResLetterWord F jl d)).flatten

@[expose] def ggGensWord (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n))
    (d : Fin n) (gens : List (List GGResLetter)) (ws : List ℕ) : List (Fin (n + 1)) :=
  (ws.map fun i => ggResLettersWord F jl d (gens.getD i [])).flatten

@[expose] def ggResLetterOk (F : List (Fin (n + 1) × List (Fin (n + 1)))) (jl : List (Fin n)) :
    GGResLetter → Bool
  | .f i => decide (i < F.length)
  | .j k => decide (k < jl.length)

@[expose] def ggResLineCheck (T : Fin (n + 1) → Vector R (n + 2)) (C : Matrix (Fin n) (Fin n) ℤ)
    (ib : Fin n) (allA : Bool) (TT : GGResLineJType) (jl : List (Fin n)) (K : List (List ℕ))
    (z w : List ℕ) (F : List (Fin (n + 1) × List (Fin (n + 1)))) (gens : List (List GGResLetter))
    (elts : List (List ℕ)) : Bool :=
  decide (jl.length = TT.rank) && decide (jl.Nodup) && jl.all (fun j => decide (j ≠ ib)) &&
  (List.finRange n).all (fun j => decide (j = ib) || decide (j ∈ jl)) &&
  (List.finRange TT.rank).all (fun k => (List.finRange TT.rank).all fun l =>
    decide (C (jl.getD k.val ib) (jl.getD l.val ib) = TT.cartan k l)) &&
  (List.finRange TT.rank).all (fun a => (List.finRange TT.rank).all fun c =>
    decide (∑ l : Fin (n + 1), (T (jl.getD a.val ib).castSucc).get l.castSucc *
      ((K.getD l.val []).getD c.val 0 : R) = if a = c then 1 else 0)) &&
  jl.all (fun j => decide (ggFDot (T j.castSucc) (ggFVec z) = 0) &&
    decide (ggFDot (T j.castSucc) (ggFVec w) = 0)) &&
  (List.finRange n).any (fun i => decide (ggFDot (T i.castSucc) (ggFVec z) ≠ 0)) &&
  !F.isEmpty &&
  F.all (fun t => (allA || decide (t.1 ≠ Fin.last n)) &&
    decide (ggFRootAt T (ggFC T t) (ggFVec z) = 0) && decide (ggFRootAt T (ggFC T t) (ggFVec w) ≠ 0) &&
    jl.any fun j => decide (ggFMat T (ggConjWord t ++ [j.castSucc]) ≠
      ggFMat T (j.castSucc :: ggConjWord t))) &&
  gens.all (fun ws => ws.all (ggResLetterOk F jl)) &&
  decide ((elts.map fun e => ggFMat T (ggGensWord F jl ib gens e)).Nodup) &&
  elts.any (fun e => decide (ggFMat T (ggGensWord F jl ib gens e) = ggFMat T [])) &&
  (List.range gens.length).all (fun i => elts.all fun e =>
    (elts.any fun e' => decide (ggFMat T (ggGensWord F jl ib gens (i :: e)) =
      ggFMat T (ggGensWord F jl ib gens e'))) &&
    (elts.any fun e' => decide (ggFMat T ((ggResLettersWord F jl ib (gens.getD i [])).reverse ++
      ggGensWord F jl ib gens e) = ggFMat T (ggGensWord F jl ib gens e')))) &&
  decide (TT.bad ∣ elts.length)

end Check

@[expose] def ggFNotProp {R : Type} [CommRing R] [DecidableEq R] {N : ℕ} (H z : Vector R (N + 1)) :
    Bool :=
  (List.finRange N).any fun l => (List.finRange N).any fun m =>
    decide (H.get l.castSucc * z.get m.castSucc - H.get m.castSucc * z.get l.castSucc ≠ 0)

@[expose] def ggQ8Check {R : Type} [CommRing R] [DecidableEq R] {n : ℕ}
    (T : Fin (n + 1) → Vector R (n + 2)) (O : List (List ℕ))
    (ci : List (List (ℕ × ℕ))) (t : Fin (n + 1) × List (Fin (n + 1))) (x₀ : List ℕ) : Bool :=
  (List.finRange n).all (fun i => decide (ggFDot (T i.castSucc) (ggFVec x₀) = 0)) &&
  (List.finRange (n + 1)).any (fun l => decide ((ggFVec x₀ : Vector R (n + 2)).get l.castSucc ≠ 0)) &&
  decide (n ≤ O.length) &&
  (List.finRange n).all (fun k =>
    decide (ggFVec (O.getD k.val []) = ggFUnit (R := R) k.castSucc.castSucc)) &&
  (List.finRange n).all (fun k => (List.finRange O.length).all fun i =>
    (fun js : ℕ × ℕ => decide (js.1 < O.length) && (List.finRange (n + 2)).all fun l =>
      decide ((ggFRefl T k.castSucc (ggFVec (O.getD i.val []))).get l =
        (js.2 : R) * (ggFVec (O.getD js.1 []) : Vector R (n + 2)).get l))
    ((ci.getD k.val []).getD i.val (0, 0))) &&
  decide (t.1.val < n) && decide (ggFRootAt T (ggFC T t) (ggFVec x₀) = 0) &&
  (List.finRange O.length).all (fun j => ggFNotProp (ggFH T t) (ggFVec (O.getD j.val [])))

@[expose] def ggO2Bond {p : ℕ} (e₁ e₂ : ℤ) (u v : ZMod p) : Bool :=
  (decide (e₂ = -1) && decide (e₁ = -2) && decide (u = 1) && decide (v = 2)) ||
    (decide (e₂ = -2) && decide (e₁ = -1) && decide (u = 2) && decide (v = 1))

@[expose] def ggO2aB (p : ℕ) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (u v : ZMod p) : Bool :=
  decide (p = 3) && (List.finRange n).any fun j₀ => (List.finRange n).any fun j₁ =>
    decide (j₀ ≠ ib) && decide (j₁ ≠ ib) && decide (j₀ ≠ j₁) &&
    (List.finRange n).all (fun i => decide (i = j₀ ∨ i = j₁ ∨ i = ib)) &&
    decide (C j₀ j₁ = -1) && decide (C j₁ j₀ = -1) && decide (C j₀ ib = -1) &&
    decide (C ib j₀ = -1) && decide (C j₁ ib = 0) && decide (C ib j₁ = 0) &&
    decide (ic = j₀ ∨ ic = j₁) && ggO2Bond e₁ e₂ u v

@[expose] def ggO2bB (p : ℕ) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (u v : ZMod p) : Bool :=
  decide (p = 3) && (List.finRange n).any fun j₁ => (List.finRange n).any fun j₂ =>
    decide (ic ≠ ib) && decide (j₁ ≠ ib) && decide (j₂ ≠ ib) && decide (ic ≠ j₁) &&
    decide (j₁ ≠ j₂) && decide (ic ≠ j₂) &&
    (List.finRange n).all (fun i => decide (i = ic ∨ i = j₁ ∨ i = j₂ ∨ i = ib)) &&
    decide (C ic j₁ = -1) && decide (C j₁ ic = -1) && decide (C j₁ j₂ = -1) &&
    decide (C j₂ j₁ = -1) && decide (C ic j₂ = 0) && decide (C j₂ ic = 0) &&
    decide (C j₁ ib = -1) && decide (C ib j₁ = -1) && decide (C ic ib = 0) &&
    decide (C ib ic = 0) && decide (C j₂ ib = 0) && decide (C ib j₂ = 0) && ggO2Bond e₁ e₂ u v

section CellCheck

variable (q : ℕ) [NeZero q] {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)

@[expose] def ggCellWitCheckI (u v : ZMod q) (w : GGCellWitI n) : Bool :=
  (fun T : Fin (n + 1) → Vector (ZMod q) (n + 2) => match w with
  | .tv t₁ t₂ l₀ z =>
    (fun H₁ H₂ : Vector (ZMod q) (n + 2) =>
      (List.finRange (n + 1)).all (fun l =>
          decide (H₂.get l₀ * H₁.get l.castSucc - H₁.get l₀ * H₂.get l.castSucc = 0)) &&
        decide (H₁.get l₀ ≠ 0) && decide (H₂.get l₀ ≠ 0) &&
        decide (H₁.get l₀ * ggFRootAt T (ggFC T t₁) (ggFUnit z) -
          H₂.get l₀ * ggFRootAt T (ggFC T t₂) (ggFUnit z) ≠ 0))
      (ggFH T t₁) (ggFH T t₂)
  | .tvk t₁ t₂ o₀ l =>
    (fun c₁ c₂ : Vector (ZMod q) (n + 1) =>
      (List.finRange (n + 1)).all (fun o =>
          decide (ggFDualAt T c₂ o₀ * ggFDualAt T c₁ o - ggFDualAt T c₁ o₀ * ggFDualAt T c₂ o = 0)) &&
        decide (ggFDualAt T c₂ o₀ ≠ 0) && decide (ggFDualAt T c₁ o₀ ≠ 0) &&
        decide (ggFDualAt T c₁ o₀ * (ggFH T t₁).get l.castSucc -
          ggFDualAt T c₂ o₀ * (ggFH T t₂).get l.castSucc ≠ 0))
      (ggFC T t₁) (ggFC T t₂)
  | .tri t j' =>
    inJ ib t.1 && inJ ib j' &&
      (fun P : ZMod q => decide (P ≠ 0) && decide (P ≠ 1) && decide (P ≠ 2) && decide (P ≠ 3) &&
        decide (P ≠ 4)) (ggFA T t j' * ggFDualAt T (ggFC T t) j')
  | .triple t j' =>
    inJ ib t.1 && inJ ib j' && decide (5 ≤ q) &&
      (fun a : Fin 3 → Fin 3 → ZMod q => decide (a 0 1 * a 1 2 * a 2 0 ≠ a 0 2 * a 2 1 * a 1 0))
        (ggFTriMat T t j')
  | .gram t j' =>
    inJ ib t.1 && inJ ib j' && decide (5 ≤ q) &&
      (fun a : Fin 3 → Fin 3 → ZMod q =>
        ((decide (a 1 2 * a 2 1 ≠ 0) && decide (a 1 2 * a 2 1 ≠ 4)) ||
          decide (a 0 1 * a 1 2 * a 2 0 ≠ a 0 2 * a 2 1 * a 1 0) ||
          (decide (a 1 2 = 0) && decide (a 2 1 ≠ 0)) || (decide (a 1 2 ≠ 0) && decide (a 2 1 = 0))) &&
          !ggTriLiftB a)
        (ggFTriMat T t j')
  | .wstar typ ts d lam gw =>
    (fun (t : Fin (n + 1) → Fin (n + 1) × List (Fin (n + 1))) (dd : Fin (n + 1) → ZMod q)
        (ll : Fin (n + 1) → Fin (n + 1) → ZMod q) =>
      ggWTypeOk typ (n + 1) &&
      (List.finRange (n + 1)).all (fun k => (gw.getD k.val []).all (fun m => decide (m < n + 1)) &&
        decide (ggFMat T [k] = ggFMat T ((gw.getD k.val []).flatMap fun m =>
          ggConjWord (ts.getD m (0, []))))) &&
      (List.finRange (n + 1)).all (fun i => decide (dd i ≠ 0)) &&
      (List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun j =>
        decide (dd i * ggFRootAt T (ggFC T (t j)) (ggFH T (t i)) =
          dd j * (ggWCartanI typ (n + 1) i j : ZMod q))) &&
      (List.finRange (n + 1)).all (fun i => (List.finRange (n + 1)).all fun o =>
        decide (∑ l : Fin (n + 1), (ggFH T (t i)).get l.castSucc * ll l o =
          if i = o then 1 else 0)))
    (fun i => ts.getD i.val (0, [])) (fun i => (d.getD i.val 0 : ZMod q))
    (fun o i => ((lam.getD o.val []).getD i.val 0 : ZMod q))
  | .std typ σ =>
    decide (u = 0) && ggWTypeOk typ (n + 1) && decide (σ.length = n + 1) && decide σ.Nodup &&
      (List.finRange (n + 1)).all (fun k => (List.finRange (n + 1)).all fun l =>
        decide (ggGlueI C ib ic e₁ e₂ k l =
          ggWCartanI typ (n + 1) (σ.getD k.val 0) (σ.getD l.val 0)))
  | .nospan z₁ z₂ l₁ l₂ =>
    (List.finRange n).all (fun i => decide (ggFDot (T i.castSucc) (ggFVec z₁) = 0) &&
      decide (ggFDot (T i.castSucc) (ggFVec z₂) = 0)) &&
      decide ((ggFVec z₁ : Vector (ZMod q) (n + 2)).get l₁.castSucc *
          (ggFVec z₂ : Vector (ZMod q) (n + 2)).get l₂.castSucc -
        (ggFVec z₁ : Vector (ZMod q) (n + 2)).get l₂.castSucc *
          (ggFVec z₂ : Vector (ZMod q) (n + 2)).get l₁.castSucc ≠ 0)
  | .q8 O ci t x₀ => decide (q = 3) && ggQ8Check T O ci t x₀
  | .line TT jl K z w F gens elts =>
    decide (q = 3) && ggResLineCheck T C ib false TT jl K z w F gens elts
  | .o2a TT jl K z w F gens elts =>
    ggO2aB q C ib ic e₁ e₂ u v && ggResLineCheck T C ib true TT jl K z w F gens elts
  | .o2b => ggO2bB q C ib ic e₁ e₂ u v)
  (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v)

@[expose] def ggCellAtI (wits : List (ℕ × ℕ × GGCellWitI n)) (u v : ZMod q) : Bool :=
  match wits.find? (fun w => w.1 == u.val && w.2.1 == v.val) with
  | some w => ggCellWitCheckI q C ib ic e₁ e₂ u v w.2.2
  | none => false

@[expose] def GGCellCheckI (wits : List (ℕ × ℕ × GGCellWitI n)) : Prop :=
  ∀ u v : ZMod q, ggCellAtI q C ib ic e₁ e₂ wits u v = true

end CellCheck

end CFSG.StandardType
