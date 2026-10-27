module

public import CFSG.Sporadic.Schreier.ONPermArr

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Certificates

variable {n : ℕ}

@[expose] def wordStrong (orig : List (Equiv.Perm (Fin n))) (W : Array (List ℤ)) :
    ℕ → Equiv.Perm (Fin n)
  | j =>
    if hj : j < orig.length then orig[j]
    else Quiver.SchreierGraph.evalWord (fun h : Fin j => wordStrong orig W h.val)
      (ptoLetters j W[j]!)
termination_by j => j
decreasing_by exact h.isLt

theorem wordStrong_of_lt (orig : List (Equiv.Perm (Fin n))) (W : Array (List ℤ)) {j : ℕ}
    (hj : j < orig.length) : wordStrong orig W j = orig[j] := by
  rw [wordStrong, dite_eq_left hj]

theorem wordStrong_of_ge (orig : List (Equiv.Perm (Fin n))) (W : Array (List ℤ)) {j : ℕ}
    (hj : orig.length ≤ j) :
    wordStrong orig W j = Quiver.SchreierGraph.evalWord (fun h : Fin j => wordStrong orig W h.val)
      (ptoLetters j W[j]!) := by
  rw [wordStrong, dite_eq_right (by omega : ¬ j < orig.length)]

@[expose] def RawSchreierDatum.ofWords (n : ℕ) (hn : 1 ≤ n) (orig : List (Equiv.Perm (Fin n)))
    (W : Array (List ℤ)) (hk : orig.length ≤ W.size) (base : List (Fin n)) (hb : base.Nodup) :
    RawSchreierDatum n where
  degree_pos := hn
  originalCount := orig.length
  strongCount := W.size
  baseCount := base.length
  originalCount_le := hk
  original := ⟨orig.toArray, by simp⟩
  strong := Vector.ofFn fun j : Fin W.size => wordStrong orig W j
  base := ⟨base.toArray, by simp⟩
  base_distinct := by simpa using hb
  derivation j _ := ptoLetters j.val W[j.val]!

section

variable {hn : 1 ≤ n} {orig : List (Equiv.Perm (Fin n))} {W : Array (List ℤ)}
  {hk : orig.length ≤ W.size} {base : List (Fin n)} {hb : base.Nodup}

theorem ofWords_strong_get (j : Fin (RawSchreierDatum.ofWords n hn orig W hk base hb).strongCount) :
    (RawSchreierDatum.ofWords n hn orig W hk base hb).strong.get j = wordStrong orig W j := by
  simp [RawSchreierDatum.ofWords, Vector.get]
  rfl

theorem ofWords_original_get
    (j : Fin (RawSchreierDatum.ofWords n hn orig W hk base hb).originalCount) :
    (RawSchreierDatum.ofWords n hn orig W hk base hb).original.get j =
      orig[j.val]'(by simpa [RawSchreierDatum.ofWords] using j.isLt) := by
  simp [RawSchreierDatum.ofWords, Vector.get]
  rfl

theorem ofWords_base_get (i : Fin (RawSchreierDatum.ofWords n hn orig W hk base hb).baseCount) :
    (RawSchreierDatum.ofWords n hn orig W hk base hb).base.get i =
      base[i.val]'(by simpa [RawSchreierDatum.ofWords] using i.isLt) := by
  simp [RawSchreierDatum.ofWords, Vector.get]
  rfl

theorem ofWords_original_toList :
    (RawSchreierDatum.ofWords n hn orig W hk base hb).original.toList = orig := by
  simp [RawSchreierDatum.ofWords]

theorem ofWords_initial :
    ∀ j : Fin (RawSchreierDatum.ofWords n hn orig W hk base hb).originalCount,
      (RawSchreierDatum.ofWords n hn orig W hk base hb).strong.get (Fin.castLE
        (RawSchreierDatum.ofWords n hn orig W hk base hb).originalCount_le j) =
      (RawSchreierDatum.ofWords n hn orig W hk base hb).original.get j := by
  intro j
  rw [ofWords_strong_get, ofWords_original_get]
  exact wordStrong_of_lt orig W _

theorem ofWords_words :
    ∀ (j : Fin (RawSchreierDatum.ofWords n hn orig W hk base hb).strongCount)
      (hj : (RawSchreierDatum.ofWords n hn orig W hk base hb).originalCount ≤ j.val),
      (RawSchreierDatum.ofWords n hn orig W hk base hb).strong.get j =
        (RawSchreierDatum.ofWords n hn orig W hk base hb).derivationValue j hj := by
  intro j hj
  rw [ofWords_strong_get, RawSchreierDatum.derivationValue, schreierWordValue,
    wordStrong_of_ge orig W hj]
  congr 1
  funext h
  rw [ofWords_strong_get]

end

end CFSG.ONSchreier
