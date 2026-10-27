module

public import CFSG.Quasithin.EmptyFaithful.ModHPerm
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.Quasithin.ModH

open CFSG.Quasithin.ModG

@[expose] def chi (B : Finset (Fin 12)) : List Bool := List.ofFn fun i : Fin 12 => decide (i ∈ B)

theorem chi_length (B : Finset (Fin 12)) : (chi B).length = 12 := by simp [chi]

theorem chi_getD (B : Finset (Fin 12)) (i : Fin 12) : (chi B).getD i.val false = decide (i ∈ B) := by
  rw [chi, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem chi_inj {B B' : Finset (Fin 12)} (h : chi B = chi B') : B = B' := by
  ext i
  have h1 := congrArg (fun l => l.getD i.val false) h
  rw [chi_getD, chi_getD] at h1
  simpa using h1

@[expose] def actL (c : ℕ) (l : List Bool) : List Bool :=
  (List.range 12).map fun j => (List.range 12).any fun i => l.getD i false && Nat.beq (dg c i - 1) j

theorem chi_image (f : Equiv.Perm (Fin 12)) (B : Finset (Fin 12)) :
    chi (B.image f) = actL (pkn 12 f) (chi B) := by
  apply List.ext_getElem
  · simp [chi, actL]
  · intro j h1 h2
    have hj : j < 12 := by simpa [chi] using h1
    simp only [chi, actL, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    have key : (⟨j, hj⟩ : Fin 12) ∈ B.image f ↔
        ((List.range 12).any fun i => (List.ofFn fun i : Fin 12 => decide (i ∈ B)).getD i false &&
          Nat.beq (dg (pkn 12 f) i - 1) j) = true := by
      rw [List.any_eq_true, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hf⟩
        refine ⟨i.val, List.mem_range.2 i.isLt, ?_⟩
        have h1 : (List.ofFn fun i : Fin 12 => decide (i ∈ B)).getD i.val false = true := by
          have := chi_getD B i
          simpa [chi, hi] using this
        have h2 : dg (pkn 12 f) i.val - 1 = j := by
          have := dg_pkn (by norm_num) f i.val i.isLt
          rw [this]
          have : (f ⟨i.val, i.isLt⟩).val = j := by
            have := congrArg Fin.val hf
            simpa using this
          omega
        rw [h1]
        simp [h2]
      · rintro ⟨i, hi, h⟩
        have hi12 : i < 12 := List.mem_range.1 hi
        refine ⟨⟨i, hi12⟩, ?_, ?_⟩
        · have h' := h
          simp only [Bool.and_eq_true] at h'
          have := chi_getD B ⟨i, hi12⟩
          have h3 : (List.ofFn fun i : Fin 12 => decide (i ∈ B)).getD i false = true := h'.1
          simp only [chi] at this
          rw [this] at h3
          simpa using h3
        · have h' := h
          simp only [Bool.and_eq_true] at h'
          have h4 : dg (pkn 12 f) i - 1 = j := Nat.eq_of_beq_eq_true h'.2
          have := dg_pkn (by norm_num) f i hi12
          rw [this] at h4
          apply Fin.ext
          simp only
          omega
    by_cases hmem : (⟨j, hj⟩ : Fin 12) ∈ B.image f
    · rw [decide_eq_true hmem]
      exact (key.1 hmem).symm
    · rw [decide_eq_false hmem]
      cases h : ((List.range 12).any fun i => (List.ofFn fun i : Fin 12 => decide (i ∈ B)).getD i false &&
          Nat.beq (dg (pkn 12 f) i - 1) j)
      · rfl
      · exact absurd (key.2 h) hmem

@[expose] def bn : List Bool → ℕ
  | [] => 0
  | b :: l => (if b then 1 else 0) + 2 * bn l

theorem bn_inj : ∀ {l l' : List Bool}, l.length = l'.length → bn l = bn l' → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd h (by simp)
  | _ :: _, [], h, _ => absurd h (by simp)
  | b :: l, b' :: l', h, e => by
    have hl : l.length = l'.length := by simpa using h
    have e' : (if b then 1 else 0) + 2 * bn l = (if b' then 1 else 0) + 2 * bn l' := e
    have hb : b = b' := by
      cases b <;> cases b' <;> simp at e' ⊢ <;> omega
    have hbn : bn l = bn l' := by
      subst hb
      omega
    rw [hb, bn_inj hl hbn]

@[expose] def allBools : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap fun l => [false :: l, true :: l]

theorem mem_allBools : ∀ (n : ℕ) (l : List Bool), l.length = n → l ∈ allBools n
  | 0, [], _ => by simp [allBools]
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, [], h => absurd h (by simp)
  | n + 1, b :: l, h => by
    have hl : l.length = n := by simpa using h
    simp only [allBools, List.mem_flatMap]
    exact ⟨l, mem_allBools n l hl, by cases b <;> simp⟩

@[expose] def popL (l : List Bool) : ℕ := (l.map fun b => if b then 1 else 0).sum

theorem popL_chi (B : Finset (Fin 12)) : popL (chi B) = B.card := by
  simp only [popL, chi, List.map_ofFn, List.sum_ofFn, Function.comp_def, decide_eq_true_eq]
  rw [Finset.sum_boole]
  simp

end CFSG.Quasithin.ModH
