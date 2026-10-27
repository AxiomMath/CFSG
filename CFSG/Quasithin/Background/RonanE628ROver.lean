module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.RonanE628

open Equiv

@[expose] def a5Code (g : Perm (Fin 5)) : ℕ :=
  (g 0).val + 5 * (g 1).val + 25 * (g 2).val + 125 * (g 3).val + 625 * (g 4).val

@[expose] def a5Digit (x k : ℕ) : ℕ := x / 5 ^ k % 5

@[expose] def a5Comp (x y : ℕ) : ℕ :=
  a5Digit x (a5Digit y 0) + 5 * a5Digit x (a5Digit y 1) + 25 * a5Digit x (a5Digit y 2) +
    125 * a5Digit x (a5Digit y 3) + 625 * a5Digit x (a5Digit y 4)

theorem a5Digit_code (g : Perm (Fin 5)) (k : Fin 5) :
    a5Digit (a5Code g) k.val = (g k).val := by
  have h0 := (g 0).isLt
  have h1 := (g 1).isLt
  have h2 := (g 2).isLt
  have h3 := (g 3).isLt
  have h4 := (g 4).isLt
  fin_cases k <;> simp [a5Digit, a5Code] <;> omega

theorem a5Digit_code_all (g : Perm (Fin 5)) :
    a5Digit (a5Code g) 0 = (g 0).val ∧ a5Digit (a5Code g) 1 = (g 1).val ∧
      a5Digit (a5Code g) 2 = (g 2).val ∧ a5Digit (a5Code g) 3 = (g 3).val ∧
      a5Digit (a5Code g) 4 = (g 4).val :=
  ⟨a5Digit_code g 0, a5Digit_code g 1, a5Digit_code g 2, a5Digit_code g 3, a5Digit_code g 4⟩

theorem a5Code_mul (g h : Perm (Fin 5)) : a5Code (g * h) = a5Comp (a5Code g) (a5Code h) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := a5Digit_code_all h
  unfold a5Comp
  rw [e0, e1, e2, e3, e4, a5Digit_code g (h 0), a5Digit_code g (h 1), a5Digit_code g (h 2),
    a5Digit_code g (h 3), a5Digit_code g (h 4)]
  rfl

theorem a5Code_injective {g h : Perm (Fin 5)} (e : a5Code g = a5Code h) : g = h := by
  ext k
  rw [← a5Digit_code g k, ← a5Digit_code h k, e]

@[expose] def a5Reached (Y : Subgroup (Perm (Fin 5))) (B : ℕ) : Prop :=
  ∀ c : ℕ, B.testBit c = true → ∃ g ∈ Y, a5Code g = c

theorem a5Reached_zero (Y : Subgroup (Perm (Fin 5))) : a5Reached Y 0 := by
  intro c hc
  simp at hc

theorem a5Reached_or (Y : Subgroup (Perm (Fin 5))) {B C : ℕ} (hB : a5Reached Y B)
    (hC : a5Reached Y C) : a5Reached Y (B ||| C) := by
  intro c hc
  rw [Nat.testBit_or, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact hB c hc
  · exact hC c hc

theorem a5Reached_or_pow (Y : Subgroup (Perm (Fin 5))) {B k : ℕ} (hB : a5Reached Y B)
    (hk : ∃ w ∈ Y, a5Code w = k) : a5Reached Y (B ||| 2 ^ k) := by
  intro c hc
  rw [Nat.testBit_or, Bool.or_eq_true] at hc
  rcases hc with hc | hc
  · exact hB c hc
  · rw [Nat.testBit_two_pow] at hc
    have hck : k = c := of_decide_eq_true hc
    subst hck
    exact hk

theorem a5Reached_foldl {α : Type} (Y : Subgroup (Perm (Fin 5))) (f : ℕ → α → ℕ) :
    ∀ (l : List α) (a : ℕ), a5Reached Y a →
      (∀ b x, x ∈ l → a5Reached Y b → a5Reached Y (f b x)) → a5Reached Y (l.foldl f a)
  | [], _, ha, _ => ha
  | x :: l, a, ha, hf =>
    a5Reached_foldl Y f l (f a x) (hf a x (by simp) ha)
      (fun b y hy hb => hf b y (by simp [hy]) hb)

@[expose] def a5Layer (gc E : List ℕ) (L : ℕ) : ℕ :=
  E.foldl (fun acc c => if L.testBit c then gc.foldl (fun a s => a ||| 2 ^ a5Comp c s) acc
    else acc) 0

theorem a5Layer_reached (Y : Subgroup (Perm (Fin 5))) (gc E : List ℕ) {L : ℕ}
    (hL : a5Reached Y L) (hgc : ∀ s ∈ gc, ∃ h ∈ Y, a5Code h = s) :
    a5Reached Y (a5Layer gc E L) := by
  unfold a5Layer
  apply a5Reached_foldl Y _ E 0 (a5Reached_zero Y)
  intro b c _ hb
  split
  · rename_i hc
    obtain ⟨x, hxY, hx⟩ := hL c hc
    apply a5Reached_foldl Y _ gc b hb
    intro b' s hs hb'
    obtain ⟨h, hhY, hh⟩ := hgc s hs
    exact a5Reached_or_pow Y hb' ⟨x * h, Y.mul_mem hxY hhY, by rw [a5Code_mul, hx, hh]⟩
  · exact hb

@[expose] def a5FrontStep (gc E : List ℕ) (BL : ℕ × ℕ) : ℕ × ℕ :=
  let img := a5Layer gc E BL.2
  (BL.1 ||| (img ^^^ (img &&& BL.1)), img ^^^ (img &&& BL.1))

@[expose] def a5FrontRun (gc E : List ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, BL => BL
  | n + 1, BL => a5FrontRun gc E n (a5FrontStep gc E BL)

theorem a5FrontStep_reached (Y : Subgroup (Perm (Fin 5))) (gc E : List ℕ)
    (hgc : ∀ s ∈ gc, ∃ h ∈ Y, a5Code h = s) {B L : ℕ} (hB : a5Reached Y B)
    (hL : a5Reached Y L) :
    a5Reached Y (a5FrontStep gc E (B, L)).1 ∧ a5Reached Y (a5FrontStep gc E (B, L)).2 := by
  have himg := a5Layer_reached Y gc E hL hgc
  have hnew : a5Reached Y (a5Layer gc E L ^^^ (a5Layer gc E L &&& B)) := by
    intro c hc
    rw [Nat.testBit_xor, Nat.testBit_and] at hc
    have hi : (a5Layer gc E L).testBit c = true := by
      revert hc
      cases (a5Layer gc E L).testBit c <;> cases B.testBit c <;> simp
    exact himg c hi
  exact ⟨a5Reached_or Y hB hnew, hnew⟩

theorem a5FrontRun_reached (Y : Subgroup (Perm (Fin 5))) (gc E : List ℕ)
    (hgc : ∀ s ∈ gc, ∃ h ∈ Y, a5Code h = s) :
    ∀ (n : ℕ) (BL : ℕ × ℕ), a5Reached Y BL.1 → a5Reached Y BL.2 →
      a5Reached Y (a5FrontRun gc E n BL).1
  | 0, _, h1, _ => h1
  | n + 1, BL, h1, h2 => by
    have := a5FrontStep_reached Y gc E hgc h1 h2
    exact a5FrontRun_reached Y gc E hgc n (a5FrontStep gc E BL) this.1 this.2

@[expose] def a5EvenCodes : List ℕ :=
  [2930, 1830, 2230, 2410, 2710, 1110, 2790, 1190, 1490, 1670, 2070, 970,
    2426, 2826, 1726, 2886, 586, 1986, 1766, 2566, 366, 2146, 446, 1346,
    2902, 1202, 2102, 2382, 2582, 482, 2642, 542, 742, 1022, 1922, 222,
    1778, 2678, 978, 2758, 558, 1358, 1138, 2538, 238, 1398, 298, 698,
    2154, 1054, 1454, 1634, 1934, 334, 2014, 414, 714, 894, 1294, 194]

@[expose] def a5DtA (p : Fin 5) : Perm (Fin 5) := swap (p + 1) (p + 2) * swap (p + 3) (p + 4)

@[expose] def a5DtB (p : Fin 5) : Perm (Fin 5) := swap (p + 1) (p + 3) * swap (p + 2) (p + 4)

@[expose] def a5DtC (p : Fin 5) : Perm (Fin 5) := swap (p + 1) (p + 4) * swap (p + 2) (p + 3)

@[expose] def a5Gens (p : Fin 5) (σ : Perm (Fin 5)) : List (Perm (Fin 5)) :=
  [a5DtA p, a5DtB p, a5DtC p, σ, σ⁻¹]

theorem a5_dt_facts : ∀ p : Fin 5, ∀ g ∈ [a5DtA p, a5DtB p, a5DtC p],
    g * g = 1 ∧ Perm.sign g = 1 ∧ g p = p := by
  decide +kernel

theorem a5_even_codes : ∀ g : Perm (Fin 5), Perm.sign g = 1 → a5Code g ∈ a5EvenCodes := by
  decide +kernel

theorem a5_closure_check : ∀ p : Fin 5, ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ p ≠ p →
    ∀ c ∈ a5EvenCodes, (a5FrontRun ((a5Gens p σ).map a5Code) a5EvenCodes 6
      (2 ^ a5Code 1, 2 ^ a5Code 1)).1.testBit c = true := by
  decide +kernel

theorem a5_sound (Y : Subgroup (Perm (Fin 5))) (gp : List (Perm (Fin 5)))
    (hgp : ∀ h ∈ gp, h ∈ Y) (E : List ℕ)
    (hE : ∀ g : Perm (Fin 5), Perm.sign g = 1 → a5Code g ∈ E)
    (hcheck : ∀ c ∈ E, (a5FrontRun (gp.map a5Code) E 6
      (2 ^ a5Code 1, 2 ^ a5Code 1)).1.testBit c = true) :
    ∀ g : Perm (Fin 5), Perm.sign g = 1 → g ∈ Y := by
  intro g hg
  have hgc : ∀ s ∈ gp.map a5Code, ∃ h ∈ Y, a5Code h = s := by
    intro s hs
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hs
    exact ⟨h, hgp h hh, rfl⟩
  have h1 : a5Reached Y (2 ^ a5Code 1) := by
    intro c hc
    rw [Nat.testBit_two_pow] at hc
    have : a5Code 1 = c := of_decide_eq_true hc
    exact ⟨1, Y.one_mem, this⟩
  have hR := a5FrontRun_reached Y _ E hgc 6 (2 ^ a5Code 1, 2 ^ a5Code 1) h1 h1
  obtain ⟨x, hxY, hx⟩ := hR (a5Code g) (hcheck _ (hE g hg))
  rw [a5Code_injective hx] at hxY
  exact hxY

theorem a5_overgroup (p : Fin 5) (Y : Subgroup (Equiv.Perm (Fin 5)))
    (hk : ∀ g : Equiv.Perm (Fin 5), g * g = 1 → Equiv.Perm.sign g = 1 → g p = p → g ∈ Y)
    {σ : Equiv.Perm (Fin 5)} (hσY : σ ∈ Y) (hsign : Equiv.Perm.sign σ = 1) (hσp : σ p ≠ p) :
    ∀ g : Equiv.Perm (Fin 5), Equiv.Perm.sign g = 1 → g ∈ Y := by
  have hdt : ∀ g ∈ [a5DtA p, a5DtB p, a5DtC p], g ∈ Y := fun g hg => by
    obtain ⟨e1, e2, e3⟩ := a5_dt_facts p g hg
    exact hk g e1 e2 e3
  refine a5_sound Y (a5Gens p σ) ?_ a5EvenCodes a5_even_codes
    (a5_closure_check p σ hsign hσp)
  intro h hh
  simp only [a5Gens, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hh
  rcases hh with h' | h' | h' | h' | h' <;> subst h'
  · exact hdt _ (by simp)
  · exact hdt _ (by simp)
  · exact hdt _ (by simp)
  · exact hσY
  · exact Y.inv_mem hσY

end CFSG.Quasithin.RonanE628
