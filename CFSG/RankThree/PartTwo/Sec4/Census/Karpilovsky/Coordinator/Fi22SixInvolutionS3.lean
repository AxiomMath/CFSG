module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22S3

open CFSG.Sporadic.Presentation.Fi22Exact

abbrev S3 := Equiv.Perm (Fin 3)

def codeS (g : S3) : ℕ := (g 0).val + 3 * (g 1).val + 9 * (g 2).val

def p3 (n : ℕ) : ℕ := if n = 0 then 1 else if n = 1 then 3 else 9

def mulC (x y : ℕ) : ℕ :=
  (x / p3 (y % 3) % 3) + 3 * (x / p3 (y / 3 % 3) % 3) + 9 * (x / p3 (y / 9 % 3) % 3)

def invC (x : ℕ) : ℕ :=
  (if x % 3 = 0 then 0 else if x / 3 % 3 = 0 then 1 else 2) +
  3 * (if x % 3 = 1 then 0 else if x / 3 % 3 = 1 then 1 else 2) +
  9 * (if x % 3 = 2 then 0 else if x / 3 % 3 = 2 then 1 else 2)

theorem codeS_mul : ∀ g h : S3, codeS (g * h) = mulC (codeS g) (codeS h) := by decide
theorem codeS_inv : ∀ g : S3, codeS g⁻¹ = invC (codeS g) := by decide
theorem codeS_one : codeS 1 = 21 := by decide
theorem codeS_inj : ∀ g h : S3, codeS g = codeS h → g = h := by decide

def invCodes : List ℕ := [21, 19, 5, 15]

theorem mem_invCodes : ∀ g : S3, g * g = 1 → codeS g ∈ invCodes := by decide

def relSub : List (List ℕ) := [[9, 11, 8, 10, 8, 11], [3, 11, 5, 2, 4, 10, 2, 11, 5, 10], [3, 11, 7, 2, 6, 10, 2, 11, 7, 10], [3, 11, 9, 2, 8, 10, 2, 11, 9, 10], [7, 11, 5, 0, 4, 10, 6, 11, 5, 1, 4, 10], [3, 5, 11, 0, 10, 4, 2, 5, 11, 1, 10, 4], [11, 5, 11, 0, 10, 4, 10, 1, 11, 5, 10, 0], [3, 9, 11, 0, 10, 8, 2, 9, 11, 1, 10, 8], [5, 9, 11, 0, 10, 8, 4, 9, 11, 1, 10, 8]]

def codesOf (w : List (Fin 6 × Bool)) : List ℕ := w.map fun p => 2 * p.1.val + if p.2 then 0 else 1

theorem relSub_mem : ∀ w ∈ relSub, w ∈ wsF.map codesOf := by decide +kernel

def evV (V : ℕ → ℕ) (w : List ℕ) : ℕ :=
  (w.map fun c => if c % 2 = 0 then V (c / 2) else invC (V (c / 2))).foldl mulC 21

def look : List (ℕ × ℕ) → ℕ → ℕ
  | [], _ => 21
  | (j, v) :: t, i => if i = j then v else look t i

def usable (as : List (ℕ × ℕ)) (w : List ℕ) : Bool := w.all fun c => as.any fun p => p.1 == c / 2

def okA (as : List (ℕ × ℕ)) : Bool :=
  relSub.all fun w => !usable as w || evV (look as) w == 21

def go : List ℕ → List (ℕ × ℕ) → Bool
  | [], as => as.all fun p => p.2 == (as.headD (0, 0)).2
  | i :: rest, as => invCodes.all fun a => !okA ((i, a) :: as) || go rest ((i, a) :: as)

theorem go_true : go [4, 5, 1, 0, 2, 3] [] = true := by decide +kernel


theorem evV_congr {V V' : ℕ → ℕ} {w : List ℕ} (h : ∀ c ∈ w, V (c / 2) = V' (c / 2)) :
    evV V w = evV V' w := by
  unfold evV
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [h c hc]

theorem look_eq {G : ℕ → ℕ} {as : List (ℕ × ℕ)} (hcons : ∀ p ∈ as, G p.1 = p.2) {i : ℕ}
    (hi : ∃ p ∈ as, p.1 = i) : look as i = G i := by
  induction as with
  | nil => obtain ⟨p, hp, _⟩ := hi; simp at hp
  | cons q t ih =>
    obtain ⟨j, v⟩ := q
    unfold look
    split_ifs with h
    · have := hcons (j, v) (by simp)
      simp only at this
      rw [h, this]
    · refine ih (fun p hp => hcons p (List.mem_cons_of_mem _ hp)) ?_
      obtain ⟨p, hp, hpi⟩ := hi
      rcases List.mem_cons.1 hp with rfl | hp'
      · exact absurd hpi.symm h
      · exact ⟨p, hp', hpi⟩

theorem okA_of_sat {G : ℕ → ℕ} {as : List (ℕ × ℕ)} (hcons : ∀ p ∈ as, G p.1 = p.2)
    (hrel : ∀ w ∈ relSub, evV G w = 21) : okA as = true := by
  unfold okA
  rw [List.all_eq_true]
  intro w hw
  by_cases hu : usable as w = true
  · have : evV (look as) w = evV G w := by
      apply evV_congr
      intro c hc
      unfold usable at hu
      rw [List.all_eq_true] at hu
      have := hu c hc
      rw [List.any_eq_true] at this
      obtain ⟨p, hp, hpc⟩ := this
      exact look_eq hcons ⟨p, hp, by simpa using hpc⟩
    simp [this, hrel w hw]
  · simp [hu]

theorem go_sound (G : ℕ → ℕ) (hrel : ∀ w ∈ relSub, evV G w = 21) :
    ∀ (order : List ℕ) (as : List (ℕ × ℕ)), go order as = true → (∀ i ∈ order, G i ∈ invCodes) →
      (∀ p ∈ as, G p.1 = p.2) → ∃ x, (∀ p ∈ as, G p.1 = x) ∧ ∀ i ∈ order, G i = x := by
  intro order
  induction order with
  | nil =>
    intro as h _ hcons
    refine ⟨(as.headD (0, 0)).2, fun p hp => ?_, by simp⟩
    unfold go at h
    rw [List.all_eq_true] at h
    simpa [hcons p hp] using h p hp
  | cons i rest ih =>
    intro as h hG hcons
    unfold go at h
    rw [List.all_eq_true] at h
    have hGi := hG i (by simp)
    have h1 := h (G i) hGi
    have hcons' : ∀ p ∈ (i, G i) :: as, G p.1 = p.2 := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp'
      · rfl
      · exact hcons p hp'
    have h2 : go rest ((i, G i) :: as) = true := by
      have := okA_of_sat hcons' hrel
      simpa [this] using h1
    obtain ⟨x, hx1, hx2⟩ := ih ((i, G i) :: as) h2 (fun j hj => hG j (by simp [hj])) hcons'
    refine ⟨x, fun p hp => hx1 p (by simp [hp]), fun j hj => ?_⟩
    rcases List.mem_cons.1 hj with rfl | hj'
    · exact hx1 (j, G j) (by simp)
    · exact hx2 j hj'

theorem fold_prod (l : List S3) (acc : S3) :
    (l.map codeS).foldl mulC (codeS acc) = codeS (acc * l.prod) := by
  induction l generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.map_cons, List.foldl_cons, List.prod_cons]
    rw [← codeS_mul, ih, mul_assoc]

theorem evV_codesOf (f : Fin 6 → S3) (w : List (Fin 6 × Bool)) :
    evV (fun i => if h : i < 6 then codeS (f ⟨i, h⟩) else 21) (codesOf w) =
      codeS (w.map fun p => cond p.2 (f p.1) (f p.1)⁻¹).prod := by
  have := fold_prod (w.map fun p => cond p.2 (f p.1) (f p.1)⁻¹) 1
  rw [codeS_one, one_mul] at this
  rw [← this]
  unfold evV codesOf
  simp only [List.map_map]
  congr 2
  funext ⟨i, b⟩
  cases b
  · have h : (2 * (i : ℕ) + 1) / 2 = i := by omega
    simp [h, codeS_inv]
  · simp

theorem six_involution_eq_of_relators (f : Fin 6 → S3) (hinv : ∀ i, f i * f i = 1)
    (hrel : ∀ w ∈ wsF, (w.map fun p => cond p.2 (f p.1) (f p.1)⁻¹).prod = 1) :
    ∀ i, f i = f 0 := by
  set G : ℕ → ℕ := fun i => if h : i < 6 then codeS (f ⟨i, h⟩) else 21 with hG
  have hrelG : ∀ w ∈ relSub, evV G w = 21 := by
    intro w hw
    obtain ⟨w', hw', rfl⟩ := List.mem_map.1 (relSub_mem w hw)
    rw [hG, evV_codesOf, hrel w' hw', codeS_one]
  have hmem : ∀ i ∈ [4, 5, 1, 0, 2, 3], G i ∈ invCodes := by
    intro i hi
    have hi6 : i < 6 := by simp at hi; omega
    simp only [hG, hi6, dite_true]
    exact mem_invCodes _ (hinv _)
  obtain ⟨x, -, hx⟩ := go_sound G hrelG [4, 5, 1, 0, 2, 3] [] go_true hmem (by simp)
  intro i
  apply codeS_inj
  have h1 : G i.val = x := hx i.val (by have := i.2; simp; omega)
  have h2 : G 0 = x := hx 0 (by simp)
  have e1 : G i.val = codeS (f i) := by simp [hG, i.2]
  have e2 : G 0 = codeS (f 0) := by simp [hG]
  rw [← e1, ← e2, h1, h2]


end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi22S3
