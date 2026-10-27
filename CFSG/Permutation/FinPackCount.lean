module

public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

@[expose] noncomputable def sumLtK (f : ℕ → ℕ) (m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc (f j)) m

theorem sumLtK_eq (f : ℕ → ℕ) (m : ℕ) : sumLtK f m = ∑ j ∈ range m, f j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    rfl

@[expose] noncomputable def cntK (n : ℕ) (Q : ℕ → Bool) (r : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ c => Bool.rec (motive := fun _ => ℕ) 0 1 (Q c))
    (fun _ w d u c => sumLtK (fun j => Bool.rec (motive := fun _ => ℕ)
      (w (Nat.succ d) (Nat.lor u (Nat.shiftLeft 1 j)) (Nat.add c (Nat.shiftLeft j (Nat.mul 4 d))))
      0 (Nat.blt 0 (Nat.land u (Nat.shiftLeft 1 j)))) n) r

theorem cntK_succ (n : ℕ) (Q : ℕ → Bool) (r d u c : ℕ) : cntK n Q (r + 1) d u c =
    sumLtK (fun j => Bool.rec (motive := fun _ => ℕ)
      (cntK n Q r (Nat.succ d) (Nat.lor u (Nat.shiftLeft 1 j))
        (Nat.add c (Nat.shiftLeft j (Nat.mul 4 d))))
      0 (Nat.blt 0 (Nat.land u (Nat.shiftLeft 1 j)))) n := rfl

@[expose] noncomputable def maskP (p : ℕ → ℕ) (d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i m => Nat.lor m (Nat.shiftLeft 1 (p i))) d

theorem testBit_maskP (p : ℕ → ℕ) (d k : ℕ) :
    (maskP p d).testBit k = true ↔ ∃ i < d, p i = k := by
  induction d with
  | zero =>
    change (0 : ℕ).testBit k = true ↔ _
    rw [Nat.zero_testBit]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ d ih =>
    change (maskP p d ||| 1 <<< p d).testBit k = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
      decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨d, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem maskP_congr {p q : ℕ → ℕ} {d : ℕ} (h : ∀ i < d, p i = q i) : maskP p d = maskP q d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change Nat.lor (maskP p d) (Nat.shiftLeft 1 (p d)) = Nat.lor (maskP q d) (Nat.shiftLeft 1 (q d))
    rw [ih fun i hi => h i (by omega), h d (by omega)]

theorem blt_land_iff (m j : ℕ) :
    Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 j)) = true ↔ m.testBit j = true := by
  have hx : Nat.land m (Nat.shiftLeft 1 j) = if m.testBit j = true then 2 ^ j else 0 := by
    change m &&& 1 <<< j = _
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases hk : j = k
    · subst hk
      by_cases h : m.testBit j = true
      · simp [h]
      · simp [h]
    · by_cases h : m.testBit j = true
      · simp [h, hk]
      · simp [h, hk]
  rw [hx, Nat.blt_eq]
  by_cases h : m.testBit j = true
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => Nat.two_pow_pos j⟩
  · rw [if_neg h]
    exact ⟨fun h0 => absurd h0 (Nat.lt_irrefl 0), fun h' => absurd h' h⟩

variable {n : ℕ}

noncomputable def ofVals (p : ℕ → ℕ) (hp : ∀ i < n, p i < n)
    (hi : ∀ i < n, ∀ j < n, p i = p j → i = j) : Perm (Fin n) :=
  Equiv.ofBijective (fun i : Fin n => (⟨p i, hp i i.2⟩ : Fin n))
    (Finite.injective_iff_bijective.1 fun a b h => Fin.ext (hi a a.2 b b.2 (congrArg Fin.val h)))

theorem valF_ofVals (p : ℕ → ℕ) (hp : ∀ i < n, p i < n)
    (hi : ∀ i < n, ∀ j < n, p i = p j → i = j) {i : ℕ} (h : i < n) :
    valF (ofVals p hp hi) i = p i := by
  rw [valF, dif_pos h]
  rfl

open Classical in
theorem cntK_card_base (Q : ℕ → Bool) (p : ℕ → ℕ) (hp : ∀ i < n, p i < n)
    (hi : ∀ i < n, ∀ j < n, p i = p j → i = j) :
    cntK n Q 0 n (maskP p n) (encF p n) =
      (univ.filter fun σ : Perm (Fin n) => (∀ i < n, valF σ i = p i) ∧ Q (enc σ) = true).card := by
    have he : ∀ σ : Perm (Fin n), (∀ i < n, valF σ i = p i) → enc σ = encF p n :=
      fun σ h => encF_congr h
    change Bool.rec (motive := fun _ => ℕ) 0 1 (Q (encF p n)) = _
    cases hq : Q (encF p n)
    · symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro σ - ⟨h1, h2⟩
      rw [he σ h1, hq] at h2
      exact Bool.false_ne_true h2
    · symm
      rw [Finset.card_eq_one]
      refine ⟨ofVals p hp hi, ?_⟩
      ext σ
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h1, -⟩
        refine Equiv.ext fun i => Fin.ext ?_
        have e1 := h1 i i.2
        have e2 := valF_ofVals p hp hi i.2
        rw [valF, dif_pos i.2] at e1 e2
        rw [e1, ← e2]
      · rintro rfl
        refine ⟨Finset.mem_univ _, fun i h => valF_ofVals p hp hi h, ?_⟩
        rw [he _ fun i h => valF_ofVals p hp hi h, hq]

open Classical in
theorem cntK_card_aux (Q : ℕ → Bool) : ∀ r d (p : ℕ → ℕ), d + r = n → (∀ i < d, p i < n) →
    (∀ i < d, ∀ j < d, p i = p j → i = j) →
    cntK n Q r d (maskP p d) (encF p d) =
      (univ.filter fun σ : Perm (Fin n) => (∀ i < d, valF σ i = p i) ∧ Q (enc σ) = true).card := by
  intro r
  induction r with
  | zero =>
    intro d p hd hp hi
    have e : d = n := hd
    rw [e] at hp hi ⊢
    exact cntK_card_base Q p hp hi
  | succ r ih =>
    intro d p hd hp hi
    have hdn : d < n := by omega
    rw [cntK_succ, sumLtK_eq]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => valF σ d) (t := range n)
      fun σ _ => Finset.mem_range.2 (valF_lt σ hdn)]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j < n := Finset.mem_range.1 hj
    by_cases hu : (maskP p d).testBit j = true
    · rw [(blt_land_iff _ _).2 hu]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ hσ hdj
      rw [Finset.mem_filter] at hσ
      obtain ⟨i, hid, hij⟩ := (testBit_maskP p d j).1 hu
      have e : valF σ i = valF σ d := by rw [hσ.2.1 i hid, hij, hdj]
      have := valF_inj σ (by omega) hdn e
      omega
    · have hb : Nat.blt 0 (Nat.land (maskP p d) (Nat.shiftLeft 1 j)) = false :=
        Bool.eq_false_iff.2 fun h => hu ((blt_land_iff _ _).1 h)
      rw [hb]
      let p' : ℕ → ℕ := fun i => if i < d then p i else j
      have hpp : ∀ i < d, p' i = p i := fun i h => if_pos h
      have hpd : p' d = j := if_neg (Nat.lt_irrefl d)
      have hm : maskP p' (d + 1) = Nat.lor (maskP p d) (Nat.shiftLeft 1 j) := by
        change Nat.lor (maskP p' d) (Nat.shiftLeft 1 (p' d)) = _
        rw [maskP_congr hpp, hpd]
      have hc : encF p' (d + 1) = Nat.add (encF p d) (Nat.shiftLeft j (Nat.mul 4 d)) := by
        change Nat.add (encF p' d) (Nat.shiftLeft (p' d) (Nat.mul 4 d)) = _
        rw [encF_congr hpp, hpd]
      have hp' : ∀ i < d + 1, p' i < n := by
        intro i h
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · rw [hpp i h]
          exact hp i h
        · rw [hpd]
          exact hjn
      have hnew : ∀ i < d, p i ≠ j := fun i h e => hu ((testBit_maskP p d j).2 ⟨i, h, e⟩)
      have hi' : ∀ i < d + 1, ∀ k < d + 1, p' i = p' k → i = k := by
        intro i h k h' e
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 h' with h' | rfl
        · rw [hpp i h, hpp k h'] at e
          exact hi i h k h' e
        · rw [hpp i h, hpd] at e
          exact absurd e (hnew i h)
        · rw [hpp k h', hpd] at e
          exact absurd e.symm (hnew k h')
        · rfl
      have key := ih (d + 1) p' (by omega) hp' hi'
      rw [hm, hc] at key
      change cntK n Q r (d + 1) _ _ = _
      rw [key]
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun i h => ?_, h2⟩, ?_⟩
        · rw [h1 i (by omega), hpp i h]
        · rw [h1 d (by omega), hpd]
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨fun i h => ?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · rw [h1 i h, hpp i h]
        · rw [h3, hpd]

theorem card_filter_eq_cntK (Q : ℕ → Bool) :
    (univ.filter fun σ : Perm (Fin n) => Q (enc σ) = true).card = cntK n Q n 0 0 0 := by
  classical
  have h := cntK_card_aux (n := n) Q n 0 (fun _ => 0) (by omega)
    (fun i h => absurd h (Nat.not_lt_zero i)) (fun i h => absurd h (Nat.not_lt_zero i))
  change cntK n Q n 0 0 0 = _ at h
  rw [h]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ =>
    ⟨fun h => ⟨fun i hi => absurd hi (Nat.not_lt_zero i), h⟩, fun h => h.2⟩)

theorem allLtK_iff_sumLtK {f : ℕ → Bool} {g : ℕ → ℕ} (h : ∀ j, f j = true ↔ g j = 0) (m : ℕ) :
    allLtK f m = true ↔ sumLtK g m = 0 := by
  rw [allLtK_iff, sumLtK_eq, Finset.sum_eq_zero_iff]
  exact ⟨fun H j hj => (h j).1 (H j (Finset.mem_range.1 hj)),
    fun H j hj => (h j).2 (H j (Finset.mem_range.2 hj))⟩

theorem walkK_iff_cntK (Q : ℕ → Bool) : ∀ r d u c,
    walkK n Q r d u c = true ↔ cntK n (fun c => !Q c) r d u c = 0 := by
  intro r
  induction r with
  | zero =>
    intro d u c
    change Q c = true ↔ Bool.rec (motive := fun _ => ℕ) 0 1 (!Q c) = 0
    cases Q c
    · exact ⟨fun h => absurd h Bool.false_ne_true, fun h => absurd h Nat.one_ne_zero⟩
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ r ih =>
    intro d u c
    rw [walkK_succ, cntK_succ]
    refine allLtK_iff_sumLtK (fun j => ?_) n
    cases Nat.blt 0 (Nat.land u (Nat.shiftLeft 1 j))
    · exact ih _ _ _
    · exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem exists_of_walkK {P : ℕ → Bool} (h : walkK n (fun c => !P c) n 0 0 0 = false) :
    ∃ σ : Perm (Fin n), P (enc σ) = true := by
  have h0 : cntK n (fun c => !!P c) n 0 0 0 ≠ 0 := fun e =>
    Bool.false_ne_true (h ▸ (walkK_iff_cntK (fun c => !P c) n 0 0 0).2 e)
  rw [← card_filter_eq_cntK, Ne, Finset.card_eq_zero] at h0
  obtain ⟨σ, hσ⟩ := Finset.nonempty_iff_ne_empty.2 h0
  rw [Finset.mem_filter, Bool.not_not] at hσ
  replace hσ := hσ.2
  exact ⟨σ, hσ⟩

end CFSG.Permutation.FinPack
