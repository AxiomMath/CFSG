module

public import CFSG.Quasithin.AppendixH.H16.H165FourData

public section

namespace CFSG.ASVolI.H16

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.RonanH143 CFSG.Monster.Code

@[expose] def h165PairIdx : Array ℕ :=
  #[0, 0, 1, 2, 1, 2, 3, 3, 4, 5, 6, 7, 7, 6, 5, 4, 8, 9, 10, 11, 11, 10, 9, 8]

@[expose] def h165PatArr (n : ℕ) : Array ℕ :=
  ((List.range 24).map fun j =>
    if n.testBit h165PairIdx[j]! then h165PartnerArr[j]! else j).toArray

theorem h165_patCheck : (List.range 4096).all (fun n =>
    !autArrOK (h165PatArr n) (h165PatArr n) ||
      (h165PatArr n == idArr || h165PatArr n == koArr 7 || h165PatArr n == h165D0Arr ||
        h165PatArr n == h165ZD0Arr)) = true := by
  decide +kernel

theorem autArrOK_of_mem {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm) {a b : Array ℕ}
    (ha : HasArr σ a) (hb : HasArr σ⁻¹ b) : autArrOK a b = true := by
  rw [autArrOK, List.all_eq_true]
  intro i hi
  have hi12 : i < 12 := List.mem_range.1 hi
  have h1 : syndM (permM a (Bmask i)) = 0 := by
    have hm : permWord σ (B ⟨i, hi12⟩) ∈ C :=
      permWord_mem_of_mem_AutPerm hσ (B_mem_C ⟨i, hi12⟩)
    rw [B_eq_bvec ⟨i, hi12⟩, permWord_bvec ha (Bmask i)] at hm
    exact (bvec_mem_C_iff (permM a (Bmask i))).1 hm
  have h2 : syndM (permM b (Bmask i)) = 0 := by
    have hm : permWord σ⁻¹ (B ⟨i, hi12⟩) ∈ C :=
      permWord_mem_of_mem_AutPerm (AutPerm.inv_mem hσ) (B_mem_C ⟨i, hi12⟩)
    rw [B_eq_bvec ⟨i, hi12⟩, permWord_bvec hb (Bmask i)] at hm
    exact (bvec_mem_C_iff (permM b (Bmask i))).1 hm
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨h1, h2⟩

private def h165OfBits (m : ℕ) (f : ℕ → Bool) : ℕ :=
  (List.range m).foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) 0

private theorem h165OfBits_testBit (f : ℕ → Bool) (m i : ℕ) :
    (h165OfBits m f).testBit i = (decide (i < m) && f i) := by
  rw [h165OfBits]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    split_ifs with hf
    · rw [Nat.testBit_or, ih, Nat.one_shiftLeft, Nat.testBit_two_pow]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1, Ne.symm him]
    · rw [ih]
      by_cases him : i = m
      · subst him; simp [hf]
      · have h1 : (i < m + 1) ↔ (i < m) := by omega
        simp [h1]

private theorem h165OfBits_lt (m : ℕ) (f : ℕ → Bool) : h165OfBits m f < 2 ^ m := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [h165OfBits_testBit]
  simp
  omega

theorem exists_testBit_eq (f : Fin 12 → Bool) : ∃ n < 4096, ∀ i : Fin 12, n.testBit i = f i := by
  refine ⟨h165OfBits 12 (fun i => if h : i < 12 then f ⟨i, h⟩ else false), ?_, fun i => ?_⟩
  · rw [show (4096 : ℕ) = 2 ^ 12 by norm_num]
    exact h165OfBits_lt 12 _
  · rw [h165OfBits_testBit]
    simp [i.2]

private def h165PairMoved (σ : Equiv.Perm (Fin 24)) (i : Fin 12) : Bool :=
  decide (∃ p : Fin 24, h165PairIdx[(p : ℕ)]! = (i : ℕ) ∧ σ p ≠ p)

private theorem h165PairIdx_iff : ∀ p q : Fin 24,
    h165PairIdx[(p : ℕ)]! = h165PairIdx[(q : ℕ)]! ↔ (q = p ∨ q = h165Partner p) := by
  decide +kernel

private theorem h165PairIdx_lt : ∀ p : Fin 24, h165PairIdx[(p : ℕ)]! < 12 := by
  decide +kernel

private theorem h165PartnerArr_lt : ∀ p : Fin 24, h165PartnerArr[(p : ℕ)]! < 24 := by
  decide +kernel

private theorem patArr_get (n : ℕ) {p : ℕ} (hp : p < 24) :
    (h165PatArr n)[p]! = if n.testBit h165PairIdx[p]! then h165PartnerArr[p]! else p := by
  rw [h165PatArr, getElem!_pos _ p (by simpa using hp)]
  simp

theorem h165_pair_preserving {σ : Equiv.Perm (Fin 24)} (hσ : σ ∈ AutPerm)
    (h : ∀ p : Fin 24, σ p = p ∨ σ p = h165Partner p) :
    σ = 1 ∨ σ = h165Z0 ∨ σ = h165D0 ∨ σ = h165Z0 * h165D0 := by
  have key : ∀ p : Fin 24, σ (h165Partner p) = h165Partner (σ p) := by
    intro p
    rcases h p with hp | hp
    · rcases h (h165Partner p) with hq | hq
      · exact hq.trans (by rw [hp])
      · exfalso
        refine h165Partner_ne p (σ.injective ?_)
        exact hq.trans ((h165Partner_partner p).trans hp.symm)
    · rcases h (h165Partner p) with hq | hq
      · exfalso
        refine h165Partner_ne p (σ.injective ?_)
        exact hq.trans hp.symm
      · rw [hq, hp, h165Partner_partner]
  obtain ⟨n, hn, hf⟩ := exists_testBit_eq (h165PairMoved σ)
  have hform : ∀ p : Fin 24, σ p =
      if n.testBit h165PairIdx[(p : ℕ)]! then h165Partner p else p := by
    intro p
    by_cases hb : n.testBit h165PairIdx[(p : ℕ)]! = true
    · rw [if_pos hb]
      by_contra hne
      have hp : σ p = p := (h p).resolve_right hne
      have hfF : h165PairMoved σ ⟨h165PairIdx[(p : ℕ)]!, h165PairIdx_lt p⟩ = false := by
        rw [h165PairMoved, decide_eq_false_iff_not]
        rintro ⟨q, hq, hqne⟩
        rcases (h165PairIdx_iff p q).1 hq.symm with hqeq | hqeq
        · rw [hqeq] at hqne
          exact hqne hp
        · rw [hqeq, key p, hp] at hqne
          exact hqne rfl
      have hbit : n.testBit h165PairIdx[(p : ℕ)]! = false := by
        rw [hf ⟨h165PairIdx[(p : ℕ)]!, h165PairIdx_lt p⟩]
        exact hfF
      exact absurd (hbit.symm.trans hb) (by decide)
    · rw [if_neg hb]
      by_contra hne
      have hp : σ p = h165Partner p := (h p).resolve_left hne
      have hfT : h165PairMoved σ ⟨h165PairIdx[(p : ℕ)]!, h165PairIdx_lt p⟩ = true := by
        rw [h165PairMoved, decide_eq_true_iff]
        exact ⟨p, rfl, by rw [hp]; exact h165Partner_ne p⟩
      have hbit : n.testBit h165PairIdx[(p : ℕ)]! = true := by
        rw [hf ⟨h165PairIdx[(p : ℕ)]!, h165PairIdx_lt p⟩]
        exact hfT
      exact absurd hbit hb
  have harr : HasArr σ (h165PatArr n) := by
    intro i
    rw [hform i, patArr_get n i.2]
    by_cases hb : n.testBit h165PairIdx[(i : ℕ)]! = true
    · simp only [hb]
      show h165PartnerArr[(i : ℕ)]! % 24 = h165PartnerArr[(i : ℕ)]!
      exact Nat.mod_eq_of_lt (h165PartnerArr_lt i)
    · have hbf : n.testBit h165PairIdx[(i : ℕ)]! = false := Bool.eq_false_iff.2 hb
      simp only [hbf]
      rfl
  have hinv : σ * σ = 1 := by
    apply Equiv.ext
    intro p
    show σ (σ p) = p
    rcases h p with hp | hp
    · rw [hp, hp]
    · rw [hp, key p, hp, h165Partner_partner]
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hinv
  have harr_inv : HasArr σ⁻¹ (h165PatArr n) := hσinv.symm ▸ harr
  have hok : autArrOK (h165PatArr n) (h165PatArr n) = true :=
    autArrOK_of_mem hσ harr harr_inv
  have hcheck : h165PatArr n = idArr ∨ h165PatArr n = koArr 7 ∨
      h165PatArr n = h165D0Arr ∨ h165PatArr n = h165ZD0Arr := by
    have hc := List.all_eq_true.1 h165_patCheck n (List.mem_range.2 hn)
    rw [hok] at hc
    simp [beq_iff_eq] at hc
    tauto
  rcases hcheck with h1 | h2 | h3 | h4
  · exact Or.inl (perm_eq_of_hasArr (h1 ▸ harr) hasArr_one)
  · exact Or.inr (Or.inl (perm_eq_of_hasArr (h2 ▸ harr) hasArr_h165Z0))
  · exact Or.inr (Or.inr (Or.inl (perm_eq_of_hasArr (h3 ▸ harr) hasArr_h165D0)))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [h165ZD0_eq]
    exact perm_eq_of_hasArr (h4 ▸ harr) hasArr_h165ZD0

end CFSG.ASVolI.H16
