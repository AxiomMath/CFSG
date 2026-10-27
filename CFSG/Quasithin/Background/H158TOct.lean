module

public import CFSG.Quasithin.Background.H158TLab

public section

namespace CFSG.Quasithin.H158T

@[expose] def o2F : Finset (Fin 24) := {8, 11, 13, 14, 17, 18, 20, 23}
@[expose] def o0F : Finset (Fin 24) := {0, 1, 2, 6, 9, 12, 16, 21}
@[expose] def o1F : Finset (Fin 24) := {3, 4, 5, 7, 10, 15, 19, 22}
@[expose] def o1L : List ℕ := [3, 4, 5, 7, 10, 15, 19, 22]
@[expose] def o2L : List ℕ := [8, 11, 13, 14, 17, 18, 20, 23]
@[expose] def c16F : Finset (Fin 24) := Finset.univ \ o2F

theorem mem_o0F (x : Fin 24) : x ∈ o0F ↔ (x : ℕ) ∈ o0L := by
  fin_cases x <;> simp [o0F, o0L]

theorem mem_o1F (x : Fin 24) : x ∈ o1F ↔ (x : ℕ) ∈ o1L := by
  fin_cases x <;> simp [o1F, o1L]

theorem mem_o2F (x : Fin 24) : x ∈ o2F ↔ (x : ℕ) ∈ o2L := by
  fin_cases x <;> simp [o2F, o2L]

theorem pt16_iff (x : Fin 24) : (x : ℕ) ∈ pt16 ↔ x ∉ o2F := by
  rw [mem_o2F]
  fin_cases x <;> simp [pt16, o2L]

theorem mem_c16F (x : Fin 24) : x ∈ c16F ↔ (x : ℕ) ∈ pt16 := by
  rw [pt16_iff, c16F, Finset.mem_sdiff]
  simp

theorem o2F_card : o2F.card = 8 := by decide

theorem c16F_card : c16F.card = 16 := by
  rw [c16F, Finset.card_univ_diff, o2F_card]
  simp

theorem o0L_pt16 : ∀ n ∈ o0L, n ∈ pt16 := by decide +kernel

theorem diff_dec : ∀ n ∈ List.range 24, (n ∈ pt16 ∧ n ∉ o0L) ↔ n ∈ o1L := by
  decide +kernel

theorem orbit_fin (σ : ℕ → Equiv.Perm (Fin 24))
    (hσ : ∀ j ∈ [0, 1, 2, 3], ∀ x : Fin 24, ((σ j x : Fin 24) : ℕ) = gimg j x)
    (X : Finset (Fin 24)) (hX : X.card = 8)
    (hinv : ∀ j ∈ [0, 1, 2, 3], ∀ x : Fin 24, σ j x ∈ X ↔ x ∈ X) : X = o2F := by
  by_cases hmeet : ∃ x0 ∈ X, (x0 : ℕ) ∈ pt16
  · exfalso
    obtain ⟨x0, hx0X, hx0⟩ := hmeet
    let P : ℕ → Bool := fun y => if h : y < 24 then decide (⟨y, h⟩ ∈ X) else false
    have hPx : ∀ x : Fin 24, P x = decide (x ∈ X) := by
      intro x
      simp [P, x.isLt]
    have hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3], P (gimg j x) = P x := by
      intro x hx j hj
      have hx24 : x < 24 := pt16_lt_dec x hx
      have key : P ((σ j ⟨x, hx24⟩ : Fin 24) : ℕ) = P ((⟨x, hx24⟩ : Fin 24) : ℕ) := by
        rw [hPx, hPx, decide_eq_decide]
        exact hinv j hj ⟨x, hx24⟩
      rw [hσ j hj ⟨x, hx24⟩] at key
      exact key
    have hall := orbit_lab P x0 hx0 (by rw [hPx]; simpa using hx0X) hP
    have hsub : c16F ⊆ X := by
      intro z hz
      have hz16 : (z : ℕ) ∈ pt16 := (mem_c16F z).1 hz
      have hz' := hall z hz16
      rw [hPx] at hz'
      simpa using hz'
    have hle := Finset.card_le_card hsub
    rw [hX, c16F_card] at hle
    omega
  · have hsub : X ⊆ o2F := by
      intro x hx
      by_contra hno
      exact hmeet ⟨x, hx, (pt16_iff x).2 hno⟩
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hX, o2F_card])

theorem part_gen (σ : ℕ → Equiv.Perm (Fin 24))
    (hσ : ∀ j ∈ [0, 1, 2, 3], ∀ x : Fin 24, ((σ j x : Fin 24) : ℕ) = gimg j x)
    (A C : Finset (Fin 24)) (h0 : (0 : Fin 24) ∈ A)
    (hAC : ∀ x : Fin 24, (x ∈ A ∨ x ∈ C) ↔ x ∈ c16F)
    (hdis : ∀ x : Fin 24, x ∈ A → x ∉ C)
    (hCne : ∃ x : Fin 24, x ∈ C)
    (hσA : ∀ j ∈ [0, 1, 2, 3], (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ A) ∨
      (∀ x : Fin 24, x ∈ A ↔ σ j x ∈ C)) :
    A = o0F ∧ C = o1F := by
  have hbit : ∀ j : ℕ, ∃ b : Bool, j ∈ [0, 1, 2, 3] → ∀ x : Fin 24, (x : ℕ) ∈ pt16 →
      (σ j x ∈ A ↔ Bool.xor (decide (x ∈ A)) b = true) := by
    intro j
    by_cases hj : j ∈ [0, 1, 2, 3]
    · rcases hσA j hj with h | h
      · refine ⟨false, fun _ x _ => ?_⟩
        rw [Bool.xor_false, decide_eq_true_eq]
        exact (h x).symm
      · refine ⟨true, fun _ x hx => ?_⟩
        have hmem : σ j x ∈ c16F := (mem_c16F _).2 (by
          rw [hσ j hj x]
          exact gen_closed_dec j hj _ hx)
        have hor := (hAC (σ j x)).2 hmem
        have hiff : σ j x ∈ A ↔ x ∉ A := by
          constructor
          · intro hsA hxA
            exact hdis _ hsA ((h x).1 hxA)
          · intro hxA
            have hsC : σ j x ∉ C := fun hc => hxA ((h x).2 hc)
            exact hor.resolve_right hsC
        rw [Bool.xor_true, Bool.not_eq_true', decide_eq_false_iff_not]
        exact hiff
    · exact ⟨false, fun h => absurd h hj⟩
  choose b hb using hbit
  have hcs : [b 0, b 1, b 2, b 3] ∈ allCs := by
    generalize b 0 = c0
    generalize b 1 = c1
    generalize b 2 = c2
    generalize b 3 = c3
    cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> decide
  let P : ℕ → Bool := fun y => if h : y < 24 then decide (⟨y, h⟩ ∈ A) else false
  have hPx : ∀ x : Fin 24, P x = decide (x ∈ A) := fun x => by simp [P, x.isLt]
  have hP : ∀ x ∈ pt16, ∀ j ∈ [0, 1, 2, 3],
      P (gimg j x) = Bool.xor (P x) ([b 0, b 1, b 2, b 3].getD j false) := by
    intro x hx j hj
    have hx24 : x < 24 := pt16_lt_dec x hx
    have hcj : [b 0, b 1, b 2, b 3].getD j false = b j := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl <;> rfl
    rw [hcj]
    have key := hb j hj ⟨x, hx24⟩ hx
    have e : gimg j x = ((σ j ⟨x, hx24⟩ : Fin 24) : ℕ) := (hσ j hj ⟨x, hx24⟩).symm
    have hPx2 : P x = decide (⟨x, hx24⟩ ∈ A) := by simp [P, hx24]
    rw [e, hPx, hPx2, Bool.eq_iff_iff, decide_eq_true_eq]
    exact key
  have hB : ∃ y ∈ pt16, P y = false := by
    obtain ⟨x, hxC⟩ := hCne
    have hx16 : x ∈ c16F := (hAC x).1 (Or.inr hxC)
    refine ⟨(x : ℕ), (mem_c16F x).1 hx16, ?_⟩
    rw [hPx]
    exact decide_eq_false (fun hxA => hdis x hxA hxC)
  have h0P : P 0 = true := (hPx 0).trans (decide_eq_true h0)
  have hlab := part_lab P _ hcs h0P hP hB
  have hAeq : A = o0F := by
    ext x
    rw [mem_o0F]
    constructor
    · intro hxA
      have hx16 : x ∈ c16F := (hAC x).1 (Or.inl hxA)
      have h1 : P (x : ℕ) = true := by rw [hPx]; exact decide_eq_true hxA
      have h2 := hlab (x : ℕ) ((mem_c16F x).1 hx16)
      rw [h1] at h2
      exact of_decide_eq_true h2.symm
    · intro hxo
      have h1 := hlab (x : ℕ) (o0L_pt16 _ hxo)
      have h2 : P (x : ℕ) = true := by rw [h1]; exact decide_eq_true hxo
      rw [hPx] at h2
      exact of_decide_eq_true h2
  have hCeq : C = o1F := by
    ext x
    rw [mem_o1F]
    have hx24 : (x : ℕ) ∈ List.range 24 := List.mem_range.2 x.isLt
    constructor
    · intro hxC
      have hxc16 : (x : ℕ) ∈ pt16 := (mem_c16F x).1 ((hAC x).1 (Or.inr hxC))
      have hxA : x ∉ A := fun hA => hdis x hA hxC
      have hxo0 : (x : ℕ) ∉ o0L := fun ho => hxA (by rw [hAeq]; exact (mem_o0F x).2 ho)
      exact (diff_dec _ hx24).1 ⟨hxc16, hxo0⟩
    · intro hxo1
      have h16 := (diff_dec _ hx24).2 hxo1
      have hxc : x ∈ c16F := (mem_c16F x).2 h16.1
      have hxA : x ∉ A := by
        rw [hAeq]
        exact fun h => h16.2 ((mem_o0F x).1 h)
      rcases (hAC x).2 hxc with h | h
      · exact absurd h hxA
      · exact h
  exact ⟨hAeq, hCeq⟩

end CFSG.Quasithin.H158T
