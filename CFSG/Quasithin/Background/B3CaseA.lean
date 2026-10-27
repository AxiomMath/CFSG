module

public import CFSG.Quasithin.Background.B3Named
public import CFSG.Quasithin.Background.B3Class

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def isRepA (n : ℕ) (K : List Tab) : Bool :=
  (List.range (n / 2)).any (fun i => seteqT K (AmL n (i + 1)))

@[expose] def chkNamedA (n : ℕ) : Bool :=
  (List.range (n / 2)).all (fun i => chkGen n (gensAm n (i + 1)) && memD (Dl n) (AmL n (i + 1)))

@[expose] def chkA (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkT n e m && chkClassify n k (isRepA n) && chkNamedA n

theorem chkNamedA_spec (h : chkNamedA n = true) :
    ∀ i < n / 2, chkGen n (gensAm n (i + 1)) = true ∧ memD (Dl n) (AmL n (i + 1)) = true := by
  simp only [chkNamedA, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
  exact h

theorem chkT_subOK {e m : ℕ} (h : chkT n e m = true) : subOK n (Tl n) = true := by
  simp only [chkT, Bool.and_eq_true] at h
  exact h.1.1.1

theorem chkClassify_chkEA {k : Mod} {pr : List Tab → Bool} (h : chkClassify n k pr = true) :
    chkEA n (Tl n) (Dl n) = true := by
  simp only [chkClassify, Bool.and_eq_true] at h
  exact h.1.1

theorem offenders_caseA (hn : 5 ≤ n) (k : Mod) {e m : ℕ} (h : chkA n k e m = true) :
    ∀ A : Subgroup (Gp n), IsOffG n k A ↔ ∃ i < n / 2, A ∈ conjClass (Am n (i + 1)) := by
  simp only [chkA, Bool.and_eq_true] at h
  obtain ⟨⟨hT, hcl⟩, hnamed⟩ := h
  have hEA := chkClassify_chkEA hcl
  have hcls := classify_filter hn k hT hcl
  obtain ⟨-, hmem, -⟩ := chkEA_spec hEA
  intro A
  rw [hcls A]
  constructor
  · rintro ⟨C, hC, hrep, γ, rfl⟩
    obtain ⟨hCok, -⟩ := hmem C hC
    simp only [isRepA, List.any_eq_true, List.mem_range] at hrep
    obtain ⟨i, hi, hCi⟩ := hrep
    obtain ⟨hg, -⟩ := chkNamedA_spec hnamed i hi
    refine ⟨i, hi, mem_conjClass.2 ⟨γ, ?_⟩⟩
    have hAok : subOK n (AmL n (i + 1)) = true := by
      simp only [chkGen, Bool.and_eq_true] at hg
      exact hg.1.1
    rw [Am, closure_eq_of_chkGen hg, subOf_congr hCok hAok hCi]
    rfl
  · rintro ⟨i, hi, hA⟩
    obtain ⟨γ, rfl⟩ := mem_conjClass.1 hA
    obtain ⟨hg, hmemD⟩ := chkNamedA_spec hnamed i hi
    obtain ⟨B, hB, hBt⟩ := memD_spec hmemD
    have hseteq : seteqT B (AmL n (i + 1)) = true := by
      simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
      exact ⟨fun t ht => (hBt t).1 ht, fun t ht => (hBt t).2 ht⟩
    refine ⟨B, hB, ?_, γ, ?_⟩
    · simp only [isRepA, List.any_eq_true, List.mem_range]
      exact ⟨i, hi, hseteq⟩
    · have hLok := (hmem B hB).1
      have hAok : subOK n (AmL n (i + 1)) = true := by
        simp only [chkGen, Bool.and_eq_true] at hg
        exact hg.1.1
      rw [Am, closure_eq_of_chkGen hg, subOf_congr hLok hAok hseteq]
      rfl

end CFSG.Quasithin.B3
