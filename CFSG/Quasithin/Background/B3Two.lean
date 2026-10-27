module

public import CFSG.Quasithin.Background.B3Inst

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

theorem SQTKn.five_le (hn : SQTKn n) : 5 ≤ n := by
  rcases hn with rfl | rfl | rfl | rfl <;> norm_num

theorem not_caseA_of_caseB {k : Mod} (h : CaseB n k) : ¬ CaseA n k := by
  rintro (h1 | h1 | h1)
  · exact absurd h.1 (by omega)
  · rcases h.2 with h2 | h2 <;> simp [h1] at h2
  · rcases h.2 with h2 | h2 <;> simp [h1] at h2

theorem caseA_or_caseB (n : ℕ) (k : Mod) : CaseA n k ∨ CaseB n k := by
  by_cases h : n % 2 = 1
  · exact Or.inl (Or.inl h)
  · have h0 : n % 2 = 0 := by omega
    cases k
    · exact Or.inl (Or.inr (Or.inl rfl))
    · exact Or.inr ⟨h0, Or.inl rfl⟩
    · exact Or.inl (Or.inr (Or.inr rfl))
    · exact Or.inr ⟨h0, Or.inr rfl⟩

theorem three_cases (hn : SQTKn n) (k : Mod) :
    (CaseA n k ∧ PropB32A n k) ∨ (CaseB n k ∧ ¬ (n = 8 ∧ k = Mod.ut0) ∧ PropB32B5 n k) ∨
    (n = 8 ∧ k = Mod.ut0 ∧ PropB32B6 n k) := by
  rcases caseA_or_caseB n k with hA | hB
  · exact Or.inl ⟨hA, propB32A_of hn hA⟩
  · by_cases hexc : n = 8 ∧ k = Mod.ut0
    · obtain ⟨rfl, rfl⟩ := hexc
      exact Or.inr (Or.inr ⟨rfl, rfl, propB32B6_eight⟩)
    · exact Or.inr (Or.inl ⟨hB, hexc, propB32B5_of hn hB hexc⟩)

theorem B3_2_1
    (hn : SQTKn n) (k : Mod) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ n / 2) :
    rk (Am n m) = m ∧
    (¬ (CaseB n k ∧ m = n / 2) → rkIdx (fixV ((Am n m).map (Mod.act n k))) = m) ∧
    (CaseB n k ∧ m = n / 2 → rkIdx (fixV ((Am n m).map (Mod.act n k))) = n / 2 - 1) := by
  obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
  have hi : i < n / 2 := by omega
  rcases three_cases hn k with ⟨hA, h⟩ | ⟨hB, -, h⟩ | ⟨hn8, hk, h⟩
  · obtain ⟨-, hr, -⟩ := h
    obtain ⟨h1, h2⟩ := hr i hi
    exact ⟨h1, fun _ => h2, fun hh => absurd hA (not_caseA_of_caseB hh.1)⟩
  · obtain ⟨-, hr, -⟩ := h
    obtain ⟨h1, h2⟩ := hr i hi
    refine ⟨h1, fun hne => ?_, fun hh => ?_⟩
    · rw [h2]
      have : ¬ (i + 1 = n / 2) := fun he => hne ⟨hB, he⟩
      simp [this]
    · rw [h2]
      simp [hh.2]
  · obtain ⟨-, hr, -⟩ := h
    obtain ⟨h1, h2⟩ := hr i hi
    have hB : CaseB n k := ⟨by omega, Or.inr hk⟩
    refine ⟨h1, fun hne => ?_, fun hh => ?_⟩
    · rw [h2]
      have : ¬ (i + 1 = n / 2) := fun he => hne ⟨hB, he⟩
      simp [this]
    · rw [h2]
      simp [hh.2]

theorem B3_2_2 (hn : SQTKn n) (k : Mod) (hB : CaseB n k) :
    rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2 := by
  rcases three_cases hn k with ⟨hA, -⟩ | ⟨-, -, -, -, h, -⟩ | ⟨-, -, -, -, h, -⟩
  · exact absurd hA (not_caseA_of_caseB hB)
  · exact h
  · exact h

theorem B3_2_3 {A : Subgroup (Gp 8)} (hA : A ∈ Rset 8) :
    rkIdx (fixV (A.map (Mod.act 8 Mod.ut0))) = 3 := by
  obtain ⟨-, -, -, hR, -⟩ := propB32B6_eight
  exact hR A hA

theorem Am_zero : Am n 0 = ⊥ := by
  unfold Am
  have : {g : Gp n | g ∈ gensAm n 0} = ∅ := by
    ext g
    simp [gensAm]
  rw [this, Subgroup.closure_empty]

theorem forall_Am_le {T : Subgroup (Gp n)} (h : ∀ i < n / 2, Am n (i + 1) ≤ T) :
    ∀ m, m ≤ n / 2 → Am n m ≤ T := by
  intro m hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [Am_zero]
    exact bot_le
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    exact h i (by omega)

theorem exists_lt_iff {P : ℕ → Prop} :
    (∃ i < n / 2, P (i + 1)) ↔ ∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ P m := by
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨i + 1, by omega, by omega, h⟩
  · rintro ⟨m, hm1, hm2, h⟩
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    exact ⟨i, by omega, h⟩

theorem B3_2_4 (hn : SQTKn n) (k : Mod) (hA : CaseA n k) :
    (∀ A : Subgroup (Gp n), IsOffG n k A ↔
      ∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∧
    (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
      ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (Dsub n).map (Mod.act n k)) ∧
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((1 : ℚ) : WithTop ℚ) := by
  rcases three_cases hn k with ⟨-, h⟩ | ⟨hB, -⟩ | ⟨hn8, hk, -⟩
  · obtain ⟨hoff, -, ⟨T, hTm, hTA0, hJ⟩, hq⟩ := h
    exact ⟨fun A => (hoff A).trans (exists_lt_iff (n := n) (P := fun m => A ∈ conjClass (Am n m))),
      ⟨T, forall_Am_le hTm, hTA0, hJ⟩, hq⟩
  · exact absurd hA (not_caseA_of_caseB hB)
  · exact absurd hA (not_caseA_of_caseB ⟨by omega, Or.inr hk⟩)

theorem B3_2_5
    (hn : SQTKn n) (k : Mod) (hB : CaseB n k) (hexc : ¬ (n = 8 ∧ k = Mod.ut0)) :
    (∀ A : Subgroup (Gp n), IsOffG n k A ↔
      A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
        (∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∨ A ∈ Hset n) ∧
    (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
      ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) =
        (Dsub n ⊔ Subgroup.closure
          {x : Gp n | x ∈ (T : Subgroup (Gp n)) ∧ IsConj (ti n 0 * ti n 1) x}).map
            (Mod.act n k)) ∧
    qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ) := by
  rcases three_cases hn k with ⟨hA, -⟩ | ⟨-, -, h⟩ | ⟨hn8, hk, -⟩
  · exact absurd hA (not_caseA_of_caseB hB)
  · obtain ⟨hoff, -, -, ⟨T, hTm, hTA0, hJ, -⟩, hq⟩ := h
    exact ⟨fun A => (hoff A).trans (or_congr Iff.rfl (or_congr Iff.rfl (or_congr
      (exists_lt_iff (n := n) (P := fun m => A ∈ conjClass (Am n m))) Iff.rfl))),
      ⟨T, forall_Am_le hTm, hTA0, hJ⟩, hq⟩
  · exact absurd ⟨hn8, hk⟩ hexc

theorem B3_2_6 :
    (∀ A : Subgroup (Gp 8), IsOffG 8 Mod.ut0 A ↔
      A ∈ conjClass (Dsub 8 ⊓ alternatingGroup (Fin 8)) ∨ A ∈ conjClass (A0 8) ∨
        (∃ m, 1 ≤ m ∧ m ≤ 4 ∧ A ∈ conjClass (Am 8 m)) ∨ A ∈ Hset 8 ∨ A ∈ Rset 8) ∧
    (∃ T : Sylow 2 (Gp 8), (∀ m, m ≤ 4 → Am 8 m ≤ T) ∧ A0 8 ≤ T ∧
      ffJ ((T : Subgroup (Gp 8)).map (Mod.act 8 Mod.ut0)) =
        (T : Subgroup (Gp 8)).map (Mod.act 8 Mod.ut0) ∧
      ∀ A : Subgroup (Gp 8), A ≤ T →
        (IsStrongFFStarOffender ((T : Subgroup (Gp 8)).map (Mod.act 8 Mod.ut0))
          (A.map (Mod.act 8 Mod.ut0)) ↔ A = Dsub 8)) ∧
    qOf ((⊤ : Subgroup (Gp 8)).map (Mod.act 8 Mod.ut0)) = ((3 / 4 : ℚ) : WithTop ℚ) := by
  obtain ⟨hoff, -, -, -, ⟨T, hTm, hTA0, hJ, hs⟩, hq⟩ := propB32B6_eight
  refine ⟨fun A => (hoff A).trans (or_congr Iff.rfl (or_congr Iff.rfl (or_congr
      (exists_lt_iff (n := 8) (P := fun m => A ∈ conjClass (Am 8 m))) Iff.rfl))),
    ⟨T, forall_Am_le hTm, hTA0, hJ, hs⟩, ?_⟩
  rw [hq]
  norm_num

end CFSG.Quasithin.B3
