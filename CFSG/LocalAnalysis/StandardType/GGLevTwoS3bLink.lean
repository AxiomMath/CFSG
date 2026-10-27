module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bFilter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompAlcove

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem

theorem levTwoS3b_combo_apply {τ : Tag} (K : KacData τ) (n : Option (Fin τ.rank) → ℕ)
    (j : Fin τ.rank) :
    K.combo n j = -(n none : ℤ) * K.θ j + (n (some j) : ℤ) := by
  rw [KacData.combo, Fintype.sum_option]
  simp [KacData.extRoot, Pi.single_apply]

theorem levTwoS3b_mem_rootsOf_iff
    {τ : Tag} (K : KacData τ) (hK : K.Facts)
    (D : Finset (Option (Fin τ.rank))) (hD : D ≠ Finset.univ) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) :
    β ∈ K.rootsOf (D : Set (Option (Fin τ.rank))) ↔
      ∃ (e : ℕ) (sgn : ℤ), e ≤ 1 ∧ (sgn = 1 ∨ sgn = -1) ∧
        (e = 0 ∨ (none : Option (Fin τ.rank)) ∈ D) ∧
        (∀ j, 0 ≤ sgn * β j + (e : ℤ) * K.θ j) ∧
        (∀ j, sgn * β j + (e : ℤ) * K.θ j ≠ 0 → (some j : Option (Fin τ.rank)) ∈ D) := by
  constructor
  · rintro ⟨hβroot, n, hnD, hβn⟩
    have hex : ∃ i : Option (Fin τ.rank), i ∉ D := by
      by_contra h
      apply hD
      rw [Finset.eq_univ_iff_forall]
      intro x
      by_contra hx
      exact h ⟨x, hx⟩
    have hle1 : n none ≤ 1 := by
      by_cases hnone : (none : Option (Fin τ.rank)) ∈ D
      · obtain ⟨i, hi⟩ := hex
        rcases i with _ | j
        · exact absurd hnone hi
        · have hnj : n (some j) = 0 := by
            by_contra h
            exact hi (hnD (some j) h)
          have hθpos : 0 < K.θ j := hK.θ_pos j
          have habs : |β j| ≤ K.θ j := by
            rcases hβroot.nonneg_or_nonpos with hpos | hneg
            · rw [abs_of_nonneg (hpos j)]
              exact hK.le_θ β hβroot hpos j
            · rw [abs_of_nonpos (hneg j)]
              have := hK.le_θ (-β) (isRoot_neg_iff.mpr hβroot)
                (fun k => neg_nonneg.mpr (hneg k)) j
              simpa using this
          have hkey : (n none : ℤ) * K.θ j ≤ K.θ j := by
            rcases hβn with h | h
            · have hβj : β j = -(n none : ℤ) * K.θ j := by
                rw [h, levTwoS3b_combo_apply, hnj]; ring
              rw [hβj, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg _),
                abs_of_pos hθpos] at habs
              exact habs
            · have hβj : β j = (n none : ℤ) * K.θ j := by
                rw [h]
                simp only [Pi.neg_apply, levTwoS3b_combo_apply, hnj]
                ring
              rw [hβj, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hθpos.le)] at habs
              exact habs
          have : (n none : ℤ) ≤ 1 := by nlinarith
          omega
      · have : n none = 0 := by
          by_contra h
          exact hnone (hnD none h)
        omega
    rcases hβn with h | h
    · refine ⟨n none, 1, hle1, Or.inl rfl, ?_, ?_, ?_⟩
      · by_cases he : n none = 0
        · exact Or.inl he
        · exact Or.inr (hnD none he)
      · intro j
        rw [h, levTwoS3b_combo_apply]
        have : (0 : ℤ) ≤ (n (some j) : ℤ) := Nat.cast_nonneg _
        linarith
      · intro j
        rw [h, levTwoS3b_combo_apply]
        intro hj
        refine hnD (some j) (fun h0 => hj ?_)
        rw [h0]; ring
    · refine ⟨n none, -1, hle1, Or.inr rfl, ?_, ?_, ?_⟩
      · by_cases he : n none = 0
        · exact Or.inl he
        · exact Or.inr (hnD none he)
      · intro j
        rw [h]
        simp only [Pi.neg_apply, levTwoS3b_combo_apply]
        have : (0 : ℤ) ≤ (n (some j) : ℤ) := Nat.cast_nonneg _
        linarith
      · intro j
        rw [h]
        simp only [Pi.neg_apply, levTwoS3b_combo_apply]
        intro hj
        refine hnD (some j) (fun h0 => hj ?_)
        rw [h0]; ring
  · rintro ⟨e, sgn, he, hsgn, hnone, hnonneg, hsupp⟩
    let n : Option (Fin τ.rank) → ℕ := fun x =>
      match x with
      | none => e
      | some j => (sgn * β j + (e : ℤ) * K.θ j).toNat
    have hn_none : n none = e := rfl
    have hn_some : ∀ j, n (some j) = (sgn * β j + (e : ℤ) * K.θ j).toNat := fun j => rfl
    refine ⟨hβ, n, ?_, ?_⟩
    · intro x hx
      cases x with
      | none =>
          rw [hn_none] at hx
          rcases hnone with he0 | hmem
          · rw [he0] at hx
            exact absurd rfl hx
          · exact hmem
      | some j =>
          rw [hn_some j] at hx
          exact hsupp j (by
            intro h0
            exact hx (by rw [h0, Int.toNat_zero]))
    · rcases hsgn with hsgn | hsgn
      · left
        funext j
        rw [levTwoS3b_combo_apply, hn_none, hn_some, hsgn, one_mul]
        have h2 : (0 : ℤ) ≤ β j + (e : ℤ) * K.θ j := by
          have := hnonneg j
          rw [hsgn, one_mul] at this
          exact this
        rw [Int.toNat_of_nonneg h2]
        ring
      · right
        funext j
        simp only [Pi.neg_apply]
        rw [levTwoS3b_combo_apply, hn_none, hn_some, hsgn, neg_one_mul]
        have h2 : (0 : ℤ) ≤ -β j + (e : ℤ) * K.θ j := by
          have := hnonneg j
          rw [hsgn, neg_one_mul] at this
          exact this
        rw [Int.toNat_of_nonneg h2]
        ring

theorem levTwoS3b_mem_rootsOf_iff_fin
    {τ : Tag} (K : KacData τ) (hK : K.Facts) (D : Finset (Option (Fin τ.rank)))
    (hD : D ≠ Finset.univ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    β ∈ K.rootsOf (D : Set (Option (Fin τ.rank))) ↔
      ∃ e : Fin 2, ∃ s : Fin 2,
        (e.val = 0 ∨ (none : Option (Fin τ.rank)) ∈ D) ∧
        (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * β j + (e.val : ℤ) * K.θ j) ∧
        (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * β j + (e.val : ℤ) * K.θ j ≠ 0 →
          (some j : Option (Fin τ.rank)) ∈ D) := by
  rw [levTwoS3b_mem_rootsOf_iff K hK D hD hβ]
  constructor
  · rintro ⟨e, sgn, he, hsgn, hnone, hnonneg, hsupp⟩
    have he2 : e = 0 ∨ e = 1 := by omega
    rcases he2 with rfl | rfl
    · rcases hsgn with rfl | rfl
      · refine ⟨0, 0, hnone, ?_, ?_⟩
        · intro j; simpa using hnonneg j
        · intro j; simpa using hsupp j
      · refine ⟨0, 1, hnone, ?_, ?_⟩
        · intro j; simpa using hnonneg j
        · intro j; simpa using hsupp j
    · rcases hsgn with rfl | rfl
      · refine ⟨1, 0, ?_, ?_, ?_⟩
        · rcases hnone with h | h
          · exact absurd h (by decide)
          · exact Or.inr h
        · intro j; simpa using hnonneg j
        · intro j; simpa using hsupp j
      · refine ⟨1, 1, ?_, ?_, ?_⟩
        · rcases hnone with h | h
          · exact absurd h (by decide)
          · exact Or.inr h
        · intro j; simpa using hnonneg j
        · intro j; simpa using hsupp j
  · rintro ⟨e, s, he, hnonneg, hsupp⟩
    fin_cases e <;> fin_cases s
    · exact ⟨0, 1, by omega, Or.inl rfl, by simp, by simpa using hnonneg,
        by simpa using hsupp⟩
    · exact ⟨0, -1, by omega, Or.inr rfl, by simp, by simpa using hnonneg,
        by simpa using hsupp⟩
    · exact ⟨1, 1, by omega, Or.inl rfl, by simpa using he, by simpa using hnonneg,
        by simpa using hsupp⟩
    · exact ⟨1, -1, by omega, Or.inr rfl, by simpa using he, by simpa using hnonneg,
        by simpa using hsupp⟩

end CFSG.StandardType.LevTwo
