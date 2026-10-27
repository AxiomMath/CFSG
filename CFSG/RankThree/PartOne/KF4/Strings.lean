module

public import CFSG.Adapters.TauCetiExceptional.MinusculeAdjointY

public section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley

@[expose] def f4Index (i : Fin 4) : Fin Tag.F4.rank := i

@[expose] def f4RootVec (m : Fin 48) : Fin Tag.F4.rank → ℤ := f4Certificate.root m

@[expose] def f4IsRootB (v : Fin Tag.F4.rank → ℤ) : Bool := decide (∃ m : Fin 48, f4RootVec m = v)

@[expose] def f4StrUp (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) : ℕ :=
  if f4IsRootB (v + (3 : ℤ) • Pi.single i 1) then 3
  else if f4IsRootB (v + (2 : ℤ) • Pi.single i 1) then 2
  else if f4IsRootB (v + Pi.single i 1) then 1 else 0

@[expose] def f4StrDown (i : Fin Tag.F4.rank) (v : Fin Tag.F4.rank → ℤ) : ℕ :=
  if f4IsRootB (v - (3 : ℤ) • Pi.single i 1) then 3
  else if f4IsRootB (v - (2 : ℤ) • Pi.single i 1) then 2
  else if f4IsRootB (v - Pi.single i 1) then 1 else 0

section Thms


theorem f4_roots_length : f4Certificate.roots.length = 48 := by decide +kernel

theorem isRoot_f4RootVec (m : Fin 48) : IsRoot Tag.F4 (f4RootVec m) :=
  RootCertificate.isRoot_root f4Certificate_check m (by rw [f4_roots_length]; exact m.2)

theorem isRoot_iff_exists_f4RootVec {v : Fin Tag.F4.rank → ℤ} :
    IsRoot Tag.F4 v ↔ ∃ m : Fin 48, f4RootVec m = v := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => hm ▸ isRoot_f4RootVec m⟩
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq f4Certificate_check h
  exact ⟨⟨k, f4_roots_length ▸ hk⟩, rfl⟩

theorem isRoot_iff_f4IsRootB {v : Fin Tag.F4.rank → ℤ} : IsRoot Tag.F4 v ↔ f4IsRootB v = true := by
  rw [isRoot_iff_exists_f4RootVec, f4IsRootB, decide_eq_true_iff]

end Thms

section StringLengths


theorem stringUp_down_F4 (i : Fin Tag.F4.rank) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot Tag.F4 α)
    (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1) :
    stringUp Tag.F4 i α = f4StrUp i α ∧ stringDown Tag.F4 i α = f4StrDown i α := by
  obtain ⟨hpq, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  have e : ∀ m : ℤ, f4IsRootB (α + m • Pi.single i 1) = true ↔
      (-(stringDown Tag.F4 i α : ℤ) ≤ m ∧ m ≤ stringUp Tag.F4 i α) := fun m => by
    rw [← isRoot_iff_f4IsRootB]
    exact hint m
  have e' : ∀ m : ℤ, f4IsRootB (α - m • Pi.single i 1) = true ↔
      (-(stringUp Tag.F4 i α : ℤ) ≤ m ∧ m ≤ stringDown Tag.F4 i α) := fun m => by
    have := e (-m)
    rw [neg_smul, ← sub_eq_add_neg] at this
    rw [this]
    omega
  have e1 : f4IsRootB (α + Pi.single i 1) = true ↔
      (-(stringDown Tag.F4 i α : ℤ) ≤ 1 ∧ 1 ≤ stringUp Tag.F4 i α) := by simpa using e 1
  have e1' : f4IsRootB (α - Pi.single i 1) = true ↔
      (-(stringUp Tag.F4 i α : ℤ) ≤ 1 ∧ 1 ≤ stringDown Tag.F4 i α) := by simpa using e' 1
  constructor
  · rw [f4StrUp]
    by_cases a : f4IsRootB (α + (3 : ℤ) • Pi.single i 1) = true
    · rw [ite_eq_left a]; have := (e 3).1 a; omega
    · rw [ite_eq_right a]
      have a' := mt (e 3).2 a
      by_cases b : f4IsRootB (α + (2 : ℤ) • Pi.single i 1) = true
      · rw [ite_eq_left b]; have := (e 2).1 b; omega
      · rw [ite_eq_right b]
        have b' := mt (e 2).2 b
        by_cases c : f4IsRootB (α + Pi.single i 1) = true
        · rw [ite_eq_left c]; have := e1.1 c; omega
        · rw [ite_eq_right c]
          have c' := mt e1.2 c
          omega
  · rw [f4StrDown]
    by_cases a : f4IsRootB (α - (3 : ℤ) • Pi.single i 1) = true
    · rw [ite_eq_left a]; have := (e' 3).1 a; omega
    · rw [ite_eq_right a]
      have a' := mt (e' 3).2 a
      by_cases b : f4IsRootB (α - (2 : ℤ) • Pi.single i 1) = true
      · rw [ite_eq_left b]; have := (e' 2).1 b; omega
      · rw [ite_eq_right b]
        have b' := mt (e' 2).2 b
        by_cases c : f4IsRootB (α - Pi.single i 1) = true
        · rw [ite_eq_left c]; have := e1'.1 c; omega
        · rw [ite_eq_right c]
          have c' := mt e1'.2 c
          omega

end StringLengths


section Strings

variable {τ : Tag} (R : Type*)
  [CommRing R]

open CFSG.TauCetiBridge.Minuscule in
theorem xOp_rootVec_of_short_string (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hpq : ¬(IsRoot τ (α + Pi.single i 1) ∧ IsRoot τ (α - Pi.single i 1)))
    (hp2 : ¬IsRoot τ (α + (2 : ℤ) • Pi.single i 1)) :
    xOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α + Pi.single i 1) := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  rw [xOp_rootVec_of_ne' R i c hα h₁ h₂]
  by_cases hr : IsRoot τ (α + Pi.single i 1)
  · have h1 := (hint 1).1 (by rwa [one_smul])
    have hp : stringUp τ i α = 1 := by
      have hle : stringUp τ i α < 2 := by
        by_contra hge
        exact hp2 ((hint 2).2 ⟨by omega, by omega⟩)
      omega
    have hq : stringDown τ i α = 0 := by
      by_contra hne
      have : IsRoot τ (α + (-1 : ℤ) • Pi.single i 1) := (hint (-1)).2 ⟨by omega, by omega⟩
      rw [neg_smul, one_smul, ← sub_eq_add_neg] at this
      exact hpq ⟨hr, this⟩
    rw [hp, hq, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  · have hp : stringUp τ i α = 0 := by
      by_contra hne
      exact hr (by simpa using (hint 1).2 ⟨by omega, by omega⟩)
    have hz : rootVec τ R (α + Pi.single i 1) = 0 := by
      rw [rootVec, dite_eq_right hr]
    rw [hp, Finset.sum_range_one, hz]
    simp

open CFSG.TauCetiBridge.Minuscule in
theorem yOp_rootVec_of_short_string (i : Fin τ.rank) (c : R) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h₁ : α ≠ Pi.single i 1) (h₂ : α ≠ -Pi.single i 1)
    (hpq : ¬(IsRoot τ (α + Pi.single i 1) ∧ IsRoot τ (α - Pi.single i 1)))
    (hq2 : ¬IsRoot τ (α - (2 : ℤ) • Pi.single i 1)) :
    yOp τ R i c (rootVec τ R α) = rootVec τ R α + c • rootVec τ R (α - Pi.single i 1) := by
  obtain ⟨-, hint⟩ := isRoot_add_smul_single_iff hα i h₁ h₂
  rw [yOp_rootVec_of_ne' R i c hα h₁ h₂]
  by_cases hr : IsRoot τ (α - Pi.single i 1)
  · have h1 := (hint (-1)).1 (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
    have hq : stringDown τ i α = 1 := by
      have hle : stringDown τ i α < 2 := by
        by_contra hge
        apply hq2
        have := (hint (-2)).2 ⟨by omega, by omega⟩
        rwa [neg_smul, ← sub_eq_add_neg] at this
      omega
    have hp : stringUp τ i α = 0 := by
      by_contra hne
      have : IsRoot τ (α + (1 : ℤ) • Pi.single i 1) := (hint 1).2 ⟨by omega, by omega⟩
      rw [one_smul] at this
      exact hpq ⟨this, hr⟩
    rw [hp, hq, Finset.sum_range_succ, Finset.sum_range_one]
    simp
  · have hq : stringDown τ i α = 0 := by
      by_contra hne
      have : IsRoot τ (α + (-1 : ℤ) • Pi.single i 1) := (hint (-1)).2 ⟨by omega, by omega⟩
      rw [neg_smul, one_smul, ← sub_eq_add_neg] at this
      exact hr this
    have hz : rootVec τ R (α - Pi.single i 1) = 0 := by
      rw [rootVec, dite_eq_right hr]
    rw [hq, Finset.sum_range_one, hz]
    simp

end Strings

end CFSG.RankThree.PartOne.KF4
