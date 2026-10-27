module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKGOneOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGForkRootSL2Label p lab →
    S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I

@[expose] def GGKGTwoOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → GGForkLatticeLabel p lab →
    S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusLattice p r R I

theorem GGKGOneOn.mono {S S' : ℕ → LargeEvenLabel → Prop} (h : GGKGOneOn S')
    (hS : ∀ p lab, S p lab → S' p lab) : GGKGOneOn S :=
  fun p lab hp hlab hl hs => h p lab hp hlab hl (hS _ _ hs)

theorem GGKGTwoOn.mono {S S' : ℕ → LargeEvenLabel → Prop} (h : GGKGTwoOn S')
    (hS : ∀ p lab, S p lab → S' p lab) : GGKGTwoOn S :=
  fun p lab hp hlab hl hs => h p lab hp hlab hl (hS _ _ hs)

inductive GGKGRow
  | aSplit | aSplitDvd | aNonsplit | aNonsplitDvd
  | uSplit | uSplitDvd | uNonsplit | uNonsplitDvd
  | spSplit | spNonsplit | dSplit | dNonsplit | twdSplit | twdNonsplit
  | e6Split | e6Nonsplit | e7Split | e7Nonsplit | e8Split | e8Nonsplit
  | f4Split | f4Nonsplit | twe6Split | twe6Nonsplit | small

@[expose] def GGKGRowLabel : GGKGRow → ℕ → LargeEvenLabel → Prop
  | .aSplit, p, lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1
  | .aSplitDvd, p, lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1
  | .aNonsplit, p, lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1
  | .aNonsplitDvd, p, lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1
  | .uSplit, p, lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1
  | .uSplitDvd, p, lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ p ∣ lab.rank + 1
  | .uNonsplit, p, lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ p ∣ lab.rank + 1
  | .uNonsplitDvd, p, lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.rank + 1
  | .spSplit, p, lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n - 1
  | .spNonsplit, p, lab => (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n + 1
  | .dSplit, p, lab => lab.tag = .D ∧ p ∣ 2 ^ lab.n - 1
  | .dNonsplit, p, lab => lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1
  | .twdSplit, p, lab => lab.tag = .twD ∧ p ∣ 2 ^ lab.n - 1
  | .twdNonsplit, p, lab => lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1
  | .e6Split, p, lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1
  | .e6Nonsplit, p, lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1
  | .e7Split, p, lab => lab.tag = .E7 ∧ p ∣ 2 ^ lab.n - 1
  | .e7Nonsplit, p, lab => lab.tag = .E7 ∧ p ∣ 2 ^ lab.n + 1
  | .e8Split, p, lab => lab.tag = .E8 ∧ p ∣ 2 ^ lab.n - 1
  | .e8Nonsplit, p, lab => lab.tag = .E8 ∧ p ∣ 2 ^ lab.n + 1
  | .f4Split, p, lab => lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1
  | .f4Nonsplit, p, lab => lab.tag = .F4 ∧ p ∣ 2 ^ lab.n + 1
  | .twe6Split, p, lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1
  | .twe6Nonsplit, p, lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1
  | .small, _, lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

theorem ggKG_dvd_of_split {p : ℕ} {lab : LargeEvenLabel} (hp5 : 5 ≤ p)
    (hs : LargeEvenSplit p lab) : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  rcases hs with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, hp3⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h
  · omega

theorem ggKG_dvd_of_lattice {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hl : GGForkLatticeLabel p lab) : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1 := by
  have h1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
  have h4 : 4 ^ lab.n = 2 ^ lab.n * 2 ^ lab.n := by rw [← mul_pow]; norm_num
  have hprod : (2 ^ lab.n - 1) * (2 ^ lab.n + 1) = 4 ^ lab.n - 1 := by
    rw [h4]
    zify [h1, Nat.one_le_iff_ne_zero.mpr (by positivity : 2 ^ lab.n * 2 ^ lab.n ≠ 0)]
    ring
  have hd := hl.2.2
  rw [← hprod] at hd
  exact hp.dvd_mul.mp hd

private theorem ggKG_cover {p : ℕ} {lab : LargeEvenLabel} (h : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) :
    ∃ i : GGKGRow, GGKGRowLabel i p lab := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with h | h <;> by_cases hd : p ∣ l + 1 <;>
    cases t <;> simp only at h <;>
    first
      | exact ⟨.aSplit, rfl, h, hd⟩ | exact ⟨.aSplitDvd, rfl, h, hd⟩
      | exact ⟨.aNonsplit, rfl, h, hd⟩ | exact ⟨.aNonsplitDvd, rfl, h, hd⟩
      | exact ⟨.uSplit, rfl, h, hd⟩ | exact ⟨.uSplitDvd, rfl, h, hd⟩
      | exact ⟨.uNonsplit, rfl, h, hd⟩ | exact ⟨.uNonsplitDvd, rfl, h, hd⟩
      | exact ⟨.spSplit, Or.inl rfl, h⟩ | exact ⟨.spSplit, Or.inr rfl, h⟩
      | exact ⟨.spNonsplit, Or.inl rfl, h⟩ | exact ⟨.spNonsplit, Or.inr rfl, h⟩
      | exact ⟨.dSplit, rfl, h⟩ | exact ⟨.dNonsplit, rfl, h⟩
      | exact ⟨.twdSplit, rfl, h⟩ | exact ⟨.twdNonsplit, rfl, h⟩
      | exact ⟨.e6Split, rfl, h⟩ | exact ⟨.e6Nonsplit, rfl, h⟩
      | exact ⟨.e7Split, rfl, h⟩ | exact ⟨.e7Nonsplit, rfl, h⟩
      | exact ⟨.e8Split, rfl, h⟩ | exact ⟨.e8Nonsplit, rfl, h⟩
      | exact ⟨.f4Split, rfl, h⟩ | exact ⟨.f4Nonsplit, rfl, h⟩
      | exact ⟨.twe6Split, rfl, h⟩ | exact ⟨.twe6Nonsplit, rfl, h⟩
      | exact ⟨.small, Or.inl rfl⟩ | exact ⟨.small, Or.inr (Or.inl rfl)⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inl rfl))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
      | exact ⟨.small, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))⟩

theorem ggKGRow_cover_one {p : ℕ} {lab : LargeEvenLabel} (hl : GGForkRootSL2Label p lab) :
    ∃ i : GGKGRow, GGKGRowLabel i p lab :=
  ggKG_cover (ggKG_dvd_of_split hl.1 hl.2)

theorem ggKGRow_cover_two {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hl : GGForkLatticeLabel p lab) : ∃ i : GGKGRow, GGKGRowLabel i p lab :=
  ggKG_cover (ggKG_dvd_of_lattice hp hl)

theorem ggForkRootSL2KGInput_of_rows (h : ∀ i, GGKGOneOn (GGKGRowLabel i)) :
    GGForkRootSL2KGInput := by
  intro p lab hp hlab hl
  obtain ⟨i, hi⟩ := ggKGRow_cover_one hl
  exact h i p lab hp hlab hl hi

theorem ggForkLatticeKGInput_of_rows (h : ∀ i, GGKGTwoOn (GGKGRowLabel i)) :
    GGForkLatticeKGInput := by
  intro p lab hp hlab hl
  obtain ⟨i, hi⟩ := ggKGRow_cover_two hp hl
  exact h i p lab hp hlab hl hi

end CFSG.StandardType
