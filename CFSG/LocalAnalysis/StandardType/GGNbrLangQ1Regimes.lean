module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorJInputs
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section
namespace CFSG.StandardType.S2MathAs51642Interfaces
open CFSG CFSG.Assembly

@[expose] def GGBstarInnerDiagJInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    CFSG.StandardType.LargeEvenMarking L (fun lab _ _ I _ θ =>
      S p lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    GGInnerDiagOn Bs J

@[expose] def Q1SelectedTransfer (S : ℕ → LargeEvenLabel → Prop)
    (Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    GGMarkingAll (K := ↥L) (fun lab _ _ I _ θ =>
      S p lab → Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      CFSG.StandardType.LargeEvenMarking J (fun labJ _ _ IJ _ θJ =>
        Rel p lab labJ ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ IJ,
            LargeEvenInduces θJ (fun j j' => (j' : G) = b⁻¹ * j * b) φ))

@[expose] def Q1ComponentConclusion {X : Type} [Group X]
    (p : ℕ) (lab : LargeEvenLabel) (A : Subgroup (MulAut X)) (J : Subgroup X)
    (Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  CFSG.StandardType.LargeEvenMarking J (fun labJ _ _ IJ _ θJ =>
    Rel p lab labJ ∧
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ IJ)

@[expose] def Q1ToralActionTransfer
    (Toral : (R : Type) → [Group R] → Subgroup (MulAut R) → Prop)
    (S : ℕ → LargeEvenLabel → Prop)
    (Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab (fun R _ I _ =>
      ∀ (X : Type) [Group X] [Finite X], commutator X = ⊤ →
      ∀ (θ : X ⧸ Subgroup.center X ≃* R) (A : Subgroup (MulAut X)),
      IsElemAbelian p A → GGInducedInn A θ I →
      Toral R (A.map (ggInducedAut θ)) →
      ∀ u : MulAut X, u ∈ A → orderOf u = p →
      ∀ J : Subgroup X, CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u) →
        Q1ComponentConclusion p lab A J Rel)

@[expose] def SmallDerived (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def CenterPrimeTo (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ SmallDerived p lab ∧
  match lab.tag with
  | .A => ¬ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1)
  | .twA => ¬ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1)
  | .E6 => ¬ (p = 3 ∧ 3 ∣ 2 ^ lab.n - 1)
  | .twE6 => ¬ (p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)
  | _ => True

@[expose] def LinearTorsion (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∧ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1)

@[expose] def UnitaryTorsion (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n + 1) ∧
    ¬ (lab.rank = 5 ∧ p = 3)

@[expose] def PGU6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def E6Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1

@[expose] def TwE6Three (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

abbrev Q1UnitaryTorsion : Prop := GGBstarInnerDiagJInputOn UnitaryTorsion
abbrev Q1PGU6 : Prop := GGBstarInnerDiagJInputOn PGU6
abbrev Q1E6Three : Prop := GGBstarInnerDiagJInputOn E6Three
abbrev Q1TwE6Three : Prop := GGBstarInnerDiagJInputOn TwE6Three
abbrev Q1SmallDerived : Prop := GGBstarInnerDiagJInputOn SmallDerived

theorem selector_cover (p : ℕ) (lab : LargeEvenLabel) :
    CenterPrimeTo p lab ∨ LinearTorsion p lab ∨ UnitaryTorsion p lab ∨ PGU6 p lab ∨
      E6Three p lab ∨ TwE6Three p lab ∨ SmallDerived p lab := by
  rcases lab with ⟨tag, rank, n⟩
  cases tag
  ·
    by_cases h : p ∣ Nat.gcd (rank + 1) (2 ^ n - 1)
    · exact Or.inr (Or.inl ⟨rfl, h⟩)
    · exact Or.inl ⟨by simp [SmallDerived], h⟩
  ·
    by_cases h : p ∣ Nat.gcd (rank + 1) (2 ^ n + 1)
    · by_cases h5 : rank = 5 ∧ p = 3
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h5.1, h5.2,
          dvd_trans (h5.2 ▸ h) (Nat.gcd_dvd_right _ _)⟩)))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h, h5⟩))
    · exact Or.inl ⟨by simp [SmallDerived], h⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  ·
    by_cases h : p = 3 ∧ 3 ∣ 2 ^ n - 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h.1, h.2⟩))))
    · exact Or.inl ⟨by simp [SmallDerived], h⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  ·
    by_cases h : p = 3 ∧ 3 ∣ 2 ^ n + 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h.1, h.2⟩)))))
    · exact Or.inl ⟨by simp [SmallDerived], h⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inl ⟨by simp [SmallDerived], trivial⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))

theorem q1On_true_iff : GGBstarInnerDiagJInputOn (fun _ _ => True) ↔
    CFSG.StandardType.GGBstarInnerDiagJInput := by
  constructor
  · intro h G _ _ p B Bs x L D J hcfg hmark
    exact h G p B Bs x L D J hcfg
      (largeEvenMarking_mono (fun lab R _ I F θ hp => ⟨trivial, hp⟩) hmark)
  · intro h G _ _ p B Bs x L D J hcfg hmark
    exact h G p B Bs x L D J hcfg
      (largeEvenMarking_mono (fun lab R _ I F θ hp => hp.2) hmark)

theorem q1On_or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGBstarInnerDiagJInputOn S) (hT : GGBstarInnerDiagJInputOn T) :
    GGBstarInnerDiagJInputOn (fun p lab => S p lab ∨ T p lab) := by
  intro G _ _ p B Bs x L D J hcfg hmark
  obtain ⟨hperf, lab, hlab, hraw⟩ := hmark
  by_cases hSp : S p lab
  · refine hS G p B Bs x L D J hcfg ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, _, hBs, hact⟩ := hh
    exact ⟨hs, hna, θ, hSp, hBs, hact⟩
  · refine hT G p B Bs x L D J hcfg ⟨hperf, lab, hlab, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F hh => ?_) hraw
    obtain ⟨hs, hna, θ, hST, hBs, hact⟩ := hh
    rcases hST with h | h
    · exact absurd h hSp
    · exact ⟨hs, hna, θ, h, hBs, hact⟩

theorem q1On_of_and_not {S T : ℕ → LargeEvenLabel → Prop}
    (hT : GGBstarInnerDiagJInputOn T)
    (hST : GGBstarInnerDiagJInputOn (fun p lab => S p lab ∧ ¬ T p lab)) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hmark
  refine q1On_or hST hT G p B Bs x L D J hcfg ?_
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ⟨?_, h.2⟩) hmark
  by_cases hTp : T p lab
  · exact Or.inr hTp
  · exact Or.inl ⟨h.1, hTp⟩

theorem q1On_of_selectedTransfer {S : ℕ → LargeEvenLabel → Prop}
    {Rel : ℕ → LargeEvenLabel → LargeEvenLabel → Prop}
    (h : Q1SelectedTransfer S Rel) : GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hmark
  have hAll := h G p B Bs x L D J hcfg
  obtain ⟨-, lab, R, hR, I, F, θ, hΛ, hP, hQ⟩ :=
    largeEvenMarking_exists' (hAll _ hmark)
  obtain ⟨hS, hNL, hact⟩ := hP
  exact largeEvenMarking_mono (fun labJ R' _ I' F' θJ hh => ⟨hh.2.1, hh.2.2⟩)
    (hQ hS hNL hact)

end CFSG.StandardType.S2MathAs51642Interfaces
