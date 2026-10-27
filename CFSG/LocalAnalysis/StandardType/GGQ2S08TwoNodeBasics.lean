module

public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteQTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2S08RowA {G : Type} [Group G] (p N : ℕ) (X J : Subgroup G) : Prop :=
  ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
    LargeEvenMarking J (fun lab _ _ _ _ _ => lab = labJ) ∧ labJ.tag = .A ∧ labX.tag = .A ∧
    labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧ p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n - 1 ∧
    labJ.rank + 3 = N

@[expose] def GGQ2S08RowTwA {G : Type} [Group G] (p N : ℕ) (X J : Subgroup G) : Prop :=
  ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
    LargeEvenMarking J (fun lab _ _ _ _ _ => lab = labJ) ∧ labJ.tag = .twA ∧ labX.tag = .twA ∧
    labX.rank = labJ.rank + 2 ∧ labX.n = labJ.n ∧ p ∣ labJ.rank + 3 ∧ p ∣ 2 ^ labJ.n + 1 ∧
    labJ.rank + 3 = N

@[expose] def GGQ2S08RowE6 {G : Type} [Group G] (p : ℕ) (X J : Subgroup G) : Prop :=
  ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
    LargeEvenMarking J (fun lab _ _ _ _ _ => lab = labJ) ∧ labJ.tag = .D ∧ labJ.rank = 4 ∧
    labX.tag = .E6 ∧ labX.n = labJ.n ∧ p = 3 ∧ p ∣ 2 ^ labJ.n - 1

@[expose] def GGQ2S08RowTwE6 {G : Type} [Group G] (p : ℕ) (X J : Subgroup G) : Prop :=
  ∃ labX labJ : LargeEvenLabel, LargeEvenMarking X (fun lab _ _ _ _ _ => lab = labX) ∧
    LargeEvenMarking J (fun lab _ _ _ _ _ => lab = labJ) ∧ labJ.tag = .D ∧ labJ.rank = 4 ∧
    labX.tag = .twE6 ∧ labX.n = labJ.n ∧ p = 3 ∧ p ∣ 2 ^ labJ.n + 1

theorem ggQ2s08_row_cases {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (h : GGQTwoTwoNodeRowAt p X J) :
    (∃ N, GGQ2S08RowA p N X J) ∨ (∃ N, GGQ2S08RowTwA p N X J) ∨ GGQ2S08RowE6 p X J ∨
      GGQ2S08RowTwE6 p X J := by
  obtain ⟨labX, labJ, hX, hJ, h | h | h | h⟩ := h
  · exact Or.inl ⟨_, labX, labJ, hX, hJ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2, rfl⟩
  · exact Or.inr (Or.inl ⟨_, labX, labJ, hX, hJ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨labX, labJ, hX, hJ, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨labX, labJ, hX, hJ, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2⟩))

abbrev GGQ2S08Pos : Type 1 := ∀ {G : Type} [Group G], ℕ → Subgroup G → Subgroup G → Prop

@[expose] def GGQ2S08TNCell (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ((P p L J ∧ x ∉ L) ∨ (P p K J ∧ y ∉ K)) →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2S08TNCellK (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      P p K J → y ∉ K →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2S08NoNbrCell (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ((P p L J ∧ x ∉ L) ∨ (P p K J ∧ y ∉ K)) → False

@[expose] def GGQ2S08NoNbrCellL (P : GGQ2S08Pos) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      P p L J → x ∉ L → False

@[expose] def GGQ2S08PosTwA (N : ℕ) : GGQ2S08Pos := fun p X J => GGQ2S08RowTwA p N X J

@[expose] def GGQ2S08PosTwABig : GGQ2S08Pos := fun p X J => ∃ N, 12 ≤ N ∧ GGQ2S08RowTwA p N X J

@[expose] def GGQ2S08PosABig : GGQ2S08Pos := fun p X J => ∃ N, 12 ≤ N ∧ GGQ2S08RowA p N X J

@[expose] def GGQ2S08PosTwE6 : GGQ2S08Pos := fun p X J => GGQ2S08RowTwE6 p X J

@[expose] def GGQ2S08PosUntw : GGQ2S08Pos := fun p X J =>
  (∃ N, GGQ2S08RowA p N X J) ∨ GGQ2S08RowE6 p X J

theorem ggQ2s08_pos_cases {G : Type} [Group G] {p : ℕ} (hp : p = 3) {X J : Subgroup G}
    (hX : GGQTwoTwoNodeRowAt p X J) :
    GGQ2S08PosUntw p X J ∨ GGQ2S08PosTwE6 p X J ∨ GGQ2S08PosTwA 3 p X J ∨
      GGQ2S08PosTwA 6 p X J ∨ GGQ2S08PosTwA 9 p X J ∨ GGQ2S08PosTwABig p X J := by
  rcases ggQ2s08_row_cases hX with ⟨N, h⟩ | ⟨N, h⟩ | h | h
  · exact Or.inl (Or.inl ⟨N, h⟩)
  · have hN : N = 3 ∨ N = 6 ∨ N = 9 ∨ 12 ≤ N := by
      obtain ⟨_, labJ, -, -, -, -, -, -, hpd, -, hN⟩ := h
      rw [hp] at hpd
      omega
    rcases hN with rfl | rfl | rfl | h12
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨N, h12, h⟩))))
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem ggQ2s08b_twA_three_row_false {G : Type} [Group G] {p : ℕ} {X J : Subgroup G}
    (hr : GGQ2S08RowTwA p 3 X J) : False := by
  obtain ⟨labX, labJ, -, hmJ, htJ, -, -, -, -, -, hN⟩ := hr
  have hrank : labJ.rank = 0 := by omega
  obtain ⟨lab, hlab, hlabJ, -⟩ := FrameRoute.ggFrameQTwo_exists_hasLabel hmJ
  rw [hlabJ] at hlab
  have h2 : 2 ≤ labJ.rank := by
    unfold LargeEvenInLambda2 at hlab
    rw [htJ] at hlab
    exact hlab.2.1
  omega

theorem ggQ2s08_tn3_holds : GGQ2S08NoNbrCell (GGQ2S08PosTwA 3) := by
  intro G _ _ p _ _ B Bs x L D J _ _ y K _ hrow
  rcases hrow with ⟨hr, -⟩ | ⟨hr, -⟩
  · exact ggQ2s08b_twA_three_row_false hr
  · exact ggQ2s08b_twA_three_row_false hr

private theorem ggQ2s08b_untw_compat_false_A {p : ℕ} {labX labJ : LargeEvenLabel}
    (hp : p = 3) (hn : labX.n = labJ.n) (hrk : labX.rank = labJ.rank + 2)
    (hdiv : p ∣ 2 ^ labJ.n - 1) : ¬ FrameRoute.ggFrameQTwo_QTwoCompat labX := by
  have hdivX : 3 ∣ 2 ^ labX.n - 1 := by
    rw [hp, ← hn] at hdiv
    exact hdiv
  have hn1 : labX.n ≠ 1 := by
    intro h1
    rw [h1] at hdivX
    norm_num at hdivX
  have hrk1 : labX.rank ≠ 1 := by
    intro h1
    rw [hrk] at h1
    omega
  intro hc
  rcases hc with h | ⟨-, h, -⟩
  · exact hn1 h
  · exact hrk1 h

private theorem ggQ2s08b_untw_compat_false_E6 {p : ℕ} {labX labJ : LargeEvenLabel}
    (hp : p = 3) (hn : labX.n = labJ.n) (htX : labX.tag = .E6)
    (hdiv : p ∣ 2 ^ labJ.n - 1) : ¬ FrameRoute.ggFrameQTwo_QTwoCompat labX := by
  have hdivX : 3 ∣ 2 ^ labX.n - 1 := by
    rw [hp, ← hn] at hdiv
    exact hdiv
  have hn1 : labX.n ≠ 1 := by
    intro h1
    rw [h1] at hdivX
    norm_num at hdivX
  intro hc
  rcases hc with h | ⟨htA, -, -⟩
  · exact hn1 h
  · exact absurd (htA.symm.trans htX) (by decide)

theorem ggQ2s08_untwL_holds :
    GGQ2S08NoNbrCellL GGQ2S08PosUntw := by
  intro G _ _ p _ hp B Bs x L D J hS hI1 y K hnb hr hx
  have h₁ : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.n < 2) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hS.2.1
  rcases hr with
    ⟨N, labX, labJ, hmX, hmJ, htJ, htX, hrk, hn, hpd, hdiv, hN⟩ |
      ⟨labX, labJ, hmX, hmJ, htJ, hrkJ, htX, hn, hp3, hdiv⟩
  · refine FrameRoute.ggFrameQTwo_qTwoLabel h₁ ?_
    refine largeEvenMarking_mono (fun lab R _ I F θ h => ?_) hmX
    rw [h]
    exact ggQ2s08b_untw_compat_false_A hp hn hrk hdiv
  · refine FrameRoute.ggFrameQTwo_qTwoLabel h₁ ?_
    refine largeEvenMarking_mono (fun lab R _ I F θ h => ?_) hmX
    rw [h]
    exact ggQ2s08b_untw_compat_false_E6 hp3 hn htX hdiv

end CFSG.StandardType

end

