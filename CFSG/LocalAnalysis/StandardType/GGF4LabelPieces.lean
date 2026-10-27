module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4SmallDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGF4SmallRes
    {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)) : Prop :=
  GGSecFiveRouteCfg p B Bs x L D J ks ∧ ¬ GGSecFiveTier1Region p B Bs x L D J ∧
    (∃ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs ks)),
      GGCoxeterPres p (ggAutomizerJoin L Bs ks) M e ∧ GGIsWeylMatrixF4 M) ∧
    GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) ∧
    (∀ K ∈ ks, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs ks)

@[expose] def GGF4LabelOrig
    (p : ℕ) (XL : Type) [Group XL] : Prop :=
  ∃ f : ℕ, 2 ≤ f ∧
    ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ XL) ∨ (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ XL))

@[expose] def GGF4LabelRow
    (p : ℕ) (XL XK : Type) [Group XL] [Group XK] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ XL ∧ GGHasLabel ⟨.C, 3, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ XL ∧ GGHasLabel ⟨.twD, 4, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ XL ∧ GGHasLabel ⟨.C, 3, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ XL ∧ GGHasLabel ⟨.twD, 4, f⟩ XK) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, 2 * f⟩ XL ∧ GGHasLabel ⟨.twA, 5, f⟩ XK) ∨
  (p = 3 ∧ GGHasLabel ⟨.A, 3, 2⟩ XL ∧ GGHasLabel ⟨.A, 5, 1⟩ XK) ∨
  (p = 3 ∧ GGHasLabel ⟨.A, 3, 2⟩ XL ∧ GGHasLabel ⟨.A, 6, 1⟩ XK)

@[expose] def GGF4LabelH1
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      ∃ f : ℕ, 1 ≤ f ∧
        ((p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L)) ∨
          (p ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)))

@[expose] def GGF4LabelH2
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → ¬ GGHasLabel ⟨.twA, 3, 1⟩ (L ⧸ Subgroup.center L)

@[expose] def GGF4LabelH3
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      ∃ K₁ K₂ : Subgroup G, (∀ K : Subgroup G, K ∈ ks ↔ K = K₁ ∨ K = K₂) ∧ K₁ ≠ K₂ ∧
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K₁ Bs) ∧
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K₂ Bs) ∧
        ggAutomizer K₁ Bs ⊔ ggAutomizer K₂ Bs = ggAutomizerJoin L Bs ks

@[expose] def GGF4LabelH4
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      GGF4LabelOrig p (L ⧸ Subgroup.center L) →
      (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
      ∀ K ∈ ks, GGF4LabelRow p (L ⧸ Subgroup.center L) (K ⧸ Subgroup.center K)

@[expose] def GGF4LabelH5
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
      (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) →
      ∀ K ∈ ks, GGF4LabelRow p (L ⧸ Subgroup.center L) (K ⧸ Subgroup.center K) →
        p = 3 ∧ GGHasLabel ⟨.A, 3, 2⟩ (L ⧸ Subgroup.center L) ∧
          GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K)

theorem ggSecFiveF4SmallLabelInput_of_pieces
    (h1 : GGF4LabelH1) (h2 : GGF4LabelH2) (h3 : GGF4LabelH3) (h4 : GGF4LabelH4)
    (h5 : GGF4LabelH5) : GGSecFiveF4SmallLabelInput := by
  intro G _ _ p B Bs x L D J ks hR hT1 ι M e hP hF hA3 hnospan
  have hres : GGF4SmallRes p B Bs x L D J ks := ⟨hR, hT1, ⟨ι, M, e, hP, hF⟩, hA3, hnospan⟩
  obtain ⟨K₁, K₂, hks, -, hB1, hB2, -⟩ := h3 G p B Bs x L D J ks hres
  have hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs) := by
    intro K hK
    rcases (hks K).1 hK with rfl | rfl
    · exact hB1
    · exact hB2
  have hp : p.Prime := hR.1.1.tableB_facts.1
  have hL : GGF4LabelOrig p (L ⧸ Subgroup.center L) := by
    obtain ⟨f, hf, h | h⟩ := h1 G p B Bs x L D J ks hres
    · refine ⟨f, ?_, Or.inl h⟩
      by_contra hf2
      have hf1 : f = 1 := by omega
      subst hf1
      have h1' : p ∣ 1 := by simpa using h.1
      exact hp.one_lt.ne' (Nat.dvd_one.1 h1')
    · refine ⟨f, ?_, Or.inr h⟩
      by_contra hf2
      have hf1 : f = 1 := by omega
      subst hf1
      have h3p : p ∣ 3 := by simpa using h.1
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3p
      subst hp3
      exact h2 G B Bs x L D J hR.1.1 h.2
  have hne : ks.Nonempty := ⟨K₁, (hks K₁).2 (Or.inl rfl)⟩
  obtain ⟨K, hK⟩ := hne
  have hrow := h4 G p B Bs x L D J ks hres hL hB
  obtain ⟨hp3, hLlab, -⟩ := h5 G p B Bs x L D J ks hres hB K hK (hrow K hK)
  exact ⟨hp3, hLlab, fun K' hK' => (h5 G p B Bs x L D J ks hres hB K' hK' (hrow K' hK')).2.2⟩

end CFSG.StandardType

end
