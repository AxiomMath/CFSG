module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBVacLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Subgroup

@[expose] def GGL48F4TwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGL48TB0TwRow (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1)

@[expose] def GGL48TB0Rank (lab : LargeEvenLabel) : ℕ :=
  if lab.tag = .twE6 then 6 else lab.rank

@[expose] def GGCoverPTableBRk (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r : ℕ) :
    Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    p ^ r ≤ Nat.card E →
    ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) →
      ∃ ρ : R, ∀ e : E, Commute ((MulAut.conj ρ)⁻¹ * a) (ggLAut L' θ ⟨e, hE e.2⟩)

@[expose] def GGTorusGenTableBRk (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r : ℕ) :
    Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E E₁ D' J' : Subgroup M) (d : M)
    (θ : L' ⧸ Subgroup.center L' ≃* R) (hE : E ≤ Subgroup.normalizer (L' : Set M)),
    GGTableBPosition p L' E I θ hE → p ^ r ≤ Nat.card E →
    E ⊓ Subgroup.centralizer (L' : Set M) ≠ ⊥ → E₁ ≤ E →
    E₁ ⊓ Subgroup.centralizer (L' : Set M) = ⊥ → Nat.card E = p * Nat.card E₁ →
    Subgroup.normalizer (E : Set M) ≤ Subgroup.normalizer (E₁ : Set M) →
    D' ≤ E → E ⊓ Subgroup.centralizer (L' : Set M) ≤ D' → D' ⊓ E₁ = zpowers d → d ≠ 1 →
    IsComponentOf J' (L' ⊓ Subgroup.centralizer (D' : Set M)) →
    (∀ z ∈ L' ⊓ Subgroup.centralizer (L' : Set M), z ^ p = 1 →
        z ∈ Subgroup.centralizer (E : Set M)) ∧
      ∀ c ∈ L' ⊓ Subgroup.centralizer (E₁ : Set M), (∃ k : ℕ, c ^ p ^ k = 1) →
        (c ∈ Subgroup.centralizer (L' : Set M) ∨
          ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M)) →
        ∃ (S : Subgroup M) (W : Set M), IsPGroup p S ∧
          S ≤ Subgroup.centralizer (E₁ : Set M) ∧ S ≤ J' ∧
          W ⊆ Subgroup.normalizer (E₁ : Set M) ∧
          c ∈ Subgroup.closure (⋃ n ∈ W, (fun s => n * s * n⁻¹) '' (S : Set M))

@[expose] def GGIrredModTableBRk (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r : ℕ) :
    Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    p ^ r ≤ Nat.card E →
    ∀ S : Subgroup M, E ⊓ Subgroup.centralizer (L' : Set M) ≤ S → S ≤ E →
      (∀ n ∈ L' ⊓ Subgroup.normalizer (E : Set M), ∀ s ∈ S, n * s * n⁻¹ ∈ S) →
      S = E ⊓ Subgroup.centralizer (L' : Set M) ∨ S = E

@[expose] def GGWPlusTableBRk (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (r : ℕ) :
    Prop :=
  ∀ (M : Type) [Group M] [Finite M] (L' E : Subgroup M) (θ : L' ⧸ Subgroup.center L' ≃* R)
    (hE : E ≤ Subgroup.normalizer (L' : Set M)), GGTableBPosition p L' E I θ hE →
    p ^ r ≤ Nat.card E →
    ¬ p ∣ Nat.card (L' ⊓ Subgroup.centralizer (L' : Set M) : Subgroup M) →
    ∀ (A M₁ E₁ : Subgroup (MulAut R)) (h : MulAut R),
      (MulAut.conj : R →* MulAut R).range ⊓
          Subgroup.normalizer (ggLAutImage L' θ E : Set (MulAut R)) ≤ A →
      A ≤ Subgroup.normalizer (ggLAutImage L' θ E : Set (MulAut R)) →
      (∀ a ∈ A, (∃ k : ℕ, a ^ p ^ k = 1) → a ∈ (MulAut.conj : R →* MulAut R).range ⊔
        Subgroup.centralizer (ggLAutImage L' θ E : Set (MulAut R))) →
      M₁ ≤ E₁ → E₁ ≤ A →
      A ⊓ Subgroup.centralizer (ggLAutImage L' θ E : Set (MulAut R)) ≤ M₁ →
      A ≤ Subgroup.normalizer (M₁ : Set (MulAut R)) →
      A ≤ Subgroup.normalizer (E₁ : Set (MulAut R)) →
      (∀ e ∈ E₁, ∃ k : ℕ, e ^ p ^ k ∈ M₁) → h ∈ A → (orderOf h).Coprime p →
      A ≤ E₁ ⊔ Subgroup.zpowers h → E₁ ≤ M₁

theorem ggCoverPTableBRk_of_coverPTableB {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (r : ℕ) (h : GGCoverPTableB p R I) : GGCoverPTableBRk p R I r :=
  fun M _ _ L' E θ hE hpos _ => h M L' E θ hE hpos

theorem ggTorusGenTableBRk_of_torusGenTableB {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (r : ℕ) (h : GGTorusGenTableB p R I) : GGTorusGenTableBRk p R I r :=
  fun M _ _ L' E E₁ D' J' d θ hE hpos _ => h M L' E E₁ D' J' d θ hE hpos

theorem ggIrredModTableBRk_of_irredModTableB {p : ℕ} {R : Type} [Group R]
    {I : Set (MulAut R)} (r : ℕ) (h : GGIrredModTableB p R I) : GGIrredModTableBRk p R I r :=
  fun M _ _ L' E θ hE hpos _ => h M L' E θ hE hpos

@[expose] def GGL48TableBKnownFormsRestRk : Prop :=
  (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGD4Three p lab →
        ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableBRk p R I (GGL48TB0Rank lab)) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGD4Three p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusGenTableBRk p R I (GGL48TB0Rank lab)) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → ¬ GGD4Three p lab →
        ¬ GGL48F4TwoThreeLabel p lab → ¬ GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48F4TwoThreeLabel p lab →
        LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableBRk p R I 5) ∧
    (∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → ¬ GGL48TableBVacLabel p lab → GGL48TB0TwRow p lab →
        LargeEvenLabelAll lab fun R _ I _ =>
          GGIrredModTableBRk p R I (GGL48TB0Rank lab) ∨ GGWPlusTableBRk p R I (GGL48TB0Rank lab))

@[expose] def GGL48F4TwoThreeConfigInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp 3 B x L → GGBstar 3 B Bs → Nat.card Bs = 3 ^ 4 →
    LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .F4 ∧ lab.n = 1) → False

@[expose] def GGL48TB0TwConfigInputInn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → ∀ r : ℕ, 4 < r →
      GGInnerDiagOnLab (fun p lab => GGL48TB0TwRow p lab ∧ GGL48TB0Rank lab = r) p Bs L →
      p ^ r ≤ Nat.card Bs

@[expose] def GGL48TB0TwConfigInputRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → ∀ r : ℕ, 5 < r →
      GGInnerDiagOnLab (fun p lab => GGL48TB0TwRow p lab ∧ GGL48TB0Rank lab = r) p Bs L →
      p ^ r ≤ Nat.card Bs

@[expose] def GGL48TB0TwConfigInputTwA : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → ∀ r : ℕ, 5 < r →
      GGInnerDiagOnLab
        (fun p lab => lab.tag = .twA ∧ p ∣ lab.rank + 1 ∧ p ∣ 2 ^ lab.n + 1 ∧ lab.rank = r)
        p Bs L →
      p ^ r ≤ Nat.card Bs

end CFSG.StandardType

end
