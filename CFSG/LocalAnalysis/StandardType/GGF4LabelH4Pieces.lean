module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelPieces

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGF4NbrList
    {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
    (GGHasLabel ⟨.C, 3, f⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (K ⧸ Subgroup.center K))) ∨
  (p = 3 ∧ (GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K) ∨
    GGHasLabel ⟨.A, 6, 1⟩ (K ⧸ Subgroup.center K))) ∨
  (p = 5 ∧ GGHasLabel ⟨.A, 5, 2⟩ (K ⧸ Subgroup.center K) ∧ Subgroup.center K = ⊥) ∨
  (∃ f : ℕ, 2 ≤ f ∧ p ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ (K ⧸ Subgroup.center K))

@[expose] def GGF4JBlock
    {G : Type} [Group G] (p f : ℕ) (L J : Subgroup G) : Prop :=
  (p ∣ 2 ^ f - 1 → GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L) →
    GGHasLabel ⟨.A, 2, f⟩ (J ⧸ Subgroup.center J) ∧
      Nat.card (Subgroup.center J) = Nat.gcd 3 (2 ^ f - 1)) ∧
  (p ∣ 2 ^ f + 1 → GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L) →
    GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) ∧
      Nat.card (Subgroup.center J) = Nat.gcd 3 (2 ^ f + 1))

@[expose] def GGF4H4List
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ K ∈ ks, GGF4NbrList p K

@[expose] def GGF4H4JBlock
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    ∀ f : ℕ, 2 ≤ f → GGF4JBlock p f L J

@[expose] def GGF4H4Psl64
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ f : ℕ, 2 ≤ f → p ∣ 2 ^ f - 1 → GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L) →
      GGF4JBlock p f L J → ∀ K ∈ ks, p = 5 → GGHasLabel ⟨.A, 5, 2⟩ (K ⧸ Subgroup.center K) →
        Subgroup.center K = ⊥ → False

@[expose] def GGF4H4Twisted
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ f : ℕ, 2 ≤ f → p ∣ 2 ^ f + 1 → GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L) →
      GGF4JBlock p f L J → ∀ K ∈ ks, GGF4NbrList p K →
        GGF4LabelRow p (L ⧸ Subgroup.center L) (K ⧸ Subgroup.center K)

@[expose] def GGF4H4Untwisted
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ f : ℕ, 2 ≤ f → p ∣ 2 ^ f - 1 → GGHasLabel ⟨.A, 3, f⟩ (L ⧸ Subgroup.center L) →
      GGF4JBlock p f L J → ∀ K ∈ ks, GGF4NbrList p K →
        GGF4LabelRow p (L ⧸ Subgroup.center L) (K ⧸ Subgroup.center K)

theorem ggF4LabelH4_of_pieces
    (hlist : GGF4H4List) (hJ : GGF4H4JBlock) (htw : GGF4H4Twisted) (hun : GGF4H4Untwisted) :
    GGF4LabelH4 := by
  intro G _ _ p B Bs x L D J ks hres hL hB K hK
  obtain ⟨f, hf, h | h⟩ := hL
  · exact hun G p B Bs x L D J ks hres hB f hf h.1 h.2 (hJ G p B Bs x L D J ks hres f hf) K hK
      (hlist G p B Bs x L D J ks hres hB K hK)
  · exact htw G p B Bs x L D J ks hres hB f hf h.1 h.2 (hJ G p B Bs x L D J ks hres f hf) K hK
      (hlist G p B Bs x L D J ks hres hB K hK)

end CFSG.StandardType

end
