module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
public import CFSG.LocalAnalysis.StandardType.GGQ2S08TwoNodeBasics
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2TNBigSel {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (Bs X : Subgroup G) (u : G) : Prop :=
  ∃ M : GGQ2LDatum p Bs X u, ∃ r : ℕ, 11 ≤ r ∧ 3 ∣ r + 1 ∧ ∃ e : Fin r ≃ M.Λ,
    (∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) ∧ M.ShapeB

@[expose] def GGQ2TN9Sel {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) : Prop :=
  (∃ M : GGQ2LDatum p Bs L x, ∃ e : Fin 8 ≃ M.Λ,
      (∀ i j, M.cartan (e i) (e j) = CartanMatrix.A 8 i j) ∧ M.ShapeB) ∧
    4 ∣ Nat.card (ggAutomizer J Bs) ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ∃ N : GGQ2NbrDatum p Bs K, ((N.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
        ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ N.Λ),
          (∀ i j, N.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀

@[expose] def GGQ2TN9SelK {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G) : Prop :=
  (∃ MK : GGQ2LDatum p Bs K y, ∃ e : Fin 8 ≃ MK.Λ,
      (∀ i j, MK.cartan (e i) (e j) = CartanMatrix.A 8 i j) ∧ MK.ShapeB) ∧
    (∃ NK : GGQ2NbrDatum p Bs K, ∃ e : Fin 8 ≃ NK.Λ,
      (∀ i j, NK.cartan (e i) (e j) = CartanMatrix.A 8 i j) ∧ Module.finrank (ZMod p) NK.V = 8 ∧
        Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range NK.coroot)) + 1 = 8) ∧
    (∃ ML : GGQ2LDatum p Bs L x, 3 ≤ Fintype.card ML.Λ ∧ ((ML.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
      ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ ML.Λ),
        (∀ i j, ML.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀) ∧
    4 ∣ Nat.card (ggAutomizer J Bs) ∧
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      Subgroup.zpowers y' ≠ Subgroup.zpowers y →
      ∃ N : GGQ2NbrDatum p Bs K', ((N.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
        ∃ (n : ℕ) (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ N.Λ),
          (∀ i j, N.cartan (e i) (e j) = C₀ i j) ∧ GGQ2WeylInner n C₀

@[expose] def GGQ2TwoNodeRestInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K)) →
      ¬ ((GGQ2S08PosTwABig p L J ∧ x ∉ L) ∨ (GGQ2S08PosTwABig p K J ∧ y ∉ K) ∨
        (GGQ2S08PosABig p K J ∧ y ∉ K)) →
      ¬ GGQ2TNBigSel p Bs L x → ¬ GGQ2TNBigSel p Bs K y → ¬ GGQ2TN9Sel p B Bs x L D J →
        ¬ GGQ2TN9SelK p B Bs x L D J y K →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGQ2S08TN9RestCell : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime], p = 3 →
    ∀ {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}, GGQTwoSetting p B Bs x L D J →
      GGQTwoI1 Bs D J → ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ((GGQ2S08PosTwA 9 p L J ∧ x ∉ L) ∨ (GGQ2S08PosTwA 9 p K J ∧ y ∉ K)) →
      ¬ GGQ2TN9Sel p B Bs x L D J → ¬ GGQ2TN9SelK p B Bs x L D J y K →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

end CFSG.StandardType

end
