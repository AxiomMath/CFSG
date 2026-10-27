module

public import CFSG.OddTranspositions.TheoremTwo.Assembly
public import CFSG.OddTranspositions.TheoremTwo.LemmaFourEight
public import CFSG.OddTranspositions.TheoremTwo.AalphaNonempty
import CFSG.OddTranspositions.SevenLocalSecond

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ CFSG.GroupTheory

@[expose] def ThirdKBenderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Setup G D →
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → LocalSecond D →
    ∀ (u w v : G) (n : ℕ), IsTriangle D u w v → Odd n → 1 < n →
      orderOf (u * v * w) = 2 * n →
      CFSG.BenderSuzuki.IsBenderGroup
        (thirdK D ((u * v * w) ^ n) ⧸ CFSG.solvableRadical (thirdK D ((u * v * w) ^ n)))

@[expose] def DiffBlockStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → LocalSecond D →
    (∃ u w v : G, IsTriangle D u w v ∧ IsThirdKind u w v) →
    ∃ w v : G, IsTriangle D hC.d w v ∧ IsThirdKind hC.d w v ∧ v ∈ DalphaStar D hC.alpha

@[expose] def QCentralStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → LocalSecond D →
    ∀ (w v : G) (n : ℕ), IsTriangle D hC.d w v → Odd n → 1 < n →
      orderOf (hC.d * v * w) = 2 * n → v ∈ DalphaStar D hC.alpha →
      CFSG.BenderSuzuki.IsBenderGroup
        (thirdK D ((hC.d * v * w) ^ n) ⧸ CFSG.solvableRadical (thirdK D ((hC.d * v * w) ^ n))) →
      CFSG.pCore 2 (thirdK D ((hC.d * v * w) ^ n)) ≤
        Subgroup.center (thirdK D ((hC.d * v * w) ^ n))

@[expose] def ConfigStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D),
    (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) → LocalSecond D →
    ∀ (w v : G) (n : ℕ), IsTriangle D hC.d w v → Odd n → 1 < n →
      orderOf (hC.d * v * w) = 2 * n → v ∈ DalphaStar D hC.alpha →
      CFSG.BenderSuzuki.IsBenderGroup
        (thirdK D ((hC.d * v * w) ^ n) ⧸ CFSG.solvableRadical (thirdK D ((hC.d * v * w) ^ n))) →
      CFSG.pCore 2 (thirdK D ((hC.d * v * w) ^ n)) ≤
        Subgroup.center (thirdK D ((hC.d * v * w) ^ n)) →
      ∃ (a : G) (K₁ S' : Subgroup G), Config D hC.d w v ((hC.d * v * w) ^ n) a K₁ S'

@[expose] def FibreSingletonStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (u w v z a : G)
    (K₁ S' : Subgroup G), Config D u w v z a K₁ S' →
    ∀ (ε : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
        Equiv.Perm (Fin 5)),
      ε '' imageClass hC = transpositions →
      ∀ (d : G) (hd : d ∈ DalphaStar D hC.alpha)
        (d' : G) (hd' : d' ∈ DalphaStar D hC.alpha),
        ε (starImage hC d hd) = ε (starImage hC d' hd') → d = d'

@[expose] def TheoremFourNineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G) (u w v z a : G) (K₁ S' : Subgroup G),
    Config D u w v z a K₁ S' →
    S' ⊓ Subgroup.centralizer (thirdK D z : Set G) = Subgroup.zpowers z →
    O4PairData G D

theorem thirdKindExclusionStep_of_pieces
    (h33 : ThirdKBenderStatement) (h41 : DiffBlockStatement) (h42 : QCentralStatement)
    (hcfg : ConfigStatement) (h47 : FibreSingletonStatement)
    (h49 : TheoremFourNineStatement) : ThirdKindExclusionStep := by
  intro G _ _ D hC hrad hL hmin
  by_cases hsec : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4
  · exact Or.inl hsec
  right
  push Not at hsec
  obtain ⟨u, w, v, htri, hne4⟩ := hsec
  have hfirst := no_firstKind_of_H' hC fun x y t hx hy ht htri' h1 => by
    have h4 := DalphaStar_triangles_of_localSecond hC hL x hx y hy t ht htri'
    rw [h4] at h1
    exact absurd h1.1 (by decide)
  rcases htri.orderOf_cases hC.setup.oddT hC.setup.normal with h1 | h4 | h3
  · exact absurd h1 (hfirst u w v htri)
  · exact absurd h4 hne4
  obtain ⟨w', v', htri', ⟨n, hn, hn1, hord⟩, hv'⟩ := h41 G D hC hrad hL ⟨u, w, v, htri, h3⟩
  have hB := h33 G D hC.setup hrad hL hC.d w' v' n htri' hn hn1 hord
  have hQ := h42 G D hC hrad hL w' v' n htri' hn hn1 hord hv' hB
  obtain ⟨a, K₁, S', hcfg'⟩ := hcfg G D hC hrad hL w' v' n htri' hn hn1 hord hv' hB hQ
  have hcent := Config.centralizer_thirdK_eq_of_prop47 hcfg' hC hC.d_mem_alpha hv' hmin
    (h47 G D hC _ _ _ _ _ _ _ hcfg')
  exact h49 G D _ _ _ _ _ _ _ hcfg' hcent

end CFSG.OddTranspositions

end
