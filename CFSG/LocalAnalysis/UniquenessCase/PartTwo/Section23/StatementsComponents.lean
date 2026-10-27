module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Context
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsOmegaMinus IsOmegaPlus IsSLn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_5_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    c.n = CFSG.Open.pRank 2 D.Z ∨
      (c.L = c.L0 ∧ IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) ∧
        c.n = 2 * CFSG.Open.pRank 2 D.Z)

@[expose] def S23_5_3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, piSet c.B = etaSet c.n →
    c.B ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ ∨
      (c.n = 2 * CFSG.Open.pRank 2 D.Z ∧
        piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) =
          {p | p.Prime ∧ p ∣ 2 ^ (CFSG.Open.pRank 2 D.Z) + 1})

@[expose] def S23_5_4 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    ∀ b ∈ c.B, b ∉ Subgroup.centralizer (D.Z : Set G) →
      ¬ InvertedIn D.M (Subgroup.zpowers b) ∧
      ∀ p : ℕ, p.Prime → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p ↥X →
        X ≤ D.M ⊓ Subgroup.centralizer ({b} : Set G) →
          X ∉ uniqueSet D.M ∧ p ∉ D.sig1

@[expose] def S23_6 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, D.sig = D.sig1

@[expose] def S23_7_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 →
    ∀ Q : Subgroup G, Q ≤ D.M → IsPGroup q ↥Q → ¬ IsCyclic ↥Q →
      (∀ x ∈ Q, x ^ q = 1) → ⁅⁅Q, Q⁆, Q⁆ = ⊥ →
    ∀ p ∈ D.sig, ∀ P : Subgroup G, P ≤ D.M → (P.subgroupOf D.M).Normal →
      P ≤ CFSG.Open.relPPrimeCore p D.M →
    ∀ Q0 : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q0 P →
      Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) →
      ((Q.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal) →
    ∀ g : G, g ∉ D.M → Q ⊓ D.M.map (MulAut.conj g).toMonoidHom = ⊥

@[expose] def S23_7_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ q : ℕ, q.Prime → q ≠ 2 →
    ∀ Q : Subgroup G, Q ≤ D.M → IsPGroup q ↥Q → ¬ IsCyclic ↥Q →
      (∀ x ∈ Q, x ^ q = 1) → ⁅⁅Q, Q⁆, Q⁆ = ⊥ →
    ∀ p ∈ D.sig, ∀ P : Subgroup G, P ≤ D.M → (P.subgroupOf D.M).Normal →
      P ≤ CFSG.Open.relPPrimeCore p D.M →
    ∀ Q0 : Subgroup G, CFSG.ABGLocalTools.IsSylowOf q Q0 P →
      Q ≤ D.M ⊓ Subgroup.normalizer (Q0 : Set G) →
      ((Q.subgroupOf (D.M ⊓ Subgroup.normalizer (Q0 : Set G))).Normal) →
    ∀ N ∈ calMOf D.T, N ≠ D.M → Permutes D.T Q → Q ⊓ N = ⊥

@[expose] def S23_7 (D : Data G) (Ch : Choice2011 G) : Prop :=
  S23_7_1 D Ch ∧ S23_7_2 D Ch

@[expose] def S23_7_2_sig (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ q ∈ D.sig,
    ∀ Q : Subgroup G, Q ≤ D.M → IsPGroup q ↥Q →
      (∀ x ∈ Q, x ^ q = 1) → ⁅⁅Q, Q⁆, Q⁆ = ⊥ →
    ∀ N ∈ calMOf D.T, N ≠ D.M → Permutes D.T Q → Q ⊓ N = ⊥

@[expose] def S23_8 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ K : Subgroup G, K ∈ calC D.M →
    (K.subgroupOf D.M).Normal ∧
    ((∃ a : ℕ, Odd a ∧ (IsL2 (Bar2 K) a ∨ IsSz (Bar2 K) a)) ∨
      (((∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (Bar2 K) q) ∨ IsJ1 (Bar2 K) ∨
          (∃ a : ℕ, IsL2 (Bar2 K) (2 * a))) ∧
        barImage D.M K = Opp 3 (CFSG.layer (Bar2 D.M))))

@[expose] def S23_9_1 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    Hinf (D.M ⊓ c.L) = ⊥ ∨ Hinf (D.M ⊓ c.L) ∈ calC D.M

@[expose] def S23_9_2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    let n := CFSG.Open.pRank 2 D.Z
    IsL2 (Bar2 c.L) n ∨ IsOmegaPlus (Bar2 c.L) 4 n ∨ IsOmegaMinus (Bar2 c.L) 4 n ∨
      IsSLn (Bar2 c.L) 3 n

@[expose] def S23_10 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch,
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) → ⁅c.B, D.Z⁆ ≠ ⊥ →
      ∃ p ∈ D.sig, ∃ P : Subgroup (Bar2 D.M),
        CFSG.ABGLocalTools.IsSylowOf p P (CFSG.fittingSubgroup (Bar2 D.M)) ∧
        ¬ barImage D.M c.B ≤ Subgroup.centralizer (P : Set (Bar2 D.M))

end CFSG.LocalAnalysis.UniquenessCase.UC22
