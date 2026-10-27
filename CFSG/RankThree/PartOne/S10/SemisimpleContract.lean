module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven

@[expose] def coordSubgroup {I : Type} [DecidableEq I] (S : I → Type) [∀ i, Group (S i)]
    (i : I) : Subgroup (∀ i, S i) :=
  (MonoidHom.mulSingle S i).range

@[expose] def conjOrbit {H : Type} [Group H] (x : H) (L : Subgroup H) : Set (Subgroup H) :=
  Set.range fun i : ℤ => L.map (MulAut.conj (x ^ i)).toMonoidHom

@[expose] def conjOrbitJoin {H : Type} [Group H] (x : H) (L : Subgroup H) : Subgroup H :=
  ⨆ i : ℤ, L.map (MulAut.conj (x ^ i)).toMonoidHom

@[expose] def TransitiveSemisimpleOddKernelCentralization : Prop :=
  ∀ (m : ℕ) (K : Type) [Group K] [Finite K], Group.IsPerfect K → evenRank K ≤ m →
    ∀ (A : Type) [Group A] [MulDistribMulAction A K] (C : Subgroup K) [C.Normal],
      (∀ (a : A) (c : K), c ∈ C → a • c ∈ C) → Group.IsNilpotent C → Odd (Nat.card C) →
      ∀ (I : Type) [Fintype I] [DecidableEq I], m + 2 ≤ Fintype.card I →
      ∀ (S : I → Type) [∀ i, Group (S i)] [∀ i, Finite (S i)] [∀ i, IsSimpleGroup (S i)],
        (∀ i, ∃ a b : S i, a * b ≠ b * a) → (∀ i, Even (Nat.card (S i))) →
        ∀ φ : K ⧸ C ≃* (∀ i, S i),
          (∀ i j : I, ∃ a : A, ∀ k : K,
            φ (k : K ⧸ C) ∈ coordSubgroup S i ↔ φ ((a • k : K) : K ⧸ C) ∈ coordSubgroup S j) →
          C ≤ Subgroup.center K

@[expose] def CyclicSemisimpleSectionOrbitBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), evenRank G ≤ m →
    ∀ (H : Subgroup G) (Γ : Type) [Group Γ] [Finite Γ] (π : H →* Γ), Function.Surjective π →
    ∀ (r : ℕ), r.Prime → ∀ z : Γ, (∃ k : ℕ, orderOf z = r ^ k) →
    ∀ (S : Subgroup Γ) [S.Normal], S ⊔ Subgroup.zpowers z = ⊤ →
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (T : I → Type) [∀ i, Group (T i)] [∀ i, Finite (T i)] [∀ i, IsSimpleGroup (T i)],
      (∀ i, ∃ a b : T i, a * b ≠ b * a) → (∀ i, Even (Nat.card (T i))) →
      ∀ φ : S ≃* (∀ i, T i),
        (∀ i j : I, ∃ n : ℕ, ∀ s : S,
          φ s ∈ coordSubgroup T i ↔ φ (MulAut.conjNormal (z ^ n) s) ∈ coordSubgroup T j) →
        Fintype.card I ≤ m + 1

@[expose] def CoprimeTransitiveSemisimpleSectionOrbitBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), evenRank G ≤ m →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ x : G, (∃ k : ℕ, orderOf x = p ^ k) →
    ∀ (H : Subgroup G) (hx : x ∈ Subgroup.normalizer (H : Set G)), ¬ p ∣ Nat.card H →
    ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (T : I → Type) [∀ i, Group (T i)] [∀ i, Finite (T i)] [∀ i, IsSimpleGroup (T i)],
      (∀ i, ∃ a b : T i, a * b ≠ b * a) → (∀ i, Even (Nat.card (T i))) →
      ∀ π : H →* (∀ i, T i), Function.Surjective π →
        (∀ h : H, π h = 1 → π (H.normalizerMonoidHom ⟨x, hx⟩ h) = 1) →
        (∀ i j : I, ∃ n : ℕ, ∀ h : H,
          π h ∈ coordSubgroup T i ↔
            π ((H.normalizerMonoidHom ⟨x, hx⟩ ^ n) h) ∈ coordSubgroup T j) →
        Fintype.card I ≤ m + 1

@[expose] def QuotientComponentOrbitBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m : ℕ), evenRank G ≤ m →
    ∀ (N : Subgroup G) [N.Normal] (r : ℕ), r.Prime → ∀ x : G ⧸ N, (∃ k : ℕ, orderOf x = r ^ k) →
    ∀ L : Subgroup (G ⧸ N), IsComponent L → L.map (MulAut.conj x).toMonoidHom ≠ L →
    ∀ d : ℕ, d = (conjOrbit x L).ncard → r ≤ d ∧ d ≤ m + 1

@[expose] def PerfectSubgroupsNormalizeQuotientComponentsAtRankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 →
    ∀ (N : Subgroup G) [N.Normal] (P : Subgroup (G ⧸ N)), Group.IsPerfect P →
    ∀ L : Subgroup (G ⧸ N), IsComponent L → P ≤ Subgroup.normalizer (L : Set (G ⧸ N))

@[expose] def SelectedPrimeElementsFixCoprimeQuotientComponents : Prop :=
  ∀ (G : Type) [Group G] [Finite G], evenRank G ≤ 3 → ∀ p : ℕ, p.Prime → 3 < p →
    ∀ (N : Subgroup G) [N.Normal], ¬ p ∣ Nat.card N → ∀ x : G, (∃ k : ℕ, orderOf x = p ^ k) →
    ∀ L : Subgroup (G ⧸ N), IsComponent L → ¬ p ∣ Nat.card (L ⧸ Subgroup.center L) →
      (x : G ⧸ N) ∈ Subgroup.normalizer (L : Set (G ⧸ N))

end CFSG.RankThree.PartOne
