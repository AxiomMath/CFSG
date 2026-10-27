module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def NormH0 (M Z Z0 : Subgroup G) : Subgroup G :=
  H0 M Z ⊓ Subgroup.normalizer (Z0 : Set G)

@[expose] def NormH0L (M Z L : Subgroup G) : Subgroup G :=
  H0 M Z ⊓ Subgroup.normalizer (L : Set G)

@[expose] def IsMaxAbNormalMod (K Z0 Q : Subgroup G) : Prop :=
  Z0 ≤ K ∧ (∀ x ∈ Z0, ∀ y ∈ Z0, ⁅x, y⁆ ∈ Q) ∧ (∀ k ∈ K, conjSubgroup k Z0 = Z0) ∧
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ K → (∀ k ∈ K, conjSubgroup k A = A) →
      (∀ x ∈ A, ∀ y ∈ A, ⁅x, y⁆ ∈ Q) → A = Z0

@[expose] def SubConfigHyp79 (M Q Z N : Subgroup G) : Prop :=
  ∃ hN : (Q.subgroupOf (H0 M Z)).Normal,
    haveI := hN
    pCore 2 (↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z)) = ⊥ ∧
    Tim79.Hyp79 (G := ↥(H0 M Z) ⧸ Q.subgroupOf (H0 M Z))
      (Subgroup.normalizer ((cen (bar (H0 M Z) Q N) : Subgroup _) : Set _))
      (cen (bar (H0 M Z) Q N)) (bar (H0 M Z) Q N)

theorem SubConfigHyp79.subConfig [Finite G] {M Q Z N : Subgroup G}
    (h : SubConfigHyp79 M Q Z N) : SubConfig M Q Z N := by
  obtain ⟨hN, ho, H⟩ := h
  exact ⟨hN, stroth_hyp_of_hyp79 ho H⟩

end CFSG.RankThree.GF2n.Stroth80
