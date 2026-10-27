module

public import CFSG.RankThree.PartTwo.Sec8.Hering418Cfg
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def KF418ModelOn (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
    P (L ⧸ aschbacherSolvableCore 3 L) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
      a ∈ Subgroup.normalizer (L : Set G) → b ∈ Subgroup.normalizer (L : Set G) →
      b ∉ Sec4.thetaQuotCentralizer L → (∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L) →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
        ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField)

namespace Hering418

open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418 (rho)

theorem mem_thetaQuotCentralizer_iff {G : Type} [Group G] [Finite G] {L : Subgroup G} {g : G} :
    g ∈ Sec4.thetaQuotCentralizer L ↔
      ∃ hg : g ∈ Subgroup.normalizer (L : Set G), rho L ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem Cfg.of_model {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b})) (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hab : a * b = b * a) (haN : a ∈ Subgroup.normalizer (L : Set G))
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hbC : b ∉ Sec4.thetaQuotCentralizer L)
    (haC : ∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L)
    (hKa : KFacts.InducesStdKind K a .field) : Cfg L K a b := by
  have hKM := le_of_mem_thetaComponentsIn hK
  obtain ⟨haK, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta (k := .field) K hKa (by decide)
  refine ⟨hKM.trans inf_le_left, hKM.trans inf_le_right, ha3, hb3, hab, haN, hbN, haK, ?_, ?_, hout⟩
  · intro h
    exact hbC (mem_thetaQuotCentralizer_iff.mpr ⟨hbN, h⟩)
  · intro j h
    apply haC j
    refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.mul_mem _ haN (Subgroup.zpow_mem _ hbN j), ?_⟩
    have e : (⟨a * b ^ j, Subgroup.mul_mem _ haN (Subgroup.zpow_mem _ hbN j)⟩ :
        Subgroup.normalizer (L : Set G)) =
        ⟨a, haN⟩ * (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) ^ j :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_zpow])
    rw [e, map_mul, map_zpow]
    exact h

end Hering418

end CFSG.RankThree.PartTwo.Sec8
