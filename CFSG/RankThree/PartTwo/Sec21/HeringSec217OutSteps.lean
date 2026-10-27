module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217Out

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

structure OutSecond {G : Type} [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G)
    (a : G) (U₀ K : Subgroup G) : Prop where
  base : CoverOut A E U c L
  frame : Frame217 E c L a
  mem_U₀ : U₀ ∈ fourGroupsMinus E
  U₀_le : U₀ ≤ iCore L a
  mem_K : K ∈ lThreeStarAt A a
  pair : (a, K) ∈ lThreeStarPairs A E U₀
  type : Nonempty (lBar K ≃* NativeSporadic.J3) ∨ Sec4.IsTripleCover (lBar K) NativeSporadic.J3
  ext : Sec4.IsExtOf ↥(starOf A K) (Multiplicative (ZMod 8)) (Multiplicative (ZMod 3 × ZMod 3))
  I_le_K : iCore L a ≤ K
  quasi : CFSG.IsQuasisimple ↥K

structure UV217Out {G : Type} [Group G] (A : Subgroup G) (c : G) (L K : Subgroup G) (a u v : G) :
    Prop where
  mem_u : u ∈ L ⊓ Subgroup.normalizer (A : Set G)
  mem_v : v ∈ K ⊓ Subgroup.normalizer (A : Set G)
  pow_u : u ^ 8 ∈ Subgroup.centralizer (dGroup a c : Set G)
  pow_v : v ^ 8 ∈ Subgroup.centralizer (dGroup a c : Set G)
  norm_u : u ∈ Subgroup.normalizer (dGroup a c : Set G)
  norm_v : v ∈ Subgroup.normalizer (dGroup a c : Set G)
  nontriv_u : u ∉ Subgroup.centralizer (dGroup a c : Set G)
  nontriv_v : v ∉ Subgroup.centralizer (dGroup a c : Set G)
  t_cent : u * v⁻¹ ∈ Subgroup.centralizer (iCore L a : Set G)

@[expose] def Sec217OutSecond : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    CoverOut A E U c L → ∃ (a : G) (U₀ K : Subgroup G), OutSecond A E U c L a U₀ K

@[expose] def Sec217OutElements : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (U₀ K : Subgroup G), OutSecond A E U c L a U₀ K → ∃ u v : G, UV217Out A c L K a u v

@[expose] def Sec217OutTransvection : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (U₀ K : Subgroup G), OutSecond A E U c L a U₀ K → ∀ u v : G, (h : UV217Out A c L K a u v) →
      ∃ d : G, d ≠ 1 ∧ Subgroup.zpowers d = dGroup a c ⊓ L ∧
        ⁅Subgroup.zpowers u, dGroup a c⁆ = Subgroup.zpowers d ∧
        ⁅Subgroup.zpowers u, dGroup a c⁆ ≠ Subgroup.zpowers a ∧
        u * d * u⁻¹ = d⁻¹ ∧ v * d * v⁻¹ = d⁻¹ ∧
        IsTransvectionOn (A.normalizerMonoidHom
          ⟨u * v⁻¹, mul_mem h.mem_u.2 (inv_mem h.mem_v.2)⟩) ∧
        (commOf (A.normalizerMonoidHom
          ⟨u * v⁻¹, mul_mem h.mem_u.2 (inv_mem h.mem_v.2)⟩)).map A.subtype =
            Subgroup.zpowers d ∧
        (fixedSubgroupOf (A.normalizerMonoidHom
          ⟨u * v⁻¹, mul_mem h.mem_u.2 (inv_mem h.mem_v.2)⟩)).map A.subtype = A ⊓ L

@[expose] def Sec217OutJCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    CoverOut A E U c L → Frame217 E c L a → ∀ d : G,
      Subgroup.zpowers d = dGroup a c ⊓ L →
      (∃ (t : G) (ht : t ∈ Subgroup.normalizer (A : Set G)),
        IsTransvectionOn (A.normalizerMonoidHom ⟨t, ht⟩) ∧
        (commOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = Subgroup.zpowers d ∧
        (fixedSubgroupOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = A ⊓ L) →
      ∀ J ∈ thetaComponentsAt 3 d, iCore L a ≤ J → c ∈ Sec4.thetaQuotCentralizer J

@[expose] def Sec217OutJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    CoverOut A E U c L → Frame217 E c L a → ∀ d : G,
      Subgroup.zpowers d = dGroup a c ⊓ L →
      (∃ (t : G) (ht : t ∈ Subgroup.normalizer (A : Set G)),
        IsTransvectionOn (A.normalizerMonoidHom ⟨t, ht⟩) ∧
        (commOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = Subgroup.zpowers d ∧
        (fixedSubgroupOf (A.normalizerMonoidHom ⟨t, ht⟩)).map A.subtype = A ⊓ L) →
      ∀ J ∈ thetaComponentsAt 3 d, iCore L a ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        A ⊓ Sec4.thetaQuotCentralizer J = Subgroup.zpowers d → False

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
