module

public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

abbrev KIsL3 {G : Type} [Group G] (M : Subgroup G) (c : G) : Prop :=
  ∃ n : ℕ, Odd n ∧
    Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n))

abbrev KType20 {G : Type} [Group G] (M N : Subgroup G) (c : G) : Prop :=
  (∃ n : ℕ, Odd n ∧
      Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 3 (GaloisField 2 n)) ∧
      Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) ∨
    (∃ n : ℕ, Even n ∧ 0 < n ∧
      Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 2 (GaloisField 2 n)) ∧
      ¬ 4 ∣ (M ⊓ N).relIndex M)

theorem KType20.isMaxParabolic {G : Type} [Group G] {M N : Subgroup G} {c : G}
    (hK : KType20 M N c) (h3 : KIsL3 M c) :
    Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
      (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c)))) := by
  rcases hK with ⟨-, -, -, hpar⟩ | ⟨m, -, hm, ⟨e⟩, -⟩
  · exact hpar
  · obtain ⟨n, hn, ⟨e'⟩⟩ := h3
    exact absurd ⟨e.symm.trans e'⟩ (not_nonempty_projSL_two_equiv_three hm hn.pos)

structure Alt20 (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) : Prop where
  eq_normalizer : N = Subgroup.normalizer (L : Set G)
  le_normalizer : A ≤ Subgroup.normalizer (L : Set G)
  quotient_iso : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2))
  not_le : ¬ L ≤ M
  pCoreOf_le : CFSG.Open.pCoreOf 2 L ≤ M
  sylow_inf : CFSG.ABGLocalTools.IsSylowOf 3 (A ⊓ L) L
  card_inf : Nat.card (A ⊓ L : Subgroup G) = 9
  orderOf_c : orderOf c = 3
  sup_inf_eq : L ⊔ (N ⊓ M) = N
  relIndex_inf : (L ⊓ M).relIndex L = 280
  card_eq : Nat.card N = 280 * Nat.card (N ⊓ M : Subgroup G)
  K_mem : kTwenty M c ∈ oTwoComponentsIn M
  K_not_le : ¬ kTwenty M c ≤ N
  K_type : KType20 M N c
  pCoreOf_K_le : CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N
  normal_inf_sup : M ≤ Subgroup.normalizer
    (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G)
  centralizer_le : KIsL3 M c → ∀ q ∈ M,
    (∀ k ∈ kTwenty M c, q * k * q⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 (kTwenty M c)) → q ∈ N
  sylow_top : ∀ P : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) →
      CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ ∧
      Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c} ∧
      c ∉ (frattini (Sec18.omegaOneThree P)).map (Sec18.omegaOneThree P).subtype

end CFSG.RankThree.PartTwo.Sec20
