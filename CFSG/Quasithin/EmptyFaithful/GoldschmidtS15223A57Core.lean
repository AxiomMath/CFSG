module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57J
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223A57Q
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Ord3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P2Idx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S15223

variable {G : Type} [Group G] [Finite G]

structure Core57 (I S K H Mc : Subgroup G) : Prop where
  charTwo : CharTwo I
  rank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2
  sylow : IsSylowTwoOf S I
  K_le : K ≤ I
  K_odd : oTwoUpper K = K
  S_normK : S ≤ Subgroup.normalizer (K : Set G)
  K_Mc : K ≤ Mc
  S_Mc : S ≤ Mc
  unique : IsUniqueM H Mc
  H_norm : H ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G)
  three : ∃ P : Subgroup G, P ≤ K ∧ IsElemAbelian 3 P ∧ Nat.card P = 9
  K_solv : Group.IsSolvable ↥K
  P1 : ∀ Y : Subgroup G, GenByOrderThree Y → Y ≤ I →
    I ≤ Subgroup.normalizer (Y : Set G) → Y ≤ Mc → ¬ Y ≤ K → quasithinV2 Y = ⊥

omit [Finite G] in
theorem blockU_ne_bot_of_isShort2 {X : Subgroup G} (hX : IsShort2 X) : blockU X ≠ ⊥ := by
  intro h
  have := hX.2.2.2.2.1
  rw [h] at this
  exact (not_lt_of_ge bot_le) this

namespace Core57

variable {I S K H Mc : Subgroup G} (c : Core57 I S K H Mc)
include c

theorem blkCfg {X : Subgroup G} (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X) :
    BlkCfg I S K X Mc := by
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := by
    have := oTwoUpper_le_normalizer_of_block distinctBlocksCommuteStatement c.charTwo c.rank hX h3
      c.K_le
    rwa [c.K_odd] at this
  have hsyl := isSylowIn_inf_of_block distinctBlocksCommuteStatement c.charTwo c.rank c.sylow hX h3
  exact ⟨c.sylow, c.K_le, c.S_normK, hKN, c.K_Mc, c.S_Mc,
    normal_normalizer_inf distinctBlocksCommuteStatement c.charTwo c.rank hX h3,
    ⟨hsyl.1, hsyl.2.1, hsyl.2.2⟩⟩

theorem exists_isMaxElemAbelian {X : Subgroup G} (hX : IsBlock2 I X) (h3 : 3 ∣ Nat.card X)
    (hXMc : ¬ X ≤ Mc)
    (hswap : ∀ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (K ⊔ S)) A →
      A ≤ Subgroup.normalizer (X : Set G)) :
    ∃ A : Subgroup G, IsMaxElemAbelian (pCoreOf 2 (K ⊔ (S ⊓ Subgroup.normalizer (X : Set G)))) A ∧
      ¬ A ≤ Subgroup.centralizer (blockU X : Set G) := by
  have cfg := c.blkCfg hX h3
  set S₁ : Subgroup G := S ⊓ Subgroup.normalizer (X : Set G) with hS₁
  set Q₁ : Subgroup G := pCoreOf 2 (K ⊔ S₁) with hQ₁
  set Q : Subgroup G := pCoreOf 2 (K ⊔ S) with hQ
  have hUO : blockU X ≤ pCoreOf 2 X := fun u hu => (hX.1.2.2.1.1 hu).1
  have hUQ : blockU X ≤ Q₁ := hUO.trans cfg.pCoreOf_le_pCoreOf_sup_inf
  have hQ₁Q : Q₁ ≤ Q := cfg.pCoreOf_sup_inf_le
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 _
  have hQ0 : Q ≠ ⊥ := fun h =>
    blockU_ne_bot_of_isShort2 hX.1 (le_bot_iff.mp ((hUQ.trans hQ₁Q).trans h.le))
  have hO : pCoreOf 2 (X ⊔ Q₁) ≤ Q := cfg.pCoreOf_sup_le_pCoreOf_sup_inf.trans hQ₁Q
  obtain ⟨A, hAQ, hA⟩ :=
    exists_isMaxElemAbelian_not_le_pCoreOf c.unique hQ2 hQ0 c.H_norm hO hXMc
  have hAQ₁ : A ≤ Q₁ :=
    (le_inf hAQ.1 (hswap A hAQ)).trans cfg.inf_normalizer_le_pCoreOf_sup_inf
  refine ⟨A, ⟨hAQ₁, hAQ.2.1, fun B hB hBe => hAQ.2.2 B (hB.trans hQ₁Q) hBe⟩, ?_⟩
  have hS₁2 : IsPGroup 2 S₁ := c.sylow.2.1.to_le inf_le_left
  have hP₀ := isSylowTwoOf_sup_inf hS₁2 inf_le_right cfg.pCoreOf_sup_le_S₁ cfg.sylowX₁
  exact not_le_centralizer_blockU_of_not_le_pCoreOf hX.1
    (cfg.pCoreOf_sup_le_S₁.trans inf_le_right) hP₀ le_sup_right (hAQ₁.trans le_sup_right) hA

end Core57

end S15223

end CFSG.Quasithin
