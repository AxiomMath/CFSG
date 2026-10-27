module

public import CFSG.Quasithin.EmptyFaithful.S1565L16
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBOrd
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Timmesfeld.Orders.Exceptional

public section

namespace CFSG.Quasithin.CLG2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native.L239 CFSG.Blueprint CFSG.Quasithin.H13.VolI
open CFSG.RankThree.PartOne.S12K

set_option linter.unusedSectionVars false

section Sz


theorem sz_quotient {H : Type} [Group H] [Finite H] {a : ℕ} {K : Type} [Field K] [Finite K]
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (ψ : H →* suzukiGroup a K)
    (hs : Function.Surjective ψ) (hk : IsPGroup 2 ψ.ker) :
    IsSz (2 * a + 1) (H ⧸ CFSG.pCore 2 H) ∧ CFSG.IsQuasisimple (H ⧸ CFSG.pCore 2 H) := by
  have hSz : IsSz (2 * a + 1) (suzukiGroup a K) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨MulEquiv.refl _⟩⟩
  have hq : CFSG.IsQuasisimple (suzukiGroup a K) :=
    isQuasisimple_of_psl2_or_sz (n := 2 * a + 1) (by omega) (Or.inr hSz)
  have hsimple : IsSimpleGroup (suzukiGroup a K) := isSimpleGroup_of_psl2_or_sz (Or.inr hSz)
  have h0 : CFSG.pCore 2 (suzukiGroup a K) = ⊥ := by
    have : Finite (suzukiGroup a K) := Finite.of_surjective ψ hs
    exact GoldMLA.pCore_two_eq_bot_of_simple hq.1.commutator_eq_top hsimple
  have hker : ψ.ker = CFSG.pCore 2 H := by
    apply le_antisymm
    · exact le_sSup ⟨ψ.normal_ker, hk⟩
    · intro x hx
      rw [MonoidHom.mem_ker]
      have himg : (CFSG.pCore 2 H).map ψ ≤ CFSG.pCore 2 (suzukiGroup a K) :=
        le_sSup ⟨(CFSG.pCore_normal (G := H) (p := 2)).map ψ hs,
          (CFSG.pCore_isPGroup (G := H) (p := 2)).map ψ⟩
      rw [h0] at himg
      exact Subgroup.mem_bot.mp (himg ⟨x, hx, rfl⟩)
  have e : (H ⧸ CFSG.pCore 2 H) ≃* suzukiGroup a K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hs)
  have hX : IsSz (2 * a + 1) (H ⧸ CFSG.pCore 2 H) :=
    ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl, hK, ⟨e⟩⟩
  exact ⟨hX, isQuasisimple_of_psl2_or_sz (n := 2 * a + 1) (by omega) (Or.inr hX)⟩

end Sz

section List


theorem ordSuzuki_big {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) :
    ordSuzuki (2 ^ f) = 29120 ∨ 9999360 < ordSuzuki (2 ^ f) := by
  by_cases h3 : f = 3
  · subst h3
    left
    decide
  · right
    have hf5 : 5 ≤ f := by
      obtain ⟨k, rfl⟩ := hf
      omega
    have hq : 32 ≤ 2 ^ f :=
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf5
    have h1 : 1024 ≤ (2 ^ f) ^ 2 := by nlinarith
    have h2 : 31 ≤ 2 ^ f - 1 := by omega
    have h3 : 1025 ≤ (2 ^ f) ^ 2 + 1 := by omega
    calc 9999360 < 1024 * 1025 * 31 := by norm_num
      _ ≤ (2 ^ f) ^ 2 * ((2 ^ f) ^ 2 + 1) * (2 ^ f - 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 h3) h2

theorem not_list15120_of_isSz {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}
    (hf : Odd f) (hf3 : 3 ≤ f) (hX : IsSz f (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ¬ (ListA15120 L ∨ ListB15120 L ∨ ListC15120 L ∨ ListD15120 L) := by
  obtain ⟨-, a, ha, hfa, hcard⟩ := CFSG.GH74.card_of_suzukiModel hX
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := isSimpleGroup_of_psl2_or_sz (Or.inr hX)
  have hbig := ordSuzuki_big hf hf3
  have hD : ∀ c : ℕ, 2 ≤ c → c ≤ 6048 →
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)).index = c → False := by
    intro c hc2 hc6 hidx
    rcases hs.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) with h | h
    · rw [h, Subgroup.index_bot, hcard] at hidx
      omega
    · rw [h, Subgroup.index_top] at hidx
      omega
  rintro (⟨n, hn, h⟩ | (⟨n, hn, h⟩ | ⟨n, hn, h⟩ | ⟨n, hn, h⟩) | (h | h) | (h | h | h | h))
  · have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = ordA 1 (2 ^ n) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    exact ordSuzuki_ne_ordA_one hf3 (by omega) (hcard.symm.trans h1)
  · exact ordSuzuki_not_rankTwoOrder hf hf3
      (hcard ▸ GoldMLB.rankTwoOrder_of_quotModel (Or.inl ⟨n, hn, h⟩))
  · exact ordSuzuki_not_rankTwoOrder hf hf3
      (hcard ▸ GoldMLB.rankTwoOrder_of_quotModel (Or.inr ⟨n, hn, h⟩))
  · have h1 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    have h2 : RankTwoOrder (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1⟩)))))
    exact ordSuzuki_not_rankTwoOrder hf hf3 (hcard ▸ h2)
  · have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = ordA 3 (2 ^ 1) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have h2 : ordA 3 (2 ^ 1) = 20160 := by decide
    omega
  · have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = ordA 4 (2 ^ 1) :=
      (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    have h2 : ordA 4 (2 ^ 1) = 9999360 := by decide
    omega
  · obtain ⟨e⟩ := h
    have h1 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 2520 := by
      rw [Nat.card_congr e.toEquiv, Bridge.card_alt_seven]
    exact hD 2520 (by norm_num) (by norm_num) h1
  · have h1 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 168 :=
      SBc11.card_of_isPSL_three_two h
    exact hD 168 (by norm_num) (by norm_num) h1
  · have h1 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 360 :=
      SBc11.card_of_isAlt_six h
    exact hD 360 (by norm_num) (by norm_num) h1
  · have h1 : Nat.card ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 6048 :=
      SBc11.card_of_isPSU_three_three h
    exact hD 6048 (by norm_num) (by norm_num) h1

end List

end CFSG.Quasithin.CLG2
