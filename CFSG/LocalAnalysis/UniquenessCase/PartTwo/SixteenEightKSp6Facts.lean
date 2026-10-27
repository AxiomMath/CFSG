module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
public import CFSG.GroupTheory.WeirSylow.CrossRankLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Spin
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartOne.KF.F128Cls
public import CFSG.RankThree.PartOne.KF.RankGL
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private theorem s16k_charP_two_of_card_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

private theorem s16k_center_statedSp_eq_bot_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (n : ℕ) : Subgroup.center (StatedSp n K) = ⊥ := by
  haveI : CharP K 2 := s16k_charP_two_of_card_two hK
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

private theorem s16k_center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) φ.injective).1 <| by
    rw [Subgroup.map_center_eq φ, h]

private theorem s16k_card_generic_exceptional_psp_three_one :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSp 3 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSp 3 2 1) = 2 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16k_statedClassicalModel_statedSp_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) :
    StatedClassicalModel (StatedSp 3 K) .PSp 3 2 1 := by
  haveI : CharP K 2 := s16k_charP_two_of_card_two hK
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := 3)
  have hproj : StatedProj (StatedSp 3 K) ≃* StatedSp 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  rintro h
  exact absurd (congrArg Prod.fst h) (by norm_num)

private theorem s16k_div_le_one_of_three_le {e : ℕ} (he : 3 ≤ e) :
    (if Even e then 2 * 3 else 3) / e ≤ 1 := by
  split_ifs with hev
  · rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < e)]
    rcases hev with ⟨k, hk⟩
    omega
  · exact Nat.div_le_of_le_mul (by omega)

private theorem s16k_three_le_orderOf_two_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) : 3 ≤ orderOf (2 : ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  change 3 ≤ orderOf ((2 : ℕ) : ZMod p)
  rw [← CFSG.GroupTheory.WeirSylow.ordMod_natCast p 2]
  refine CFSG.GroupTheory.WeirSylow.three_le_ordMod_of_not_dvd_sq_sub_one ?_ ?_
  · intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  · intro h
    have h' : (p : ℤ) ∣ (3 : ℤ) := by
      have := h
      norm_num at this
      exact this
    have h'' : p ∣ 3 := by exact_mod_cast h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h'')

theorem s16k_sp6_center_mult (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSpn X 6 1) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 := by
  simp only [IsSpn, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
  have hbot : Subgroup.center (StatedSp 3 K) = ⊥ := s16k_center_statedSp_eq_bot_two hK2 3
  have hclass : StatedClassicalModel X .PSp 3 2 1 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (s16k_statedClassicalModel_statedSp_three hK2)
  have hmodel : CFSG.Models.LieModel X .PSp 3 2 1 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSp 3 2 1 hmodel
  refine ⟨?_, ?_⟩
  · rw [s16k_center_eq_bot_of_mulEquiv e hbot, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16k_card_generic_exceptional_psp_three_one

theorem s16k_pRank_aut_sp6 {X : Type} [Group X] [Finite X] (h : IsSpn X 6 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ if p = 3 then 3 else 1 := by
  have hSpn : IsSpn X 6 1 := h
  simp only [IsSpn, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by rw [hcard]; norm_num
  haveI : CharP K 2 := s16k_charP_two_of_card_two hK2
  have hbot : Subgroup.center (StatedSp 3 K) = ⊥ := s16k_center_statedSp_eq_bot_two hK2 3
  have hcentX : Subgroup.center X = ⊥ := s16k_center_eq_bot_of_mulEquiv e hbot
  have hconj_bij : Function.Bijective (MulAut.conj : X →* MulAut X) := by
    refine ⟨?_, fun α => ?_⟩
    · intro x y hxy
      have h1 : (MulAut.conj (x⁻¹ * y) : MulAut X) = 1 := by
        rw [map_mul, map_inv, hxy, inv_mul_cancel]
      have h2 : x⁻¹ * y ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := congrArg (fun f : MulAut X => f g) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        have hz : (x⁻¹ * y) * g = g * (x⁻¹ * y) := by
          have h2' := congrArg (fun z : X => z * (x⁻¹ * y)) h
          simpa [mul_assoc] using h2'
        exact hz.symm
      rw [hcentX, Subgroup.mem_bot] at h2
      exact inv_mul_eq_one.mp h2
    · obtain ⟨x, rfl⟩ := isSpn_six_one_exists_eq_conj hSpn α
      exact ⟨x, rfl⟩
  have hpr : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) =
      CFSG.Open.pRank p (⊤ : Subgroup (StatedSp 3 K)) := by
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
        (MulEquiv.ofBijective (MulAut.conj : X →* MulAut X) hconj_bij),
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  rw [hpr]
  by_cases hp3 : p = 3
  ·
    rw [if_pos hp3]
    have hpK3 : (p : K) ≠ 0 := by
      intro h0
      rw [CharP.cast_eq_zero_iff K 2] at h0
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0).symm
    refine CFSG.SectionRank.pRank_le (p := p) (G := StatedSp 3 K) hp.one_lt ?_
    intro E _ hEel
    have hmap : IsElemAbelian p (E.map (StatedSp 3 K).subtype) :=
      CFSG.SectionRank.isElemAbelian_map hEel _
    have hcomm : ∀ g ∈ E.map (StatedSp 3 K).subtype,
        ∀ h ∈ E.map (StatedSp 3 K).subtype, g * h = h * g := by
      haveI : IsMulCommutative (E.map (StatedSp 3 K).subtype) := hmap.1
      intro g hg h hh
      exact congrArg Subtype.val
        (mul_comm' (⟨g, hg⟩ : ↥(E.map (StatedSp 3 K).subtype)) ⟨h, hh⟩)
    have hexp : ∀ g ∈ E.map (StatedSp 3 K).subtype, g ^ p = 1 := hmap.2
    have hdiv : ∀ i : ℕ, 0 < i → i < 2 → ¬ p ∣ Nat.card K ^ i - 1 := by
      intro i _ hi2
      have hi1 : i = 1 := by omega
      subst hi1
      rw [hK2]
      norm_num
      exact hp.ne_one
    have hbound := CFSG.RankThree.PartOne.LIT.card_le_pow_div_gl
      (K := K) (ι := Fin 3 ⊕ Fin 3) (p := p) hp hpK3 (d := 2) (by norm_num) hdiv
      (E.map (StatedSp 3 K).subtype) hcomm hexp
    rw [Subgroup.card_map_of_injective (StatedSp 3 K).subtype_injective] at hbound
    simpa using hbound
  ·
    rw [if_neg hp3]
    have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hpK : ¬ p ∣ Nat.card K := by
      rw [hK2]
      intro hd
      exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
    have hdiv : (if Even (orderOf (Nat.card K : ZMod p)) then 2 * 3 else 3) /
        orderOf (Nat.card K : ZMod p) ≤ 1 := by
      rw [hK2]
      exact s16k_div_le_one_of_three_le (s16k_three_le_orderOf_two_zmod hp hp2 hp3)
    have hSp : CFSG.pRank p ↥(StatedSp 3 K) ≤ 1 :=
      CFSG.RankThree.PartOne.pRank_statedSp_le_one (K := K) (n := 3) hp hp2 hpK hdiv
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top p (StatedSp 3 K)] at hSp

theorem s16k_sp6_fix_ord (hF : RSp6SpinForm) (hSt : RSp6SpinStab) {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {H : Subgroup (MulAut W)} (hH : IsSpn ↥H 6 1)
    (hrk : rk ↥(⊤ : Subgroup W) = 8) (hirr : IsIrrOn H ⊤ ⊥) :
    ∀ w : W, w ≠ 1 → ∃ g ∈ H, orderOf g = 3 ∧ g w = w := by
  obtain ⟨Q, hQplus, hQinv⟩ := hF W hW H hH hrk hirr
  obtain ⟨hSing, hNon⟩ := hSt W hW H hH hrk hirr Q hQplus hQinv
  intro w hw
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∃ g : ↥(ptCent H w), orderOf g = 3 := by
    by_cases hQw : Q w = 0
    ·
      obtain ⟨N, _, _, hL3⟩ := hSing w hw hQw
      have hquot : Nat.card (↥(ptCent H w) ⧸ N) = 168 := card_eq_of_isL3 hL3
      have hcard : Nat.card ↥(ptCent H w) = 168 * Nat.card ↥N := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hquot]
      have hdvd : 3 ∣ Nat.card ↥(ptCent H w) := by
        rw [hcard]
        exact dvd_mul_of_dvd_left (by norm_num : 3 ∣ 168) _
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      exact ⟨g, hg⟩
    ·
      have hG2 := hNon w hQw
      have hdvd : 3 ∣ Nat.card ↥(ptCent H w) := by
        rw [hG2.1]
        norm_num
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      exact ⟨g, hg⟩
  obtain ⟨g, hg⟩ := key
  exact ⟨(g : MulAut W), (Subgroup.mem_inf.1 g.2).1, by rw [Subgroup.orderOf_coe, hg],
    by simpa using MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 g.2).2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
