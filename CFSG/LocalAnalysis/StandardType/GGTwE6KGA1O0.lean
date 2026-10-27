module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.Open

private theorem o0_exists_theta {f : ℕ} (hf : 1 ≤ f) :
    ∃ Θ : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
        RingAut (GaloisField 2 (2 * f)),
      Θ.ker = LayerSixE.twInndiagAut f := by
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K := frobQEquiv hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, σ c = c ^ (2 ^ f) := fun c => by
    change frobQ 2 f c = c ^ (2 ^ f)
    exact frobQ_apply 2 f c
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, ⟨E⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σ hσ
  refine ⟨Θ, ?_⟩
  rw [twInndiagAut_eq_range_twistedE6InndiagConj hf,
    CFSG.HardMathSupport.Timmesfeld.CrossChar.range_twistedE6InndiagConj]
  exact hker

theorem normal_twInndiagAut {f : ℕ} (hf : 1 ≤ f) : (LayerSixE.twInndiagAut f).Normal := by
  obtain ⟨Θ, hΘ⟩ := o0_exists_theta hf
  rw [← hΘ]
  exact MonoidHom.normal_ker Θ

private theorem o0_odd_of_three_dvd {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1) : Odd f := by
  have hcast : ((2 : ℕ) : ZMod 3) ^ f = -1 := by
    have h0 : ((2 ^ f + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h3
    push_cast at h0
    exact add_eq_zero_iff_eq_neg.mp h0
  rw [show ((2 : ℕ) : ZMod 3) = -1 by decide] at hcast
  exact (neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ZMod 3) ≠ 1)).mp hcast

private theorem o0_pow_two_dvd_two_mul_odd {n f : ℕ} (hn : 1 ≤ n) (hf : Odd f)
    (h : 2 ^ n ∣ 2 * f) : n = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ, mul_comm (2 ^ m) 2] at h
  have hm : 2 ^ m ∣ f := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp h
  have hodd : Odd (2 ^ m) := Odd.of_dvd_nat hf hm
  have hm0 : m = 0 := by
    by_contra hne
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [pow_succ] at hodd
    exact Odd.not_two_dvd_nat hodd ⟨2 ^ k, by ring⟩
  omega

theorem exists_zpowers_of_inf_twInndiagAut_eq_bot {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    {U : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUI : U ⊓ LayerSixE.twInndiagAut f = ⊥) :
    ∃ t : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)),
      t ^ 2 = 1 ∧ t ∉ LayerSixE.twInndiagAut f ∧ U = Subgroup.zpowers t := by
  let K := GaloisField 2 (2 * f)
  let C := ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))
  obtain ⟨Θ, hΘ⟩ := o0_exists_theta hf
  have hfodd : Odd f := o0_odd_of_three_dvd h3
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite C := inferInstance
  haveI : Finite U := inferInstance
  have hne1 : ∃ t ∈ U, t ≠ 1 := by
    by_contra h
    push Not at h
    exact hU ((Subgroup.eq_bot_iff_forall U).mpr h)
  obtain ⟨t, htU, htne⟩ := hne1
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hU2
  have hnpos : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [h0, pow_zero] at hn
    exact hU (Subgroup.card_eq_one.mp hn)
  let φ : U →* RingAut K := Θ.comp U.subtype
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : Θ (x : MulAut C) = Θ (y : MulAut C) := hxy
    have hmem : (x : MulAut C) * (y : MulAut C)⁻¹ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy', mul_inv_cancel]
    rw [hΘ] at hmem
    have hxU : (x : MulAut C) * (y : MulAut C)⁻¹ ∈ U :=
      mul_mem x.2 (inv_mem y.2)
    have hmem2 : (x : MulAut C) * (y : MulAut C)⁻¹ ∈
        U ⊓ LayerSixE.twInndiagAut f := ⟨hxU, hmem⟩
    rw [hUI] at hmem2
    exact Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem2))
  have hdvd : Nat.card U ∣ Nat.card (RingAut K) :=
    Subgroup.card_dvd_of_injective φ hφinj
  have hring : Nat.card (RingAut K) = 2 * f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
      (GaloisField.card 2 (2 * f) (by omega))).1
  have hdvd2 : 2 ^ n ∣ 2 * f := by
    rw [hn, hring] at hdvd
    exact hdvd
  have hn1 : n = 1 := o0_pow_two_dvd_two_mul_odd hnpos hfodd hdvd2
  have hcardU : Nat.card U = 2 := by rw [hn, hn1, pow_one]
  have hord : orderOf t = 2 := by
    have hd : orderOf t ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard U htU
      rwa [hcardU] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) htne
    · exact h
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hord] at this
  have htnot : t ∉ LayerSixE.twInndiagAut f := by
    intro ht
    have hmem : t ∈ U ⊓ LayerSixE.twInndiagAut f := ⟨htU, ht⟩
    rw [hUI] at hmem
    exact htne (Subgroup.mem_bot.mp hmem)
  refine ⟨t, ht2, htnot, ?_⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr htU) ?_
  rw [Nat.card_zpowers, hord, hcardU]

end CFSG.StandardType.NoOffTwE6Three
