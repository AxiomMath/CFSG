module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Nat
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Quot
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Absorb
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec91b

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

namespace HS9

theorem not_two_pow_mul_sq_sub_one {q : ℕ} (hq4 : 4 ≤ q) (hq : 2 ∣ q) :
    ¬ ∃ k : ℕ, q * (q ^ 2 - 1) = 2 ^ k := by
  rintro ⟨k, hk⟩
  have hodd : Odd (q ^ 2 - 1) := by
    obtain ⟨c, rfl⟩ := hq
    have hc1 : 1 ≤ c := by omega
    have e : (2 * c) ^ 2 = 4 * (c * c) := by ring
    rw [e]
    have ht : 1 ≤ c * c := Nat.mul_pos hc1 hc1
    generalize c * c = u at ht
    exact ⟨2 * u - 1, by omega⟩
  have hdvd : q ^ 2 - 1 ∣ 2 ^ k := hk ▸ Dvd.intro_left _ rfl
  have hcop : Nat.Coprime (q ^ 2 - 1) (2 ^ k) :=
    ((Nat.coprime_two_left.mpr hodd).pow_left k).symm
  have h1 : q ^ 2 - 1 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  have : q ^ 2 ≥ 16 := by nlinarith
  omega

theorem isSLModel_two_data {X : Type} [Group X] {q : ℕ} (h4 : 4 ≤ q)
    (hq2 : ∃ s : ℕ, q = 2 ^ s) (h : IsSLModel 2 q X) :
    Nat.card X = q * (q ^ 2 - 1) ∧ IsSimpleGroup X := by
  obtain ⟨K, fK, finK, hK, ⟨e⟩⟩ := h
  obtain ⟨s, hs⟩ := hq2
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hs)
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, card_statedSL_two, hK]
  · haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl (hK ▸ h4))
    exact e.isSimpleGroup

theorem card_omegaPlus_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) = (Nat.card K * (Nat.card K ^ 2 - 1)) ^ 2 := by
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_statedSL_two]
  ring

end HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec97Head_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement) :
    Sec97HeadStatement := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYR, hXY, hXYQ, hcomm⟩, hYsl, -⟩ := hsplit
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  set R := Rt M (LB M Q B) t with hR
  set N := hc.CN t with hN
  set L := LB M Q B with hL
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hqpos : 0 < Nat.card Z := Nat.card_pos
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := HS9.normalizer_of_commutator_le hQX hcomm
  have hXY' : X ≤ Subgroup.normalizer (Y : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y) (Y := X) hQY (fun a ha y hy => by
      have := Q.inv_mem (hcomm y hy a ha)
      rwa [commutatorElement_inv] at this)
  have hRX : R ≤ Subgroup.normalizer (X : Set G) :=
    calc R = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le Subgroup.le_normalizer hYX
  have hRY : R ≤ Subgroup.normalizer (Y : Set G) :=
    calc R = X ⊔ Y := hXY.symm
      _ ≤ _ := sup_le hXY' Subgroup.le_normalizer
  have hNR : N ≤ R := fun x hx => (Ctx.mem_CN.mp hx).1
  have hLR : L ≤ R := le_Rt (M := M) L ht
  have hRN : R ≤ Subgroup.normalizer (N : Set G) := fun r hr =>
    Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hc.CN_conj_mem ht hr hx, fun hx => by
      have := hc.CN_conj_mem ht (R.inv_mem hr) hx
      simpa [mul_assoc] using this⟩
  obtain ⟨hYQnorm, hYmod⟩ := hYsl
  obtain ⟨hYcard, hYsimple⟩ := HS9.isSLModel_two_data hq4 hq2 hYmod
  have hQY_idx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  have hRX_idx : X.relIndex R = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
    have h1 : X.relIndex R = X.relIndex (Y ⊔ X) := by rw [sup_comm, hXY]
    rw [h1, HS9.relIndex_sup_right_of_le_normalizer hYX, ← Subgroup.inf_relIndex_right, hXYQ,
      hQY_idx]
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hs.plus4
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hRN_idx : N.relIndex R = (Nat.card Z * (Nat.card Z ^ 2 - 1)) ^ 2 := by
    have h1 : N.relIndex R = Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) := by
      rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hφ]
    rw [h1, HS9.card_omegaPlus_four (hK ▸ hq4), hK]
  have hN2 : IsPGroup 2 ↥N :=
    hc.isPGroup_CN_of_311 h34 hs5 (h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen t ht
      hs5.notQ (sec9_Rt_ne_LB h34 hs))
  have hNX : N ≤ X := by
    have hDnorm : R ≤ Subgroup.normalizer ((N ⊔ X : Subgroup G) : Set G) := fun r hr => by
      rw [← conjSubgroup_eq_self_iff]
      have e1 : conjSubgroup r (N ⊔ X) = conjSubgroup r N ⊔ conjSubgroup r X :=
        Subgroup.map_sup _ _ _
      rw [e1, conjSubgroup_eq_self_iff.mpr (hRN hr), conjSubgroup_eq_self_iff.mpr (hRX hr)]
    have hD2 : ∃ k : ℕ, X.relIndex (N ⊔ X) = 2 ^ k := by
      rw [HS9.relIndex_sup_right_of_le_normalizer (hNR.trans hRX)]
      exact HS9.relIndex_two_pow_of_isPGroup X hN2
    have hnot2 : ¬ ∃ k : ℕ, Q.relIndex Y = 2 ^ k := by
      rw [hQY_idx]
      exact HS9.not_two_pow_mul_sq_sub_one hq4 hqev
    have hDX := HS9.eq_of_two_power_index hXR hYR hXY hXYQ hRX hRY (sup_le hNR hXR) hDnorm
      le_sup_right ⟨hYQnorm, hYsimple⟩ hnot2 hD2
    exact hDX ▸ le_sup_left
  refine ⟨hNX, ?_⟩
  have hL2 : IsPGroup 2 ↥L := hc.isPGroup_LB h34 hs5.width hs5.n_gt hs5.noA2 hs5.gen
  have hE2 : IsPGroup 2 ↥(L ⊓ X) :=
    hL2.of_injective (Subgroup.inclusion (inf_le_left : L ⊓ X ≤ L))
      (Subgroup.inclusion_injective _)
  have hapos : 0 < Nat.card Z * (Nat.card Z ^ 2 - 1) :=
    Nat.mul_pos hqpos (Nat.sub_pos_of_lt (by nlinarith))
  have hXN_idx : N.relIndex X = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
    have h1 := Subgroup.relIndex_mul_relIndex N X R hNX hXR
    rw [hRN_idx, hRX_idx] at h1
    refine Nat.eq_of_mul_eq_mul_right hapos ?_
    rw [h1]
    ring
  have h2a : X.relIndex L ≤ Nat.card Z := by
    obtain ⟨k, hk⟩ := HS9.relIndex_two_pow_of_isPGroup X hL2
    have hdvd := HS9.relIndex_dvd_of_normalizes hLR hXR (hLR.trans hRX)
    rw [hk, hRX_idx] at hdvd
    rw [hk]
    exact HS9.le_of_two_pow_dvd_mul_sq_sub_one hqev hqpos hdvd
  have h2b : N.relIndex (L ⊓ X) ≤ Nat.card Z := by
    obtain ⟨k, hk⟩ := HS9.relIndex_two_pow_of_isPGroup N hE2
    have hdvd := HS9.relIndex_dvd_of_normalizes (A := L ⊓ X) (B := N) (C := X) inf_le_right hNX
      (inf_le_left.trans (hLR.trans hRN))
    rw [hk, hXN_idx] at hdvd
    rw [hk]
    exact HS9.le_of_two_pow_dvd_mul_sq_sub_one hqev hqpos hdvd
  have hLN_idx : (L ⊓ N).relIndex L = Nat.card Z ^ 2 := by
    rw [Subgroup.inf_relIndex_left]
    exact HS9.relIndex_LB_CN h34 hs
  have hmul := Subgroup.relIndex_mul_relIndex (L ⊓ N) (L ⊓ X) L (inf_le_inf_left L hNX)
    inf_le_left
  have hEq : (L ⊓ N) ⊓ (L ⊓ X) = N ⊓ (L ⊓ X) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨h.2.1, h.1⟩, h.2⟩⟩
  have hA : (L ⊓ N).relIndex (L ⊓ X) = N.relIndex (L ⊓ X) := by
    rw [← Subgroup.inf_relIndex_right (L ⊓ N), ← Subgroup.inf_relIndex_right N, hEq]
  have hB : (L ⊓ X).relIndex L = X.relIndex L := by
    rw [Subgroup.inf_relIndex_left]
  rw [hA, hB, hLN_idx] at hmul
  rw [hA]
  have hq0 : 0 < Nat.card Z := hqpos
  by_contra hne
  have hlt : N.relIndex (L ⊓ X) < Nat.card Z := lt_of_le_of_ne h2b hne
  have : N.relIndex (L ⊓ X) * X.relIndex L < Nat.card Z * Nat.card Z :=
    Nat.mul_lt_mul_of_lt_of_le hlt h2a hq0
  nlinarith [hmul]

end CFSG.RankThree.GF2n.Stroth80
