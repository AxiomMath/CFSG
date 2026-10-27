module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndSmall
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7Lift
import CFSG.GroupTheory.PCoreSurjective
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangCount
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddJ1Cent
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddSigPi
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R92a
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem card_bar2_opp_dvd_card_xbar9 (S : SliceCore D L D₃ Y H) :
    Nat.card (Bar2 (Opp 3 Y)) ∣ Nat.card (xbar9 Y H) := by
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun y hy => F09.opp_le_L9 Y H hy
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (toImg9 hXH)
    (toImg9_surjective hXH) (S.isPGroup_ker_toImg9 hXH)
  rw [xbar9, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(F09.img9 H (Opp 3 Y))),
    ← Nat.card_congr e.toEquiv]
  exact Dvd.intro _ rfl

theorem xbar9_le_wbar9 (S : SliceCore D L D₃ Y H) : xbar9 Y H ≤ wbar9 D Y H := by
  have hXM : Opp 3 Y ≤ H ⊓ D.M := le_inf ((opp_le 3 Y).trans S.Y_le_H)
    ((opp_le 3 Y).trans S.Y_le_M)
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (H ⊓ D.M) :=
    Subgroup.map_mono fun y hy => hXM hy
  exact fun z hz => Subgroup.mem_subgroupOf.2 (hle (Subgroup.mem_subgroupOf.1 hz))

theorem false_of_wbar9_eq_top (S : SliceCore D L D₃ Y H) {E : Subgroup G}
    (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) (hW : wbar9 D Y H = ⊤) : False := by
  have hLM : F09.L9 Y H ≤ D.M := by
    intro l hl
    have hlH : l ∈ H := L9_le_of_le S.Y_le_H hl
    have hl' : (⟨l, hlH⟩ : ↥H) ∈ (F09.L9 Y H).subgroupOf H := Subgroup.mem_subgroupOf.2 hl
    have hmem : (⟨_, Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) hl'⟩ :
        F09.Lbar9 Y H) ∈ wbar9 D Y H := by
      rw [hW]
      exact Subgroup.mem_top _
    obtain ⟨g, hg, hgl⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hmem)
    have hgl' : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) g =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) ⟨l, hlH⟩ := hgl
    obtain ⟨c, hc, hgc⟩ := (QuotientGroup.mk'_eq_mk' _).1 hgl'
    have hlc : l = (g : G) * (c : G) := by rw [← Subgroup.coe_mul, hgc]
    rw [hlc]
    exact D.M.mul_mem (Subgroup.mem_subgroupOf.1 hg).2 (hI (Subgroup.mem_map_of_mem H.subtype hc))
  exact S.not_H_le_M ((F09.eq_L9_sup_of_hyp91 hyp).le.trans (sup_le hLM inf_le_right))

end SliceCore

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem not_isSpor_J1_Lbar9 (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hI : F09.I9 H ≤ D.M) (h11 : q = 11)
    (hSp : CFSG.CGT.PushingUpLit.CGT6.SporadicThreeCenterSmallPrimes) :
    ¬ IsSpor (F09.Lbar9 Y H) .J1 := by
  intro hJ
  have hcard : Nat.card (F09.Lbar9 Y H) = 175560 := by
    obtain ⟨e⟩ : Nonempty (F09.Lbar9 Y H ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hJ
    exact (Nat.card_congr (e.trans CFSG.Walter.walterJ1EquivNative.symm).toEquiv).trans
      CFSG.Walter.J1Props.card_walterJ1
  have hX : 660 ∣ Nat.card (xbar9 Y H) := by
    have h2 := two_mul_card_of_isL2Odd S.prime S.q_ne_two S.shape_opp
    rw [h11] at h2
    have h660 : Nat.card (Bar2 (Opp 3 Y)) = 660 := by
      norm_num at h2
      omega
    rw [← h660]
    exact S.card_bar2_opp_dvd_card_xbar9
  have hXW : xbar9 Y H ≤ wbar9 D Y H := S.xbar9_le_wbar9
  have hmod : ∀ p : ℕ, p.Prime → 3 < p → p ∣ 660 → ¬ p * p ∣ 175560 →
      (wbar9 D Y H).index ≡ 1 [MOD p] := by
    intro p hp hp3 hp660 hpp
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := xbar9 Y H) p (hp660.trans hX)
    have hAq : Nat.card (zpowers (x : F09.Lbar9 Y H)) = p := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
    have hAqX : zpowers (x : F09.Lbar9 Y H) ≤ xbar9 Y H := (zpowers_le).mpr x.2
    have hNW := S.normalizer_le_wbar9_of_not_dvd hN hI hp (by omega)
      (S.not_dvd_card_L9_inf_I9_of_center hI hp (by omega)
        (S.not_dvd_card_center_barImage_L9 hyp hI hSp hJ hp hp3)) _ hAqX hAq
    refine CFSG.HardMathSupport.Timmesfeld.LocalTwo.index_modEq_one_of_normalizer_le
      (hAqX.trans hXW) (IsPGroup.of_card (n := 1) (by rw [hAq, pow_one])) ?_
      fun n hn => hNW hn
    intro hdvd
    have hci := Subgroup.card_mul_index (zpowers (x : F09.Lbar9 Y H))
    rw [hAq, hcard] at hci
    obtain ⟨c, hc⟩ := hdvd
    exact hpp ⟨c, by rw [← hci, hc, mul_assoc]⟩
  have h5 := hmod 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11' := hmod 11 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hidx : (wbar9 D Y H).index = 1 := by
    obtain ⟨t, ht⟩ := hX.trans (Subgroup.card_dvd_of_le hXW)
    have hci := Subgroup.card_mul_index (wbar9 D Y H)
    rw [ht, hcard] at hci
    have hd : (wbar9 D Y H).index ∣ 266 := ⟨t, by
      have h1 : 660 * ((wbar9 D Y H).index * t) = 660 * 266 := by
        rw [show (660 : ℕ) * 266 = 175560 from rfl, ← hci]
        ring
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
    have hle : (wbar9 D Y H).index ≤ 266 := Nat.le_of_dvd (by norm_num) hd
    unfold Nat.ModEq at h5 h11'
    obtain ⟨k, hk⟩ : ∃ k, (wbar9 D Y H).index = 55 * k + 1 :=
      ⟨(wbar9 D Y H).index / 55, by omega⟩
    have hk4 : k ≤ 4 := by omega
    rw [hk] at hd ⊢
    interval_cases k <;> first | rfl | (norm_num at hd)
  exact S.false_of_wbar9_eq_top hyp hI (Subgroup.index_eq_one.mp hidx)

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
