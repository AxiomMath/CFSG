module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.RankFourTheoremC.PPointExoticRank
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporJ4
public import CFSG.Sporadic.J4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open

theorem card_le_of_isSpor_J4_of_isElemAbelian
    {K : Type} [Group K] [Finite K]
    (hK : IsSpor K .J4) (B : Subgroup (MulAut K)) (hB : IsElemAbelian 11 B) :
    Nat.card B ≤ 11 ^ 2 := by
  obtain ⟨e⟩ := hK
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J4.nonempty_mulEquiv
  exact CFSG.LocalAnalysis.RankFourTheoremC.autRankTwoAt_jFour K ⟨e.trans b⟩ B hB

theorem exists_orderOf_eleven_commute_of_isSpor_J4
    {K : Type} [Group K]
    (hK : IsSpor K .J4) (x : K) (hx : orderOf x = 3) :
    ∃ w : K, orderOf w = 11 ∧ Commute x w := by
  obtain ⟨e⟩ : Nonempty (K ≃* CFSG.Blueprint.NativeSporadic.J4) := hK
  obtain ⟨φ⟩ : Nonempty (CFSG.Sporadic.J4.J ≃* CFSG.Blueprint.NativeSporadic.J4) :=
    ⟨(CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer
      (CFSG.Sporadic.J4Schreier.Q11 : Set CFSG.Sporadic.J4.J) ⊓
      Subgroup.centralizer ({CFSG.Sporadic.J4Schreier.qz} : Set CFSG.Sporadic.J4.J))) 3
    (by rw [CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.card_normalizer_inf_centralizer_qz]
        norm_num)
  have hc0 : orderOf (c : CFSG.Sporadic.J4.J) = 3 := (Subgroup.orderOf_coe c).trans hc
  have hcz : Commute CFSG.Sporadic.J4Schreier.qz (c : CFSG.Sporadic.J4.J) :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 c.2).2 _ (Set.mem_singleton _)
  have hc3 : (c : CFSG.Sporadic.J4.J) ^ 3 = 1 := by
    rw [← hc0]
    exact pow_orderOf_eq_one _
  have hc1 : (c : CFSG.Sporadic.J4.J) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc0
    exact absurd hc0 (by norm_num)
  have hq0 := CFSG.Sporadic.J4Schreier.orderOf_qz
  have hq11 : CFSG.Sporadic.J4Schreier.qz ^ 11 = 1 := by
    rw [← hq0]
    exact pow_orderOf_eq_one _
  have hq1 : CFSG.Sporadic.J4Schreier.qz ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hq0
    exact absurd hq0 (by norm_num)
  have hφc : orderOf (φ c) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hc3, map_one])
      (fun h => hc1 (φ.injective (h.trans (map_one φ).symm)))
  have hx3 : x ^ 3 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hex : orderOf (e x) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hx3, map_one])
      (fun h => hx1 (e.injective (h.trans (map_one e).symm)))
  obtain ⟨k, hk⟩ :=
    CFSG.RankThree.PartTwo.Sec4.RonanK432.j4_isConj_of_orderThree (φ c) (e x) hφc hex
  have hw11 : (k * φ CFSG.Sporadic.J4Schreier.qz * k⁻¹) ^ 11 = 1 := by
    rw [conj_pow, ← map_pow, hq11, map_one, mul_one, mul_inv_cancel]
  have hw1 : k * φ CFSG.Sporadic.J4Schreier.qz * k⁻¹ ≠ 1 := by
    intro h
    apply hq1
    apply φ.injective
    rw [map_one]
    calc φ CFSG.Sporadic.J4Schreier.qz
        = k⁻¹ * (k * φ CFSG.Sporadic.J4Schreier.qz * k⁻¹) * k := by group
      _ = 1 := by rw [h]; group
  refine ⟨e.symm (k * φ CFSG.Sporadic.J4Schreier.qz * k⁻¹), ?_, ?_⟩
  · exact orderOf_eq_prime (by rw [← map_pow, hw11, map_one])
      (fun h => hw1 (e.symm.injective (h.trans (map_one e.symm).symm)))
  · have hcq : Commute (φ c) (φ CFSG.Sporadic.J4Schreier.qz) := hcz.symm.map φ
    have h1 : Commute (e x) (k * φ CFSG.Sporadic.J4Schreier.qz * k⁻¹) := by
      rw [← hk]
      exact (Commute.conj_iff k).2 hcq
    have h2 := h1.map e.symm
    rwa [MulEquiv.symm_apply_apply] at h2

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08
