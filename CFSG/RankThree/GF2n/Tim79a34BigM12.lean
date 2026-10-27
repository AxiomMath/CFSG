module

public import CFSG.RankThree.GF2n.Tim79a34BigStandard
public import CFSG.RankThree.GF2n.Tim79a34BigBarLemmas
public import CFSG.RankThree.GF2n.Tim79a34BigM12Lemma
public import CFSG.RankThree.GF2n.Tim79a34BigSpFacts

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Blueprint
open scoped commutatorElement

@[expose] def M12OrderStatement : Prop := Nat.card ↥NativeSporadic.M12 = 95040

@[expose] def M12A5CentralizerStatement : Prop :=
  ∀ R' : Subgroup ↥NativeSporadic.M12, Nat.card R' = 60 → commutator R' = ⊤ →
    Nat.card (Subgroup.centralizer (R' : Set ↥NativeSporadic.M12)) ≤ 2

@[expose] def M12AutOrderStatement : Prop :=
  Nat.card (MulAut ↥NativeSporadic.M12) ≤ 2 * Nat.card ↥NativeSporadic.M12

theorem bigM12Statement_of_bar [IsSimpleGroup ↥NativeSporadic.M12]
    (hM12 : M12OrderStatement) (hF1 : M12A5CentralizerStatement)
    (hF2 : M12AutOrderStatement)
    (h1 : BigRbarIsoStatement) (h2 : BigWbarCardStatement)
    (h3 : BigWbarCentralizesStatement) (h5 : BigEpsilonNormalizerStatement)
    (h6 : BigEpsilonCentralizerStatement) (h7 : BigRegularStatement) : BigM12Statement := by
  intro G _ _ M V Q P H hH hM
  obtain ⟨e0⟩ := hM
  have e : ↥(Subgroup.normalClosure (RbarM M V H : Set (Mbar M))) ≃* ↥NativeSporadic.M12 := e0
  obtain ⟨f, hf, h2f, n, hn, Φ, hΦ, -⟩ := id hH.three
  have hq4 : 4 ≤ 2 ^ f := h2f ▸ hH.q_big
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have : f ≤ 1 := by omega
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  obtain ⟨eR⟩ := h1 G M V Q P H hH n f hn h2f ⟨MulEquiv.ofBijective Φ hΦ⟩
  have hm : 1 ≤ n - 1 := by omega
  haveI : IsSimpleGroup ↥(RbarM M V H) := by
    haveI := isSimpleGroup_statedSp_gf2f hm hf2
    exact eR.isSimpleGroup
  have hnc : ¬ IsMulCommutative ↥(RbarM M V H) := by
    intro hc
    apply not_isMulCommutative_statedSp_gf2f hm hf2
    exact ⟨⟨fun a b => eR.symm.injective (by
      rw [map_mul, map_mul]
      exact hc.is_comm.comm _ _)⟩⟩
  have hdvd : Nat.card ↥(StatedSp (n - 1) (GaloisField 2 f)) ∣ 95040 := by
    rw [← Nat.card_congr eR.toEquiv, ← hM12, ← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le (Subgroup.subset_normalClosure)
  obtain ⟨hm1, hf1⟩ := eq_of_card_statedSp_dvd_m12 hm hf2 hdvd
  have hcard60 : Nat.card ↥(RbarM M V H) = 60 := by
    rw [Nat.card_congr eR.toEquiv, hm1, hf1]
    exact card_statedSp_one_two
  have hperf : commutator ↥(RbarM M V H) = ⊤ := (bar_isQuasisimple hnc).1
  have hB4 : Nat.card ↥(WbarM M V H) = 4 := by
    rw [h2 G M V Q P H hH, ← h2f, hf1]
    norm_num
  exact false_of_m12_data (Subgroup.normalClosure (RbarM M V H : Set (Mbar M)))
    (RbarM M V H) (WbarM M V H) e hM12 hF1 hF2 Subgroup.subset_normalClosure hcard60 hperf
    (isElemAbelian_wbar hH) hB4 (h3 G M V Q P H hH) (h5 G M V Q P H hH)
    (h6 G M V Q P H hH) (h7 G M V Q P H hH)

end CFSG.RankThree.GF2n.Tim79a
