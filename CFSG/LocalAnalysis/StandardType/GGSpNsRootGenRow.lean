module

public import CFSG.LocalAnalysis.StandardType.GGSpNsRootGenLabels
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.ClassicalGroups.Alternating.PointRadicalFixedCard
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType

open CFSG.Assembly TableBSymp
open CFSG.ClassicalGroups.Alternating CFSG.ClassicalGroups.Symplectic

private theorem two_dvd_card_symplecticProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) : 2 ∣ Nat.card (LargeEvenProj (LargeEvenSpGroup K n)) := by
  have : NeZero n := ⟨by omega⟩
  rw [Nat.card_congr (spProjEquivSp.trans spEquiv).toEquiv]
  have hB : (spForm n K).IsAlt := spForm_isAlt
  obtain ⟨v, hv⟩ : ∃ v : Fin n ⊕ Fin n → K, v ≠ 0 :=
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, fun h => one_ne_zero (Pi.single_eq_zero_iff.mp h)⟩
  obtain ⟨w, hw⟩ : ∃ w, spForm n K v w ≠ 0 := by
    by_contra h
    exact hv (spForm_nondegenerate.1 v fun w => not_not.mp fun hw => h ⟨w, hw⟩)
  have h1 : Tsp hB v 1 ≠ 1 := by
    intro h
    have h' := congrArg (fun g : Gsp (spForm n K) => g.app w) h
    simp only [Tsp_app, one_mul, Gsp.app_one, add_eq_left, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact hw (by rw [← hB.neg_eq w v, h', neg_zero])
    · exact hv h'
  have h2 : Tsp hB v 1 ^ 2 = 1 := by rw [pow_two, Tsp_mul_self]
  exact orderOf_eq_prime h2 h1 ▸ orderOf_dvd_natCard _

theorem ggTorusRootGenAvoidKG_symplecticFour
    {K : Type} [Field K] [Finite K]
    {f p : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (r : ℕ) :
    GGTorusRootGenAvoidKG p r (LargeEvenProj (LargeEvenSpGroup K 2))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K 2)) (LargeEvenGSpSet K 2)) := by
  have : CharP K 2 := charP_two_of_card hK
  have hpK : (p : K) ≠ 0 := by
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm
  let e : LargeEvenProj (LargeEvenSpGroup K 2) ≃* LargeEvenSpGroup K 2 := spProjEquivSp
  refine ggTorusRootGenAvoidKG_of_mulEquiv e (fun φ hφ => ?_)
    (ggTorusRootGenAvoidKG_of_scTorusModel hp
      (fun L' _ _ ψ hψ hker hperf => statedSp_injective_of_cover hK hf le_rfl L' ψ hψ hker hperf)
      (center_statedSp_eq_bot_of_charP_two (by norm_num)) subset_rfl
      fun E hE _ h3 _ => absurd (h3.trans (SpJoin.card_le_pow_of_isElemAbelian hp hp2 hpK E hE))
        (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num))))
  obtain ⟨x, rfl⟩ := sp_I_subset_inn hφ
  refine ⟨e x, MulEquiv.ext fun y => ?_⟩
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem recipeSymplecticNs_rootGenAvoidKG_zero
    {l n p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n + 1) (hn : 2 ≤ n) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusRootGenAvoidKG p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  refine ⟨K, inferInstance, inferInstance, hK, hQ, 0,
    TypeA.ggTorusLift_zero (two_dvd_card_symplecticProj (by omega)), ?_⟩
  rcases (show l = 2 ∨ 3 ≤ l by omega) with rfl | hl3
  · exact ggTorusRootGenAvoidKG_symplecticFour hK hn hp hp2 0
  · exact ggTorusRootGenAvoidKG_symplecticNs hK hn hl3 hp hp2 hpq 0

theorem ggRootGenKGAvoidOn_symp :
    GGRootGenKGAvoidOn GGRootGenSympLabel := by
  rintro p ⟨t, l, n⟩ hp hp2 hlab ⟨hpn, hn, ht⟩
  dsimp only at ht hpn hn
  intro Q hQ
  rcases ht with rfl | rfl <;>
    exact recipeSymplecticNs_rootGenAvoidKG_zero hp hp2 hpn hn hlab.2.1 hQ

theorem ggRootGenLInputOnNS_symp :
    GGRootGenLInputOnNS GGRootGenSympLabel := by
  intro G _ _ p B Bs x L D J hHyp _ _ _ hL
  exact ggRootCompGenAvoiding_L_of_avoidOn ggRootGenKGAvoidOn_symp hHyp hL

theorem ggRootGenNbrInputOnNS_symp :
    GGRootGenNbrInputOnNS GGRootGenSympLabel := by
  intro G _ _ p B Bs x L D J hHyp _ _ _ y K hnb hK
  exact ggRootCompGenAvoiding_nbr_of_avoidOn ggRootGenKGAvoidOn_symp hHyp hnb hK

theorem ggRootGenLInputOnNS_notSpOrthSplitOrth_of_notSymp
    (h : GGRootGenLInputOnNS fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (GGRootGenSpOrthSplitLabel p lab ∨ GGRootGenOrthLabel p lab ∨
        GGRootGenSympLabel p lab)) :
    GGRootGenLInputOnNS fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (GGRootGenSpOrthSplitLabel p lab ∨ GGRootGenOrthLabel p lab) := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW hL
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSympLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (GGRootGenSpOrthSplitLabel p lab ∨
        GGRootGenOrthLabel p lab ∨ GGRootGenSympLabel p lab)))
      (fun lab hlab => (em (GGRootGenSympLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim (fun h₁ => hlab.2 (Or.inl h₁))
          fun h₂ => h₂.elim (fun h₃ => hlab.2 (Or.inr h₃)) hn⟩) hL).elim_or with h₁ | h₂
  · exact ggRootGenLInputOnNS_symp G p B Bs x L D J hHyp hq hN hW h₁
  · exact h G p B Bs x L D J hHyp hq hN hW h₂

theorem ggRootGenNbrInputOnNS_notSpOrthSplitOrth_of_notSymp
    (h : GGRootGenNbrInputOnNS fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (GGRootGenSpOrthSplitLabel p lab ∨ GGRootGenOrthLabel p lab ∨
        GGRootGenSympLabel p lab)) :
    GGRootGenNbrInputOnNS fun p lab => GGRootGenOpenLabel p lab ∧
      ¬ (GGRootGenSpOrthSplitLabel p lab ∨ GGRootGenOrthLabel p lab) := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW y K hnb hK
  rcases (GGInnerDiagOnLabel.mono_label (T := fun p lab => GGRootGenSympLabel p lab ∨
      (GGRootGenOpenLabel p lab ∧ ¬ (GGRootGenSpOrthSplitLabel p lab ∨
        GGRootGenOrthLabel p lab ∨ GGRootGenSympLabel p lab)))
      (fun lab hlab => (em (GGRootGenSympLabel p lab)).imp_right fun hn =>
        ⟨hlab.1, fun h' => h'.elim (fun h₁ => hlab.2 (Or.inl h₁))
          fun h₂ => h₂.elim (fun h₃ => hlab.2 (Or.inr h₃)) hn⟩) hK).elim_or with h₁ | h₂
  · exact ggRootGenNbrInputOnNS_symp G p B Bs x L D J hHyp hq hN hW y K hnb h₁
  · exact h G p B Bs x L D J hHyp hq hN hW y K hnb h₂

end CFSG.StandardType

end
