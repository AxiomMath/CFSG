module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotNeighbourStandardBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi


variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem centralizer_thetaRankOneGroup_inf_eq_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    centralizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ = su6Levi σ := by
  have hf : 1 ≤ 1 := le_rfl
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP k 2 := F4Pilot.charP_two_of_natCard_eq_two_pow hk
  obtain ⟨hLX, -⟩ := su6Levi_facts hf hk hK hσ
  obtain ⟨X, hXJ, hcyc, hX⟩ := exists_nonsplit_le_thetaRankOneGroup hf hk hK
  obtain ⟨hcen, -, hXD, -⟩ := centralizer_nonsplit_twistedE6 hf hk hK hσ hXJ hX hcyc
  refine le_antisymm (fun g hg => ?_) (le_inf hLX (su6Levi_le_graphFixedRootGroup σ))
  obtain ⟨hgJ, hgC⟩ := mem_inf.1 hg
  have hgX : g ∈ centralizer (X : Set (ModGL TwistTag.E6.tag K)) ⊓
      graphFixedRootGroup TwistTag.E6 K σ := mem_inf.2 ⟨centralizer_le hXJ hgJ, hgC⟩
  rw [hcen] at hgX
  have hgX' : g ∈ ((X ⊔ su6Levi σ : Subgroup (ModGL TwistTag.E6.tag K)) :
      Set (ModGL TwistTag.E6.tag K)) := hgX
  rw [coe_mul_of_left_le_normalizer_right _ _ (hXD.trans (centralizer_le_normalizer _))] at hgX'
  obtain ⟨a, ha, d, hd, rfl⟩ := Set.mem_mul.1 hgX'
  have haJ : a ∈ centralizer (thetaRankOneGroup (algebraMap k K) :
      Set (ModGL TwistTag.E6.tag K)) := by
    have := mul_mem hgJ (inv_mem (hLX hd))
    rwa [mul_inv_cancel_right] at this
  have haJ' : a ∈ thetaRankOneGroup (algebraMap k K) := hXJ ha
  rw [thetaRankOneGroup_eq_range hK2] at haJ'
  obtain ⟨B, hB⟩ := haJ'
  have hBc : B ∈ center (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [mem_center_iff]
    intro B'
    apply injective_thetaSL2_comp_map hK2 (algebraMap k K)
    have hB'J : ((thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))) B' ∈
        thetaRankOneGroup (algebraMap k K) := by
      rw [thetaRankOneGroup_eq_range hK2]
      exact ⟨B', rfl⟩
    have h := mem_centralizer_iff.1 haJ _ hB'J
    rw [map_mul, map_mul, hB]
    exact h
  have ha1 : a = 1 := by
    rw [← hB, E6Pilot.eq_one_of_mem_center_SL2 hBc, map_one]
  rw [ha1, one_mul]
  exact hd

theorem centralizer_thetaRankOneGroup_subgroupOf_two (hk : Nat.card k = 2 ^ 1)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) :
    centralizer ((thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ) : Set (graphFixedRootGroup TwistTag.E6 K σ)) =
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  rw [centralizer_subgroupOf (thetaRankOneGroup_le_C0 le_rfl hk hK hσ),
    ← inf_subgroupOf_right, centralizer_thetaRankOneGroup_inf_eq_two hk hK hσ]

theorem factF56_leviX_two (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1) (κ κ' : Fin 2)
    (ι : (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ) ≃*
      (![((su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordTX)).toMonoidHom,
      ((uLevi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
        (MulAut.conj (relWeylC σ relWordUX)).toMonoidHom] κ')) :
    Nonempty (centralizer ((((((thetaRankOneGroup (algebraMap k K)).subgroupOf
        (graphFixedRootGroup TwistTag.E6 K σ)).subgroupOf _).map ι.toMonoidHom).map
          (Subgroup.subtype _) : Subgroup (graphFixedRootGroup TwistTag.E6 K σ)) :
        Set (graphFixedRootGroup TwistTag.E6 K σ)) ≃*
      (su6Levi σ).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) := by
  obtain ⟨-, m, -, hm⟩ := factF5_leviX le_rfl hk hK hσ κ κ' ι
  rw [hm]
  obtain ⟨e⟩ := E6Pilot.nonempty_centralizer_map_conj_mulEquiv
    ((thetaRankOneGroup (algebraMap k K)).subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)) m
  rw [centralizer_thetaRankOneGroup_subgroupOf_two hk hK hσ] at e
  exact ⟨e⟩

end CFSG.SeitzReduction.TwistedE6Pilot
