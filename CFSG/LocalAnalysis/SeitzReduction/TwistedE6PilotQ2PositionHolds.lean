module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Position
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2Main

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.EvenSmallLie CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.OmegaPilot (OmegaNotOddLieInputAt)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem not_normal_neighbour_2E6_nonsplit_two (hset : SeitzSetting G L)
    (hk : Nat.card k = 2 ^ 1) (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {A : Subgroup (ModGL TwistTag.E6.tag K)} (hAJ : A ≤ thetaRankOneGroup (algebraMap k K))
    (hA : Nat.card A = 2 ^ 1 + 1) (hcyc : IsCyclic A) :
    ¬ (((modelToG e (su6Levi σ)).subgroupOf (centralizer (modelToG e A : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (modelToG e A : Set G))))).Normal := by
  have hf : 1 ≤ 1 := le_rfl
  have : CharP K 2 := charP_two_of_card le_rfl hK
  have hKt := inf_centralizer_eq_zpowers_twistedE6 hset hf hK hσ e htC ht
  have hAC := (centralizer_nonsplit_twistedE6 hf hk hK hσ hAJ hA hcyc).2.2.2
  have hXL : modelToG e A ≤ L := map_subtype_le _
  have htX : t ∈ centralizer (modelToG e A : Set G) := centralizer_le hXL htC
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hXodd : Odd (Nat.card (modelToG e A)) := by
    change Odd (Nat.card (((A.subgroupOf (graphFixedRootGroup TwistTag.E6 K σ)).map
      e.symm.toMonoidHom).map L.subtype))
    rw [card_map_symm_subgroupOf hAC, hA]
    decide
  have hXJ : modelToG e A ≤ (((thetaRankOneGroup (algebraMap k K)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 K σ)).map e.symm.toMonoidHom).map L.subtype :=
    map_mono (map_mono fun x hx => mem_subgroupOf.2 (hAJ (mem_subgroupOf.1 hx)))
  obtain ⟨x, z, hz, hxz, hz1, hzU, -, -⟩ :=
    exists_conj_eq_mul_twoSided_twistedE6_two hset.standardSetting hk hK hσ e ht hKt
  have hzt : z * t = t * z := mem_centralizer_iff.1 htC z hz.1
  have ht2 : t ^ 2 = 1 := by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hz2 : orderOf z = 2 := by
    have hsq : (x⁻¹ * t * x) ^ 2 = 1 := by
      have : (x⁻¹ * t * x) ^ 2 = x⁻¹ * t ^ 2 * x := by
        rw [sq, sq]
        group
      rw [this, ht2, mul_one, inv_mul_cancel]
    rw [hxz] at hsq
    have hz2' : z ^ 2 = 1 := by
      have e1 : (t * z) ^ 2 = t ^ 2 * z ^ 2 := by
        rw [sq, sq, sq]
        calc t * z * (t * z) = t * (z * t) * z := by group
          _ = t * (t * z) * z := by rw [hzt]
          _ = t * t * (z * z) := by group
      rw [e1, ht2, one_mul] at hsq
      exact hsq
    exact orderOf_eq_prime hz2' hz1
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_le_centralizer_mulEquiv_of_conj_eq_mul_twistedE6_two
    hset.standardSetting hk hK hσ e htC ht hXodd hXJ hz.1 hz2 hzU hxz
  obtain ⟨-, -, hDX, -, -, -⟩ := neighbour_data_2E6_nonsplit_two hset hk hK hσ e hAJ hA hcyc
  obtain ⟨-, hsyl, -⟩ :=
    neighbour_standard_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc rfl htX rfl
  obtain ⟨hDs, hDp, hDo⟩ := su6Levi_subgroupOf_facts hf hk hK hσ
  obtain ⟨hDq, hZD, hOutD⟩ := lemmaA_data_of_simple (G := G) e hDo
  have hDL : modelToG e (su6Levi σ) ≤ L := map_subtype_le _
  have hrepD : repX K 0 ∈ su6Levi σ := repX_mem_su6Levi (apply_apply_eq hK hσ) 0
  have hyD : (e.symm (repXC (apply_apply_eq hK hσ) 0) : G) ∈ modelToG e (su6Levi σ) :=
    ⟨e.symm (repXC (apply_apply_eq hK hσ) 0),
      ⟨repXC (apply_apply_eq hK hσ) 0, mem_subgroupOf.2 hrepD, rfl⟩, rfl⟩
  have hy1 : (e.symm (repXC (apply_apply_eq hK hσ) 0) : G) ≠ 1 := by
    intro h
    have h' : e.symm (repXC (apply_apply_eq hK hσ) 0) = 1 := Subtype.ext h
    have h'' : repXC (apply_apply_eq hK hσ) 0 = 1 := by
      rw [← e.apply_symm_apply (repXC (apply_apply_eq hK hσ) 0), h', map_one]
    have h3 : repX K 0 = 1 := congrArg Subtype.val h''
    have h4 := orderOf_repX (K := K) 0
    rw [h3, orderOf_one] at h4
    exact absurd h4 (by decide)
  exact F4Pilot.not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD
    (hDL.trans hLt) hsyl hyD hy1 (Or.inr rfl) hP ⟨eP.trans (mapSymmEquiv e _)⟩

theorem twistedE6TwoPositionInput_holds : TwistedE6TwoPositionInput :=
  fun _ _ _ _ _ _ _ _ _ hset hk hK _ hσ e _ htC ht _ hAJ hA hcyc =>
    not_normal_neighbour_2E6_nonsplit_two hset hk hK hσ e htC ht hAJ hA hcyc

theorem false_of_twistedE6_two_of_rows (hGLS : GLS3OddLieAutComponentsInput)
    (hres : CatSUmSporadicAtF 6 1) (hF : TwistedE6TwoFieldRowInput)
    (hS : TwistedE6TwoSwapRowInput) (hset : SeitzSetting G L)
    (hL : LieModel L .twistedE6 0 2 1) : False :=
  false_of_twistedE6_two_of_inputs hGLS hres twistedE6TwoPositionInput_holds
    (twistedE6TwoRowsInput_of_rows hF hS) hset hL

end CFSG.SeitzReduction.TwistedE6Pilot
