module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSQ2U62Setup
import CFSG.LocalAnalysis.StandardType.GGResidualRk1UnitaryTwoNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitary
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseTwoE

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem card_or_center_of_typeE6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e) (hBB : B = Bs) {X : Subgroup G}
    (hX : X ∈ 𝒦)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs X)
    {σ : Fin 6 ≃ ι} (hM : M = CoxeterMatrix.E₆.reindex σ) :
    3 ^ 6 ≤ Nat.card Bs ∨ Subgroup.center ↥X = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := ggRouteCfg_isElemAbelian hcfg
  have hW6 : GGWeylOfType 3 CoxeterMatrix.E₆ (ggAutomizerJoin L Bs 𝒦) := by
    subst hM
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have h5 : 3 ^ 5 ≤ Nat.card Bs := E6QTwo.three_pow_five_le_card hBs hcfg.1.2.2.2.1
    (fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer (ggAutomizerJoin_le_top L Bs 𝒦 hφ)) hW6
  obtain ⟨k, hk⟩ := hBs.isPGroup.exists_card_eq
  rw [hk] at h5 ⊢
  have hk5 : 5 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h5
  rcases lt_or_ge k 6 with hk6 | hk6
  · obtain rfl : k = 5 := by omega
    exact Or.inr (GGSecFiveRouteCfg.center_eq_bot_of_twA5_E6_member hcfg hpres ⟨σ, hM⟩ hBB hX
      hlab hk)
  · exact Or.inl (Nat.pow_le_pow_right (by norm_num : 0 < 3) hk6)

theorem GGSecFiveRouteCfg.three_pow_six_le_card_or_center_eq_bot_of_twA5_member
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hTB : GGTBFixInput) (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) (hBB : B = Bs) {X : Subgroup G} (hX : X ∈ 𝒦)
    (hlab : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ lab.rank = 5 ∧ lab.n = 1) 3 Bs X)
    (h720 : Nat.card ↥(ggAutomizer X Bs) = 720) :
    3 ^ 6 ≤ Nat.card ↥Bs ∨ Subgroup.center ↥X = ⊥ := by
  by_cases hAD : GGIsWeylMatrixA M ∨ NSJoin.NSTypeD M
  · exact Or.inl (three_pow_six_le_card_of_nbr_card_automizer hTB hcfg hpres hAD
      (GGSecFiveWeakNbr.of_mem hcfg hX) h720)
  rw [not_or] at hAD
  have hBs : IsElemAbelian 3 Bs := ggRouteCfg_isElemAbelian hcfg
  rcases GGIsWeylMatrixE.of_not_typeA_not_typeD hpres.1 hle3 hAD.1 hAD.2 with
    ⟨σ, hM⟩ | ⟨σ, hM⟩ | ⟨σ, hM⟩
  · exact card_or_center_of_typeE6 hcfg hpres hBB hX hlab hM
  · have hW7 : GGWeylOfType 3 CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h7 : 3 ^ 7 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) hBs hW7 FrameRoute.exists_elemAbelian_two_coxeterE7
    exact Or.inl (le_trans (by norm_num) h7)
  · have hW8 : GGWeylOfType 3 CoxeterMatrix.E₈ (ggAutomizerJoin L Bs 𝒦) := by
      subst hM
      exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
    have h8 : 3 ^ 8 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
      Nat.prime_three (by norm_num) hBs hW8 FrameRoute.exists_elemAbelian_two_coxeterE8
    exact Or.inl (le_trans (by norm_num) h8)

end CFSG.StandardType

end
