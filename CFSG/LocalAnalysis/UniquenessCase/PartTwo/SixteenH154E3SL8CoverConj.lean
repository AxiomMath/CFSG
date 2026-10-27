module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaE
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.B15P4

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_cover_ncard_conjSetOf (D : Data G) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {L₀ : Subgroup G} (hL₀ : L₀ ∈ calC D.M)
    (h₀ : barSub ⊥ V h.hyp151.isElemAbelian L₀ =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    (conjSetOf D.M L₀).ncard = 2 := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hna : ⁅lBar ⊥ V hV L, lBar ⊥ V hV L⁆ ≠ ⊥ := by
    rw [perfect_of_isComponentOf hcomp]
    exact ne_bot_of_isComponentOf hcomp
  have hnaLbx : ⁅barSub ⊥ V hV (conjSubgroup L x),
      barSub ⊥ V hV (conjSubgroup L x)⁆ ≠ ⊥ := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L, ← Subgroup.map_commutator]
    change (⁅lBar ⊥ V hV L, lBar ⊥ V hV L⁆).map _ ≠ ⊥
    rw [perfect_of_isComponentOf hcomp]
    intro hbot
    exact ne_bot_of_isComponentOf hcomp
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).1 hbot)
  have hbar : ∀ m ∈ D.M, barSub ⊥ V hV (conjSubgroup L₀ m) = lBar ⊥ V hV L ∨
      barSub ⊥ V hV (conjSubgroup L₀ m) = barSub ⊥ V hV (conjSubgroup L x) := by
    intro m hm
    have h' : barSub ⊥ V hV (conjSubgroup L₀ m) =
        barSub ⊥ V hV (conjSubgroup (conjSubgroup L x) m) := by
      rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hm) L₀,
        s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hm) (conjSubgroup L x), h₀]
    rw [h', conjSubgroup_conjSubgroup]
    exact c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn (D.M.mul_mem hxM hm)
  have hxi : x⁻¹ ∈ D.M := D.M.inv_mem hxM
  have hK : conjSubgroup L₀ x⁻¹ ∈ calC D.M :=
    uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hL₀ hxi
  have hKbar : barSub ⊥ V hV (conjSubgroup L₀ x⁻¹) = lBar ⊥ V hV L := by
    have h' : barSub ⊥ V hV (conjSubgroup L₀ x⁻¹) =
        barSub ⊥ V hV (conjSubgroup (conjSubgroup L x) x⁻¹) := by
      rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxi) L₀,
        s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxi) (conjSubgroup L x), h₀]
    rw [h', conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rfl
  have hKne : conjSubgroup L₀ x⁻¹ ≠ L₀ := by
    intro hc
    refine hxn ((s15_Infra_mem_nBar_iff h125 hV hxM).2 ?_)
    rw [← h₀, ← hc, hKbar]
    rfl
  have hsub : conjSetOf D.M L₀ ⊆ {L₀, conjSubgroup L₀ x⁻¹} := by
    rintro _ ⟨g, hg, rfl⟩
    have hgi : g⁻¹ ∈ D.M := D.M.inv_mem hg
    have heq : L₀.map (MulAut.conj g).toMonoidHom = conjSubgroup L₀ g⁻¹ := by
      rw [conjSubgroup, inv_inv]
    rw [heq]
    have hcal : conjSubgroup L₀ g⁻¹ ∈ calC D.M :=
      uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hL₀ hgi
    rcases hbar g⁻¹ hgi with hb | hb
    · refine Or.inr (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal hK (hb.trans hKbar.symm) ?_)
      rw [hb]; exact hna
    · refine Or.inl (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal hL₀ (hb.trans h₀.symm) ?_)
      rw [hb]; exact hnaLbx
  have hKmem : conjSubgroup L₀ x⁻¹ ∈ conjSetOf D.M L₀ :=
    ⟨x, hxM, by rw [conjSubgroup, inv_inv]⟩
  have hset : conjSetOf D.M L₀ = {L₀, conjSubgroup L₀ x⁻¹} :=
    Set.Subset.antisymm hsub (Set.insert_subset_iff.2
      ⟨PartOne.Section8.mem_conjSetOf_self D.M L₀, Set.singleton_subset_iff.2 hKmem⟩)
  rw [hset, Set.ncard_pair hKne.symm]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
