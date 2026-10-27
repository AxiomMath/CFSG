module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4CA1BC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoSwapPair
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_exists_conj_of_mem_mbar {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {φ : MulAut (Vtil V₀ V hV)}
    (hφ : φ ∈ Mbar D.M V₀ V hV) :
    ∃ m : G, m ∈ D.M ∧ barSub V₀ V hV (conjSubgroup L m) =
      (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom := by
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
  have hgm : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil _ _).inv_mem g.2
  have hgt : actTil V₀ V hV ⟨(g : G)⁻¹, hgm⟩ = (actTil V₀ V hV g)⁻¹ := by
    rw [show (⟨(g : G)⁻¹, hgm⟩ : stabTil V₀ V) = ⟨g, g.2⟩⁻¹ from rfl, map_inv]
  refine ⟨(g : G)⁻¹, D.M.inv_mem hgM, ?_⟩
  rw [← hgφ, s15_Infra_barSub_conjSubgroup V₀ V hV hgm L]
  congr 1
  rw [hgt, inv_inv]

theorem s16h_sl4_exists_x (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) :
    ∃ L' : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)),
      L' ≠ lBar ⊥ V h.hyp151.isElemAbelian L ∧
      s16h_SL4TwoFrame (Mbar D.M ⊥ V h.hyp151.isElemAbelian)
        (lBar ⊥ V h.hyp151.isElemAbelian L) L'
        (barSub ⊥ V h.hyp151.isElemAbelian D.T) ∧
      ∃ x : G, x ∈ D.M ∧ x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L ∧
        lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) = L' := by
  obtain ⟨L', hne, F⟩ := s16h_sl4_two_frame_of_setting D h hs2
  obtain ⟨t, htT, htL⟩ := F.swap
  obtain ⟨m, hmM, hm⟩ :=
    s16h_sl4_exists_conj_of_mem_mbar h.hyp151 h.hyp151.isElemAbelian (L := L)
      (F.t_le htT)
  have hmL : lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L m) = L' := by
    change barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L m) = L'
    rw [hm]
    exact htL
  refine ⟨L', hne, F, m, hmM, fun hmn => hne ?_, hmL⟩
  rw [s15_Infra_mem_nBar_iff h.hyp151.hyp125 h.hyp151.isElemAbelian hmM] at hmn
  rw [← hmL]
  exact hmn

theorem s16h_sl4_wTil_inf_conj_of_hZ0 (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) =
      commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have h1 : preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓
        commSub ⊤ (lBar ⊥ V hV (conjSubgroup L x))) =
      preTil ⊥ V hV (commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)) := by
    rw [s16c167_twenty_two_preTil_inf, ← s16h_wSub_inf_centralizer_eq_preTil D h, ← hZ0,
      ← s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs hxM)]
    rfl
  have h2 := congrArg (imgTil ⊥ V hV) h1
  rwa [imgTil_preTil, imgTil_preTil] at h2

theorem s16h_sl4_lift_fixed (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {w : Vtil ⊥ V h.hyp151.isElemAbelian}
    (hwT : w ∈ fixV (barSub ⊥ V h.hyp151.isElemAbelian D.T))
    (hwZ : w ∉ commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) :
    ∃ v : G, v ∈ V ∧ v ∈ Subgroup.centralizer (D.T : Set G) ∧
      v ∉ wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTM : D.T ≤ D.M := D.sylowM.le
  obtain ⟨xq, hxq⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
  have hvV : IntMod.val xq ∈ V := xq.val_mem
  have hmk : mkTil ⊥ V hV (IntMod.mk hV ⟨IntMod.val xq, hvV⟩) = w := by
    rw [← hxq]
    exact congrArg _ (IntMod.val_injective rfl)
  refine ⟨IntMod.val xq, hvV, ?_, ?_⟩
  · have h1 : IntMod.val xq ∈ preTil ⊥ V hV (fixV (barSub ⊥ V hV D.T)) := by
      rw [mem_preTil_iff_of_mem ⊥ V hV _ hvV, hmk]
      exact hwT
    rw [s15_Glue_mem_preTil_fixV_iff ⊥ V D.T hV (hTM.trans hMs) hvV] at h1
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h2 := Subgroup.mem_bot.1 (h1 e he)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2
  · rw [s16h_wSub_inf_centralizer_eq_preTil D h, mem_preTil_iff_of_mem ⊥ V hV _ hvV, hmk]
    exact hwZ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
