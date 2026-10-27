module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6Outer
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinE6Rank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6


theorem finE6Two27_holds : FinE6Two27 := by
  classical
  intro W _ _ hW Y L g hctx hgY hg2 hlie hcard
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hperf : Group.IsPerfect ↥L := hq.1
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  haveI : Nontrivial ↥L := by
    haveI := hq.2.1
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  have hLbot : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance
  have hirr' : X1.IsIrrOn L := by
    refine ⟨?_, fun U hU => hirr.2.2.2 U hU bot_le le_top⟩
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI := hnt
    exact (ne_of_lt hirr.1) (Subgroup.ext fun x => by simp [Subsingleton.elim x 1])
  obtain ⟨K, _, _, _, hK, ⟨eS'⟩⟩ := exists_adjointEquiv_of_lieModel hlie
  obtain ⟨D, hDf⟩ := exists_hatData_of_adjointEquiv hK hperf eS'
  obtain ⟨δ, m, k, _, _, _, c, hδ, hm1, hkc, hWc, hρirr, hinj⟩ :=
    exists_moduleCoordinates hW' hperf hLbot hirr'
  obtain ⟨ιK⟩ := nonempty_ringHom_of_card_two (k := k) hK
  letI : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep c.rep := (SL2Modules.isIrreducible_iff c.rep).1 hρirr
  have hρ' : IsSimpleRep (c.rep.comp D.π) := simpleRep_comp D.π D.hπs hρ
  have hnt : ∃ (x : ↥(e6Data_valid.minGroup K)) (v : Fin m → k), (c.rep.comp D.π) x v ≠ v := by
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥L)
    obtain ⟨x, rfl⟩ := D.hπs s
    refine ⟨x, ?_⟩
    by_contra hcon'
    push Not at hcon'
    apply hs
    apply hinj
    rw [map_one]
    exact LinearMap.ext fun v => hcon' v
  have hδm : δ * m = 27 := Nat.pow_right_injective (le_refl 2) (hWc.symm.trans hcard)
  have hm27 : m ≤ 27 := by nlinarith
  obtain ⟨hm, hty⟩ := isE6TwentySevenType_of_isSimpleRep hK (c.rep.comp D.π) hρ' hnt hm27
  have hδ1 : δ = 1 := by subst hm; omega
  have hk2 : Nat.card k = 2 := by rw [hkc, hδ1]; norm_num
  have hgN := mem_normalizer_of_isContext hctx hgY
  have hg2' : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg2, sq] at this
  obtain ⟨B, hBu, hBρ⟩ := exists_intertwiner_of_card_eq_two c hk2 hgN
  have hgL : g ∈ L :=
    mem_of_normalizer_of_isE6TwentySevenType hW' hperf hirr' hK eS' D hDf hρ hty hgN hg2' B hBu
      hBρ
  have hfix := natCard_fixV_zpowers_le D c hk2 hρ hty hgL hg2
  exact le_trans (by norm_num) (six_le_mQuot_of_card_fixV_le hcard hfix)

end CFSG.LocalAnalysis.WeakClosure81
