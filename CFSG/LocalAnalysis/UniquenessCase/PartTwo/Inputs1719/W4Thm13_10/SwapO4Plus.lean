module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.SwapLemmas
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4PlusUnique

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem exists_o4Plus_of_swapping {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y)
    (haL : IsAlt ↥L 5) (haK : IsAlt ↥K 5) (hne : L ≠ K)
    (hXn : ((L ⊔ K).subgroupOf Y).Normal)
    (hsw : ∃ g ∈ Y, K = L.map (MulAut.conj g).toMonoidHom) {t : MulAut W}
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (htL : L.map (MulAut.conj t).toMonoidHom = K) :
    ∃ R : Subgroup (MulAut W), R ≤ Y ∧ IsDirSumOver (conjSet R Y) commV ∧
      CFSG.Open.IsSubnormal L R ∧ IsNaturalO4Plus R 2 ∧ conjSet R Y = {R} := by
  classical
  have hd4 : dMinDeg ↥L = 4 := dMinDeg_eq_four_of_isAlt_five haL
  have hQL : QuadTrivial L := quadTrivial_of_commutator_eq_top hcL.2.2.1
  have hQK : QuadTrivial K := quadTrivial_of_commutator_eq_top hcK.2.2.1
  have hL1 : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (CFSG.LocalCores.isQuasisimple_nontrivial
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hcL.2.2))
  have ht1 : t * t = 1 := by
    have h : t ^ 2 = 1 := ht2 ▸ pow_orderOf_eq_one t
    simpa [pow_two] using h
  have hswap : commSub (commSub (⊤ : Subgroup W) L) K ≠ ⊥ := by
    have h := commSub_commSub_ne_bot_of_swap hW hQL hL1 ht1 (by omega)
    rwa [htL] at h
  let H : Subgroup (MulAut W) := ⨆ X ∈ conjSet L Y, X
  have hH : H = ⨆ X ∈ conjSet L Y, X := rfl
  have hHK : H = L ⊔ K := by
    rw [hH, iSup_conjSet_eq_biSup_conj]
    exact iSup_conj_eq_of_swap hcL hcK haL haK hne rfl hXn hsw
  rcases w4Lem12_8_holds W hW Y hO2 hB L hcL H hH with
    h1 | ⟨hsum, -⟩ | ⟨R, e, hRY, hsumR, hLR, hnatR, hme, hde⟩
  ·
    exfalso
    have h2 := Asc81c.Pf.mParam_le_of_orderOf_two htY ht2
    omega
  ·
    exfalso
    set C : Subgroup W := fixV H with hC
    obtain ⟨-, -, -, hn, -, -⟩ := h_facts hcL hH
    have hYle : Y ≤ stabSub C := by
      rw [hC]
      exact le_stabSub_fixV hn
    have hLmem : L ∈ conjSet L Y := ⟨1, Y.one_mem, (Asc81c.Pf.map_conj_one L).symm⟩
    have hKmem : K ∈ conjSet L Y := by
      obtain ⟨g, hg, hgK⟩ := hsw
      exact ⟨g, hg, hgK⟩
    have hdisj : Disjoint (commV (autQuot L C)) (commV (autQuot K C)) :=
      hsum.1.pairwiseDisjoint (i := ⟨L, hLmem⟩) (j := ⟨K, hKmem⟩)
        (fun h => hne (congrArg Subtype.val h))
    have hLstab : L ≤ stabSub C := hcL.1.trans hYle
    have hKstab : K ≤ stabSub C := hcK.1.trans hYle
    have hcommKL : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l :=
      fun l hl k hk => (B69.components_mul_comm_of_ne hcL hcK hne k hk l hl).symm
    have hDL : commSub (commSub (⊤ : Subgroup W) L) K ≤ commSub (⊤ : Subgroup W) L := by
      refine commSub_le_of_invariant ?_
      intro k hk w hw
      rw [← commV_eq_commSub] at hw ⊢
      exact B69.commV_invariant_of_commute (fun l hl => (hcommKL l hl k hk).symm) w hw
    have hDK : commSub (commSub (⊤ : Subgroup W) L) K ≤ commV K := by
      rw [commV_eq_commSub]
      exact commSub_mono le_top le_rfl
    have hmap : (commSub (commSub (⊤ : Subgroup W) L) K).map (QuotientGroup.mk' C) = ⊥ := by
      have h1 : (commSub (commSub (⊤ : Subgroup W) L) K).map (QuotientGroup.mk' C) ≤
          commV (autQuot L C) := by
        rw [commV_autQuot hLstab, commV_eq_commSub]
        exact Subgroup.map_mono hDL
      have h2 : (commSub (commSub (⊤ : Subgroup W) L) K).map (QuotientGroup.mk' C) ≤
          commV (autQuot K C) := by
        rw [commV_autQuot hKstab]
        exact Subgroup.map_mono hDK
      have hle : (commSub (commSub (⊤ : Subgroup W) L) K).map (QuotientGroup.mk' C) ≤
          commV (autQuot L C) ⊓ commV (autQuot K C) := le_inf h1 h2
      rw [disjoint_iff.mp hdisj] at hle
      exact le_bot_iff.mp hle
    have hDC : commSub (commSub (⊤ : Subgroup W) L) K ≤ C := by
      have h := (Subgroup.map_eq_bot_iff _).mp hmap
      rwa [QuotientGroup.ker_mk'] at h
    have hCfix : C ≤ fixV K := by
      rw [hC, hHK, Asc81c.Pf.fixV_sup]
      exact inf_le_right
    have hJstab : StableUnder K (commSub (⊤ : Subgroup W) L) := by
      refine stableUnder_commSub ?_ (fun x _ u _ => Subgroup.mem_top u)
      intro k hk l hl
      rw [show k * l * k⁻¹ = l from by
        rw [show k * l = l * k from (hcommKL l hl k hk).symm]
        group]
      exact hl
    have hbot : commSub (commSub (⊤ : Subgroup W) L) K = ⊥ :=
      hQK _ hJstab (hDC.trans hCfix)
    exact hswap hbot
  ·
    have he2 : e = 2 := by omega
    refine ⟨R, hRY, hsumR, hLR, ?_, ?_⟩
    · rwa [he2] at hnatR
    ·
      have hRmem : R ∈ conjSet R Y := ⟨1, Y.one_mem, (Asc81c.Pf.map_conj_one R).symm⟩
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hRmem, ?_⟩
      intro X hX
      obtain ⟨y, hy, rfl⟩ := hX
      by_contra hneX
      have hXmem : R.map (MulAut.conj y).toMonoidHom ∈ conjSet R Y := ⟨y, hy, rfl⟩
      have hLyle : L.map (MulAut.conj y).toMonoidHom ≤ R.map (MulAut.conj y).toMonoidHom :=
        Subgroup.map_mono hLR.le
      have hVLVR : commV L ≤ commV R := by
        rw [commV_eq_commSub L, commV_eq_commSub R]
        exact commSub_mono le_top hLR.le
      have happly : ∀ x ∈ R.map (MulAut.conj y).toMonoidHom, ∀ u ∈ commV R, x u = u := by
        intro x hx u hu
        exact Thm14_5.apply_eq_of_mem_commV hRY hsumR.1 hRmem hXmem (Ne.symm hneX) hx hu
      have hzero : commSub (commV L) (L.map (MulAut.conj y).toMonoidHom) = ⊥ := by
        rw [commSub_eq_bot_iff]
        intro u hu x hx
        exact happly x (hLyle hx) u (hVLVR hu)
      rcases map_conj_cases hcL hcK hne hXn hy with ⟨hLy, -⟩ | ⟨hLy, -⟩
      ·
        have hfix : commV L ≤ fixV L := by
          have h := commSub_eq_bot_iff.mp hzero
          rwa [hLy] at h
        have hbot : commSub (⊤ : Subgroup W) L = ⊥ := by
          refine hQL ⊤ (fun x _ u _ => Subgroup.mem_top u) ?_
          rw [← commV_eq_commSub]
          exact hfix
        have htop : fixV L = ⊤ := top_le_iff.mp (commSub_eq_bot_iff.mp hbot)
        have hLbot : L = ⊥ := by
          rw [eq_bot_iff]
          intro l hl
          rw [Subgroup.mem_bot]
          ext w
          have hw : w ∈ fixV L := by rw [htop]; exact Subgroup.mem_top w
          simpa using (mem_fixV.mp hw) l hl
        exact hL1 hLbot
      ·
        have hbot : commSub (commSub (⊤ : Subgroup W) L) K = ⊥ := by
          have h := hzero
          rw [commV_eq_commSub L, hLy] at h
          exact h
        exact hswap hbot

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10
