module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RLiftAbs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem subgroupOf_iSup {A : Type*} [Group A] {S : Subgroup A} {ι : Sort*}
    (H : ι → Subgroup A) (hH : ∀ i, H i ≤ S) :
    (⨆ i, H i).subgroupOf S = ⨆ i, (H i).subgroupOf S := by
  apply Subgroup.map_injective (Subgroup.subtype_injective S)
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_iSup]
  rw [show (⨆ i, map S.subtype ((H i).subgroupOf S)) = ⨆ i, H i by
    apply iSup_congr
    intro i
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hH i)]]
  exact inf_eq_left.2 (iSup_le hH)

theorem exists_Y_of_factors (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) {n : ℕ}
    (N : Fin n → Subgroup (MulAut (Vtil V₀ V hV)))
    (hNM : ∀ j, N j ≤ Mbar D.M V₀ V hV) (hNS : ∀ j, IsSimpleGroup ↥(N j))
    (hNZ : ∀ j, Subgroup.center ↥(N j) = ⊥) (hN3 : ∀ j, 3 ∣ Nat.card ↥(N j))
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x)
    (hnorm : Mbar D.M V₀ V hV ≤
      normalizer ((⨆ j, N j : Subgroup (MulAut (Vtil V₀ V hV))) : Set (MulAut (Vtil V₀ V hV)))) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ D.M ≤ normalizer (Y : Set G) ∧ ⁅Y, Y⁆ = Y ∧
      rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊤ ∧
      Group.IsSolvable ↥(Y ⊓ F11.CTilde D.M V₀ V) ∧
      (∀ y ∈ CFSG.pCore 2 ↥Y, (y : G) ∈ F11.CTilde D.M V₀ V) ∧
      barSub V₀ V hV Y = ⨆ j, N j := by
  classical
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  haveI hNor := s15_Three_cTilde_normal (D := D) hV hMs
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) hV hMs
  set T : Fin n → Subgroup (F11.MBar11 D.M V₀ V) :=
    fun j => ((N j).subgroupOf (Mbar D.M V₀ V hV)).map e.symm.toMonoidHom with hT
  have hTe : ∀ j, Nonempty (↥(T j) ≃* ↥(N j)) := fun j =>
    ⟨(((N j).subgroupOf (Mbar D.M V₀ V hV)).equivMapOfInjective e.symm.toMonoidHom
      e.symm.injective).symm.trans (Subgroup.subgroupOfEquivOfLe (hNM j))⟩
  have hTS : ∀ j, IsSimpleGroup ↥(T j) := fun j =>
    (hTe j).some.isSimpleGroup_congr.mpr (hNS j)
  have hTZ : ∀ j, Subgroup.center ↥(T j) = ⊥ := fun j => by
    rw [← Subgroup.map_center_eq (hTe j).some.symm, hNZ j, Subgroup.map_bot]
  have hTcard : ∀ j, Nat.card ↥(T j) = Nat.card ↥(N j) := fun j =>
    Nat.card_congr (hTe j).some.toEquiv
  have hT3 : ∀ j, 3 ∣ Nat.card ↥(T j) := fun j => (hTcard j) ▸ hN3 j
  have hTq : ∀ j, CFSG.Open.IsQuasisimple ↥(T j) := fun j => by
    haveI := hTS j
    exact P22y.isQuasisimple_of_isSimpleGroup (hTZ j)
  have hTcomm : ∀ k l, k ≠ l → ∀ x ∈ T k, ∀ y ∈ T l, x * y = y * x := by
    rintro k l hkl _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hNcomm k l hkl _ ha _ hb)
  have hTcomm' : Pairwise fun k l => ∀ x y, x ∈ T k → y ∈ T l → Commute x y :=
    fun k l hkl x y hx hy => hTcomm k l hkl x hx y hy
  have hTind : iSupIndep T := fun j =>
    CFSG.ComponentClassification.CenterlessCommutingFamily.disjoint_of_centralizes (T j) _
      (hTZ j) (iSup₂_le fun l hl y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
        hTcomm j l (Ne.symm hl) x hx y hy)
  set X : Subgroup (F11.MBar11 D.M V₀ V) := ⨆ k, T k with hX
  have hXlayer : rankThreeLayer X = X := P22y.rankThreeLayer_iSup_of_comm hTq hTcomm
  set Xp : Subgroup G := F11.barPreimage11 D.M V₀ V X with hXp
  have hXpM : Xp ≤ D.M := Subgroup.map_subtype_le _
  have hCX : F11.CTilde D.M V₀ V ≤ Xp := by
    intro x hx
    have hxM : x ∈ D.M := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx 1) V.one_mem).1
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    show QuotientGroup.mk' _ ⟨x, hxM⟩ ∈ X
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact X.one_mem
  have hbarXp : F11.barImage11 D.M V₀ V Xp = X := by
    unfold F11.barImage11
    rw [hXp]
    unfold F11.barPreimage11
    have h1 : ((X.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M))).map
        D.M.subtype).subgroupOf D.M =
          X.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) :=
      Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X
  obtain ⟨Y, hY, -⟩ := h119 V₀ V (Hyp125.hyp11 h127 h) Xp hCX hXpM
    (by rw [hbarXp]; exact hXlayer)
  obtain ⟨hYX, hYperf, hO2E, hYn, hYC, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  set f : ↥Y →* F11.MBar11 D.M V₀ V :=
    (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp
      (Subgroup.inclusion hYM) with hf
  have hfrange : f.range = X := by
    rw [← hbarXp, ← hYbar, hf, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hfker : ∀ y : ↥Y, y ∈ f.ker ↔ (y : G) ∈ F11.CTilde D.M V₀ V := by
    intro y
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hlayer : rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) = ⊤ := by
    set L := rankThreeLayer (⊤ : Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y)) with hL
    have h1 : (L.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))).map Y.subtype =
        (⊤ : Subgroup ↥Y).map Y.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hO2E
    have h2 := Subgroup.map_injective Y.subtype_injective h1
    have h3 := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)) L
    rw [h2, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h3
    exact h3.symm
  have hR : CFSG.pCore 2 ↥Y ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfr : f.range = ⨆ k, T k := hfrange.trans hX
    refine P22y.eq_bot_of_isPGroup_two hTcomm' hTind hTS hT3 hTZ (CFSG.pCore_isPGroup.map f)
      ?_ ?_
    · rw [← hfr]
      exact Subgroup.map_le_range _ _
    · rw [← hfr]
      rintro _ ⟨y, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · rintro ⟨r, hr, rfl⟩
        exact ⟨y * r * y⁻¹, (CFSG.pCore_normal).conj_mem r hr y, by simp [map_mul, map_inv]⟩
      · rintro ⟨r, hr, hrz⟩
        refine ⟨y⁻¹ * r * y, ?_, ?_⟩
        · have := (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem r hr y⁻¹
          simpa using this
        · rw [map_mul, map_mul, map_inv, hrz]
          group
  have hR' : ∀ y ∈ CFSG.pCore 2 ↥Y, (y : G) ∈ F11.CTilde D.M V₀ V :=
    fun y hy => (hfker y).1 (hR hy)
  have hsol : Group.IsSolvable ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
    haveI := uc22p20a_isSolvable_oinf Y
    exact solvable_of_solvable_injective (f := Subgroup.inclusion hYC)
      (Subgroup.inclusion_injective hYC)
  set Nall : Subgroup (MulAut (Vtil V₀ V hV)) := ⨆ j, N j with hNall
  have hNallN : (Nall.subgroupOf (Mbar D.M V₀ V hV)).Normal := by
    rw [hNall]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (iSup_le hNM)).2 hnorm
  have hXmap : X.map e.toMonoidHom = Nall.subgroupOf (Mbar D.M V₀ V hV) := by
    rw [hX, hNall, Subgroup.map_iSup, subgroupOf_iSup N hNM]
    apply iSup_congr
    intro k
    rw [hT, Subgroup.map_map,
      show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ from by ext x; simp,
      Subgroup.map_id]
  have hXN : X.Normal := by
    have hXeq : X = (Nall.subgroupOf (Mbar D.M V₀ V hV)).comap e.toMonoidHom := by
      rw [← hXmap]
      exact (Subgroup.comap_map_eq_self_of_injective e.injective X).symm
    rw [hXeq]
    exact hNallN.comap e.toMonoidHom
  have hXpN : (Xp.subgroupOf D.M).Normal := by
    have h1 : Xp.subgroupOf D.M =
        X.comap (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)) := by
      rw [hXp]
      unfold F11.barPreimage11
      exact Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
    rw [h1]
    exact hXN.comap (QuotientGroup.mk' _)
  have hDM_nXp : D.M ≤ normalizer (Xp : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXpM).1 hXpN
  have hcov : Y ⊔ F11.CTilde D.M V₀ V = Xp := by
    refine le_antisymm (sup_le hYX hCX) ?_
    intro x hx
    have hxM : x ∈ D.M := hXpM hx
    have hxY : QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M) ⟨x, hxM⟩ ∈
        F11.barImage11 D.M V₀ V Y := by
      rw [hYbar]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx)
    rw [F11.barImage11, Subgroup.mem_map] at hxY
    obtain ⟨y, hy, hyx⟩ := hxY
    have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.1 hy
    have hmemC : ((y⁻¹ * ⟨x, hxM⟩ : ↥D.M) : G) ∈ F11.CTilde D.M V₀ V :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (by simpa using hyx))
    have hx_eq : x = (y : G) * ((y⁻¹ * ⟨x, hxM⟩ : ↥D.M) : G) := by
      rw [show ((y⁻¹ * ⟨x, hxM⟩ : ↥D.M) : G) = (y : G)⁻¹ * x from rfl]
      group
    rw [hx_eq]
    exact Subgroup.mul_mem_sup hyY hmemC
  have hCM : F11.CTilde D.M V₀ V ≤ D.M := fun x hx =>
    (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx 1) V.one_mem).1
  have hDM_nC : D.M ≤ normalizer (F11.CTilde D.M V₀ V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCM).1 hNor
  have hYnorm : D.M ≤ normalizer (Y : Set G) := by
    intro g hg
    exact le_normalizer_of_perfect_cover hYX hCX hYn (hXpM.trans hDM_nC) hYperf hcov hsol
      (hDM_nXp hg) (hDM_nC hg)
  have hbarY : barSub V₀ V hV Y = Nall := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        Nall.subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hYM, hYbar, hbarXp, hXmap]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [hNall] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hYM),
      inf_eq_left.2 (iSup_le hNM)] at h2
    exact h2
  exact ⟨Y, hYM, hYnorm, hYperf, hlayer, hsol, hR', by simpa only [hNall] using hbarY⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
