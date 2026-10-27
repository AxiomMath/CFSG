module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC163Four
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_perfect_cover_of_factors (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    {n : ℕ} (N : Fin n → Subgroup (MulAut (Vtil V₀ V hV)))
    (hNM : ∀ j, N j ≤ Mbar D.M V₀ V hV)
    (hNS : ∀ j, IsSimpleGroup ↥(N j))
    (hNZ : ∀ j, Subgroup.center ↥(N j) = ⊥)
    (hN3 : ∀ j, 3 ∣ Nat.card ↥(N j))
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ Group.IsPerfect ↥Y ∧
      ∃ f : ↥Y →* MulAut (Vtil V₀ V hV),
        f.range = (⨆ j, N j) ∧
        CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ ∧
        Group.IsSolvable f.ker ∧ CFSG.pCore 2 ↥Y ≤ f.ker := by
  classical
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  have hNor := s15_Three_cTilde_normal (D := D) hV hMs
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
    have := hTS j
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
  obtain ⟨hYX, hYperfField, hO2E, -, hYC, hYbar⟩ := hY
  have hYM : Y ≤ D.M := hYX.trans hXpM
  set f0 : ↥Y →* F11.MBar11 D.M V₀ V :=
    (QuotientGroup.mk' ((F11.CTilde D.M V₀ V).subgroupOf D.M)).comp
      (Subgroup.inclusion hYM) with hf0
  have hf0range : f0.range = X := by
    rw [← hbarXp, ← hYbar, hf0, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hf0ker : ∀ y : ↥Y, y ∈ f0.ker ↔ (y : G) ∈ F11.CTilde D.M V₀ V := by
    intro y
    rw [MonoidHom.mem_ker, hf0, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hlayer : CFSG.layer (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊤ := by
    rw [P22y.layer_eq_rankThreeLayer_top]
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
  have hsolv0 : Group.IsSolvable ↥f0.ker := by
    have hle : f0.ker.map Y.subtype ≤ OInf Y := by
      rintro _ ⟨y, hy, rfl⟩
      exact hYC ⟨y.2, (hf0ker y).1 hy⟩
    have := uc22p20a_isSolvable_oinf Y
    exact solvable_of_solvable_injective (f := (Subgroup.inclusion hle).comp
      (f0.ker.equivMapOfInjective Y.subtype Y.subtype_injective).toMonoidHom)
      ((Subgroup.inclusion_injective hle).comp (MulEquiv.injective _))
  have hR0 : CFSG.pCore 2 ↥Y ≤ f0.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfr : f0.range = ⨆ k, T k := hf0range.trans hX
    refine P22y.eq_bot_of_isPGroup_two hTcomm' hTind hTS hT3 hTZ
      (CFSG.pCore_isPGroup.map f0) ?_ ?_
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
  have hYperf : Group.IsPerfect ↥Y := by
    apply Subgroup.isPerfect_iff.mpr
    exact hYperfField
  set f : ↥Y →* MulAut (Vtil V₀ V hV) :=
    (Subgroup.subtype (Mbar D.M V₀ V hV)).comp (e.toMonoidHom.comp f0) with hf
  have hfker : f.ker = f0.ker := by
    rw [hf, MonoidHom.ker_comp_of_injective (e.toMonoidHom.comp f0)
      (Subgroup.subtype (Mbar D.M V₀ V hV))
      (Mbar D.M V₀ V hV).subtype_injective,
      MonoidHom.ker_comp_of_injective f0 e.toMonoidHom e.injective]
  have hsolv : Group.IsSolvable ↥f.ker := by
    rw [hfker]
    exact hsolv0
  have hR : CFSG.pCore 2 ↥Y ≤ f.ker := by
    rw [hfker]
    exact hR0
  have hbarYle : barSub V₀ V hV Y ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV hYM
  have hXe : X.map e.toMonoidHom = (barSub V₀ V hV Y).subgroupOf
      (Mbar D.M V₀ V hV) := by
    rw [← hbarXp, ← hYbar]
    exact he Y hYM
  have hbarY : barSub V₀ V hV Y = ⨆ j, N j := by
    calc barSub V₀ V hV Y
        = ((barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV)).map
            (Subgroup.subtype (Mbar D.M V₀ V hV)) :=
          (Subgroup.map_subgroupOf_eq_of_le hbarYle).symm
      _ = (X.map e.toMonoidHom).map (Subgroup.subtype (Mbar D.M V₀ V hV)) := by
          rw [hXe]
      _ = ((⨆ j, T j).map e.toMonoidHom).map
            (Subgroup.subtype (Mbar D.M V₀ V hV)) := by rw [hX]
      _ = (⨆ j, (T j).map e.toMonoidHom).map
            (Subgroup.subtype (Mbar D.M V₀ V hV)) := by rw [Subgroup.map_iSup]
      _ = (⨆ j, (N j).subgroupOf (Mbar D.M V₀ V hV)).map
            (Subgroup.subtype (Mbar D.M V₀ V hV)) := by
          congr 1
          apply iSup_congr
          intro j
          rw [hT, Subgroup.map_map]
          have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
            ext x; simp
          rw [hcomp, Subgroup.map_id]
      _ = ⨆ j, ((N j).subgroupOf (Mbar D.M V₀ V hV)).map
            (Subgroup.subtype (Mbar D.M V₀ V hV)) := by rw [Subgroup.map_iSup]
      _ = ⨆ j, N j := by
          apply iSup_congr
          intro j
          exact Subgroup.map_subgroupOf_eq_of_le (hNM j)
  have hfrange : f.range = ⨆ j, N j := by
    rw [hf, MonoidHom.range_comp, MonoidHom.range_comp, hf0range]
    rw [hXe, Subgroup.map_subgroupOf_eq_of_le hbarYle]
    exact hbarY
  exact ⟨Y, hYM, hYperf, f, hfrange, hlayer, hsolv, hR⟩

theorem le_pRank_of_factors (D : Data G) (h127 : R127 D) (h119 : F11.R119 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (N : Fin n → Subgroup (MulAut (Vtil V₀ V hV)))
    (hNM : ∀ j, N j ≤ Mbar D.M V₀ V hV) (hNS : ∀ j, IsSimpleGroup ↥(N j))
    (hNZ : ∀ j, Subgroup.center ↥(N j) = ⊥) (hN3 : ∀ j, 3 ∣ Nat.card ↥(N j))
    (hNp : ∀ j, p ∣ Nat.card ↥(N j))
    (hNcomm : ∀ j l, j ≠ l → ∀ x ∈ N j, ∀ y ∈ N l, x * y = y * x) :
    n ≤ CFSG.Open.pRank p D.M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Y, hYM, -, f, hfrange, hlayer, hsolv, hR⟩ :=
    exists_perfect_cover_of_factors D h127 h119 h hV N hNM hNS hNZ hN3 hNcomm
  have hNq : ∀ j, CFSG.Open.IsQuasisimple ↥(N j) := fun j => by
    have := hNS j
    exact P22y.isQuasisimple_of_isSimpleGroup (hNZ j)
  have hNperf : ∀ j, ⁅N j, N j⁆ = N j := by
    intro j
    have h1 := (hNq j).1
    have h2 : (_root_.commutator ↥(N j)).map (N j).subtype = ⁅N j, N j⁆ := by
      rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    rw [← h2, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hNind : iSupIndep N := fun j =>
    CFSG.ComponentClassification.CenterlessCommutingFamily.disjoint_of_centralizes (N j) _
      (hNZ j) (iSup₂_le fun l hl y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
        hNcomm j l (Ne.symm hl) x hx y hy)
  have hs : ∀ j, ∃ s ∈ N j, orderOf s = p := by
    intro j
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' p (hNp j)
    exact ⟨a, a.2, by rw [Subgroup.orderOf_coe, ha]⟩
  choose s hsT hsp using hs
  have h4 := le_pRank_of_layer hp hp2 f hlayer hsolv hR N
    (fun j => hfrange ▸ le_iSup N j) hNperf hNcomm hNind s hsT hsp
  have h5 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) Y
  have h6 := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt hYM
  omega

theorem seven_mem_sig (D : Data G) (hSg : UC6S846.SigmaStd D) (h127 : R127 D)
    (h119 : F11.R119 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V)
    {K : Subgroup (MulAut (Vtil V₀ V hV))} (hK : IsComponentOf K (Mbar D.M V₀ V hV))
    (hK8 : UC22.IsL2 ↥K 3) {g φ : MulAut (Vtil V₀ V hV)} (hg : g ∈ Mbar D.M V₀ V hV)
    (hφ : φ ∈ Mbar D.M V₀ V hV) (hKg : K ≠ K.map (MulAut.conj g).toMonoidHom)
    (hcomm : ⁅K ⊔ K.map (MulAut.conj g).toMonoidHom,
      (K ⊔ K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj φ).toMonoidHom⁆ = ⊥) :
    7 ∈ D.sig := by
  obtain ⟨N, hNM, hNS, hNZ, hN3, hN7, hNcomm⟩ := exists_four_factors hK hK8 hg hφ hKg hcomm
  exact hSg.four_mem 7 Nat.prime_seven (by norm_num)
    (le_pRank_of_factors D h127 h119 h hV Nat.prime_seven (by norm_num) N hNM hNS hNZ hN3 hN7
      hNcomm)

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
