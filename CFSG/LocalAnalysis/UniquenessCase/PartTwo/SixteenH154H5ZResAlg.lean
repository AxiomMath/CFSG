module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.Quasithin.Background.SmithD310UCaseI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_L3_le_stabSub (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub ⊤ L) := by
  intro g hg
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => L.mul_mem (L.mul_mem hg hx) (L.inv_mem hg)
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => L.mul_mem (L.mul_mem (L.inv_mem hg) hx) (L.inv_mem (L.inv_mem hg))
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub ⊤ L := commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private noncomputable def s16h_L3_resHom (L : Subgroup (MulAut W)) :
    ↥L →* MulAut ↥(commSub ⊤ L) :=
  (resHom (commSub ⊤ L)).comp (Subgroup.inclusion (s16h_L3_le_stabSub L))

private theorem s16h_L3_resHom_apply (L : Subgroup (MulAut W)) (l : ↥L)
    (u : ↥(commSub ⊤ L)) :
    ((s16h_L3_resHom L l) u : W) = (l : MulAut W) u.1 := by
  simp [s16h_L3_resHom, resHom_apply]

private theorem s16h_L3_resHom_mem_autSub (L : Subgroup (MulAut W)) (l : ↥L) :
    s16h_L3_resHom L l ∈ autSub L (commSub ⊤ L) := by
  refine mem_autSub.mpr ⟨⟨(l : MulAut W), s16h_L3_le_stabSub L l.2⟩, l.2, rfl⟩

private theorem s16h_L3_resHom_range (L : Subgroup (MulAut W)) :
    (s16h_L3_resHom L).range = autSub L (commSub ⊤ L) := by
  ext ψ
  constructor
  · rintro ⟨l, rfl⟩
    exact s16h_L3_resHom_mem_autSub L l
  · intro hψ
    obtain ⟨g, hg, hgψ⟩ := mem_autSub.mp hψ
    refine ⟨⟨(g : MulAut W), hg⟩, ?_⟩
    rw [← hgψ]
    ext u
    rw [s16h_L3_resHom_apply, resHom_apply]

private theorem s16h_L3_mem_fixV_of_mem_fixV_autSub {L : Subgroup (MulAut W)}
    {v : ↥(commSub ⊤ L)} (hv : v ∈ fixV (autSub L (commSub ⊤ L))) :
    (v : W) ∈ fixV L := by
  rw [mem_fixV] at hv ⊢
  intro l hl
  have hmem : s16h_L3_resHom L ⟨l, hl⟩ ∈ autSub L (commSub ⊤ L) :=
    s16h_L3_resHom_mem_autSub L ⟨l, hl⟩
  have h := hv (s16h_L3_resHom L ⟨l, hl⟩) hmem
  simpa [s16h_L3_resHom_apply] using congrArg Subtype.val h

private theorem s16h_L3_resHom_injective {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hL3 : IsSLn ↥L 3 1) :
    Function.Injective (s16h_L3_resHom L) := by
  have hLq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  have hLn : IsL3 ↥L 1 := s16k_isLn_of_isSLn (by norm_num) hL3
  have hcenter : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isL3 hLn
  have hkne : (s16h_L3_resHom L).ker ≠ ⊤ := by
    intro htop
    have hfixU : ∀ (l : ↥L) (u : ↥(commSub ⊤ L)),
        (l : MulAut W) u.1 = u.1 := by
      intro l u
      have hmem : l ∈ (s16h_L3_resHom L).ker := by
        rw [htop]
        exact Subgroup.mem_top l
      rw [MonoidHom.mem_ker] at hmem
      have h := congrArg
        (fun f : MulAut ↥(commSub ⊤ L) => ((f u : ↥(commSub ⊤ L)) : W)) hmem
      simpa [s16h_L3_resHom_apply] using h
    have hUfix : commSub ⊤ L ≤ fixV L := by
      intro u hu
      rw [mem_fixV]
      intro l hl
      exact hfixU ⟨l, hl⟩ ⟨u, hu⟩
    have hcomm_bot : commSub (commSub ⊤ L) L = ⊥ := commSub_eq_bot_iff.mpr hUfix
    have hperfGroup : Group.IsPerfect ↥L := ⟨hLq.1⟩
    have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfGroup
    have h4 : commSub (commSub ⊤ L) L = commSub ⊤ L :=
      CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperf (⊤ : Subgroup W)
    have hUbot : commSub ⊤ L = ⊥ := by rw [← h4, hcomm_bot]
    have hWfix : (⊤ : Subgroup W) ≤ fixV L := commSub_eq_bot_iff.mp hUbot
    have hLbot : L = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      rw [Subgroup.mem_bot]
      ext w
      exact mem_fixV.mp (hWfix (Subgroup.mem_top w)) l hl
    haveI : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hLq.2.toNontrivial
    haveI hnt : Nontrivial ↥L :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot L).mp hnt hLbot
  have hker : (s16h_L3_resHom L).ker ≤ Subgroup.center ↥L :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hLq
      (s16h_L3_resHom L).ker hkne
  have hkerbot : (s16h_L3_resHom L).ker = ⊥ := le_bot_iff.mp (hcenter ▸ hker)
  exact (s16h_L3_resHom L).ker_eq_bot_iff.mp hkerbot

private theorem s16h_L3_isQuasisimple_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : CFSG.Open.IsQuasisimple H) : CFSG.Open.IsQuasisimple G := by
  obtain ⟨hperf, hsimple⟩ := h
  haveI : Group.IsPerfect H := ⟨hperf⟩
  haveI : Group.IsPerfect G :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  haveI : IsSimpleGroup (H ⧸ Subgroup.center H) := hsimple
  exact (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e
    (Subgroup.map_center_eq e)).isSimpleGroup

private noncomputable def s16h_L3_equiv {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hL3 : IsSLn ↥L 3 1) :
    ↥L ≃* ↥(autSub L (commSub ⊤ L)) :=
  (MonoidHom.ofInjective (s16h_L3_resHom_injective hc hL3)).trans
    (MulEquiv.subgroupCongr (s16h_L3_resHom_range L))

private theorem s16h_L3_res_elem {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    ∀ u : ↥(commSub ⊤ L), u * u = 1 := by
  intro u
  exact Subtype.ext (by simpa [pow_two] using hc.elem (u : W))

private theorem s16h_L3_res_le {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    autSub L (commSub ⊤ L) ≤
      autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L) :=
  autSub_mono (le_inf hc.comp.1 Subgroup.le_normalizer) _

private theorem s16h_L3_res_normal {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L) ≤
      Subgroup.normalizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) := by
  intro φ hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  constructor
  · intro hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hψ
    have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp hg).2
    have hgl : (g : MulAut W) * (l : MulAut W) * (g : MulAut W)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hgN l).mp hl
    refine mem_autSub.mpr
      ⟨⟨(g : MulAut W) * (l : MulAut W) * (g : MulAut W)⁻¹,
        s16h_L3_le_stabSub L hgl⟩, hgl, ?_⟩
    rw [show (⟨(g : MulAut W) * (l : MulAut W) * (g : MulAut W)⁻¹,
        s16h_L3_le_stabSub L hgl⟩ : ↥(stabSub (commSub ⊤ L))) = g * l * g⁻¹ from
      Subtype.ext rfl]
    simp only [map_mul, map_inv]
  · intro hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hφ
    obtain ⟨m, hm, hmψ⟩ := mem_autSub.mp hψ
    have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.mem_inf.mp hg).2
    have hgNinv : (g : MulAut W)⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hgN
    have hconj : (g : MulAut W)⁻¹ * (m : MulAut W) * (g : MulAut W) ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp hgNinv m).mp hm
      simpa using h
    refine mem_autSub.mpr
      ⟨⟨(g : MulAut W)⁻¹ * (m : MulAut W) * (g : MulAut W),
        s16h_L3_le_stabSub L hconj⟩, hconj, ?_⟩
    have hmap : resHom (commSub ⊤ L)
        ⟨(g : MulAut W)⁻¹ * (m : MulAut W) * (g : MulAut W),
          s16h_L3_le_stabSub L hconj⟩ =
        (resHom (commSub ⊤ L) g)⁻¹ * resHom (commSub ⊤ L) m *
          resHom (commSub ⊤ L) g := by
      rw [show (⟨(g : MulAut W)⁻¹ * (m : MulAut W) * (g : MulAut W),
          s16h_L3_le_stabSub L hconj⟩ : ↥(stabSub (commSub ⊤ L))) =
          g⁻¹ * m * g from Subtype.ext rfl]
      simp only [map_mul, map_inv]
    rw [hmap, hmψ]
    group

private theorem s16h_L3_res_quasi {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hL3 : IsSLn ↥L 3 1) :
    CFSG.Open.IsQuasisimple ↥(autSub L (commSub ⊤ L)) :=
  s16h_L3_isQuasisimple_of_mulEquiv (s16h_L3_equiv hc hL3).symm hc.comp.2.2

private theorem s16h_L3_res_sl3 {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) (hL3 : IsSLn ↥L 3 1) :
    IsSLn ↥(autSub L (commSub ⊤ L)) 3 1 := by
  have he := s16h_L3_equiv hc hL3
  obtain ⟨K, hF, hfin, hcard, ⟨f⟩⟩ := hL3
  exact ⟨K, hF, hfin, hcard, ⟨he.symm.trans f⟩⟩

private theorem s16h_L3_res_comm {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    commSub ⊤ (autSub L (commSub ⊤ L)) = ⊤ := by
  set U : Subgroup W := commSub ⊤ L with hU
  set T : Subgroup ↥U := commSub ⊤ (autSub L U) with hTdef
  have hLq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  have hperfGroup : Group.IsPerfect ↥L := ⟨hLq.1⟩
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hperfGroup
  have h4 : commSub U L = U := by
    have h := CFSG.Quasithin.SmithD310U.commSub_commSub_eq hperf (⊤ : Subgroup W)
    simpa [hU] using h
  have hUT' : commSub U L ≤ T.map U.subtype := by
    rw [commSub, Subgroup.closure_le]
    rintro c ⟨x, hx, w, hw, rfl⟩
    have hxm : (x : MulAut W) w ∈ U :=
      ((mem_stabSub.mp (s16h_L3_le_stabSub L hx)) w).2 hw
    have hUm : (x : MulAut W) w * w⁻¹ ∈ U :=
      U.mul_mem hxm (U.inv_mem hw)
    refine Subgroup.mem_map.mpr ⟨⟨(x : MulAut W) w * w⁻¹, hUm⟩, ?_, rfl⟩
    have hgen : s16h_L3_resHom L ⟨x, hx⟩ ⟨w, hw⟩ * ⟨w, hw⟩⁻¹ ∈ T :=
      Subgroup.subset_closure
        ⟨s16h_L3_resHom L ⟨x, hx⟩, s16h_L3_resHom_mem_autSub L ⟨x, hx⟩,
          ⟨w, hw⟩, Subgroup.mem_top _, rfl⟩
    have hval : s16h_L3_resHom L ⟨x, hx⟩ ⟨w, hw⟩ = ⟨(x : MulAut W) w, hxm⟩ :=
      Subtype.ext (s16h_L3_resHom_apply L ⟨x, hx⟩ ⟨w, hw⟩)
    rw [hval] at hgen
    convert hgen using 1
  have hUT : U ≤ T.map U.subtype := h4.ge.trans hUT'
  have hTU : T.map U.subtype = U := le_antisymm (Subgroup.map_subtype_le T) hUT
  rw [eq_top_iff]
  intro u _
  have hu : (u : W) ∈ T.map U.subtype := by rw [hTU]; exact u.2
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hu
  have hveq : v = u := Subtype.ext hvu
  rw [hveq] at hv
  exact hv

private theorem s16h_L3_res_faithful {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) :
    ∀ a ∈ autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L),
      (∀ u : ↥(commSub ⊤ L), a u * u⁻¹ ∈ fixV (autSub L (commSub ⊤ L))) → a = 1 := by
  intro a ha hfix
  obtain ⟨g, hg, rfl⟩ := mem_autSub.mp ha
  have hgN : (g : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.mem_inf.mp hg).2
  have hquot : ∀ w ∈ commSub ⊤ L,
      (g : MulAut W) w * w⁻¹ ∈ commSub ⊤ L ⊓ fixV L := by
    intro w hw
    have hgw : (g : MulAut W) w ∈ commSub ⊤ L :=
      (mem_stabSub.mp g.2 w).2 hw
    refine ⟨(commSub ⊤ L).mul_mem hgw ((commSub ⊤ L).inv_mem hw), ?_⟩
    have h := hfix ⟨w, hw⟩
    have he : resHom (commSub ⊤ L) g ⟨w, hw⟩ * ⟨w, hw⟩⁻¹ =
        (⟨(g : MulAut W) w * w⁻¹, (commSub ⊤ L).mul_mem hgw
          ((commSub ⊤ L).inv_mem hw)⟩ : ↥(commSub ⊤ L)) :=
      Subtype.ext rfl
    rw [he] at h
    exact s16h_L3_mem_fixV_of_mem_fixV_autSub h
  have htriv := s16h_H5_triv_of_triv_quot hc.comp hgN hquot
  ext u
  rw [resHom_apply]
  simpa using htriv u.1 u.2

theorem s16h_L3_res_algebra {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
    {t : MulAut W} (hc : s16h_H5Cfg A L t) (hL3 : IsSLn ↥L 3 1) :
    (∀ u : ↥(commSub ⊤ L), u * u = 1) ∧
    autSub L (commSub ⊤ L) ≤
      autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L) ∧
    autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L) ≤
      Subgroup.normalizer (autSub L (commSub ⊤ L) : Set (MulAut ↥(commSub ⊤ L))) ∧
    CFSG.Open.IsQuasisimple ↥(autSub L (commSub ⊤ L)) ∧
    IsSLn ↥(autSub L (commSub ⊤ L)) 3 1 ∧
    commSub ⊤ (autSub L (commSub ⊤ L)) = ⊤ ∧
    (∀ a ∈ autSub (A ⊓ Subgroup.normalizer (L : Set (MulAut W))) (commSub ⊤ L),
      (∀ u : ↥(commSub ⊤ L), a u * u⁻¹ ∈ fixV (autSub L (commSub ⊤ L))) → a = 1) :=
  ⟨s16h_L3_res_elem hc, s16h_L3_res_le hc, s16h_L3_res_normal hc,
    s16h_L3_res_quasi hc hL3, s16h_L3_res_sl3 hc hL3, s16h_L3_res_comm hc,
    s16h_L3_res_faithful hc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
