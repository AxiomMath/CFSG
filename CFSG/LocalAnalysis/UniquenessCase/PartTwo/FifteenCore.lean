module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Core_imgTil_iSup {ι : Sort*} (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (U : ι → Subgroup G) (hU : ∀ i, U i ≤ V) :
    imgTil V₀ V hV (⨆ i, U i) = ⨆ i, imgTil V₀ V hV (U i) := by
  unfold imgTil
  rw [← Subgroup.map_iSup]
  congr 1
  have hcomap : ∀ U : Subgroup G, intSub V hV U = U.comap (valHom V hV) := fun U => rfl
  have hinj : Function.Injective (valHom V hV) := fun _ _ h => IntMod.val_injective h
  have hrange : (valHom V hV).range = V := by
    ext g
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.val_mem, fun hg => ⟨IntMod.mk hV ⟨g, hg⟩, rfl⟩⟩
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_iSup]
  simp only [hcomap, Subgroup.map_comap_eq, hrange]
  rw [inf_eq_right.mpr (iSup_le hU), iSup_congr fun i => inf_eq_right.mpr (hU i)]

theorem s15_Core_imgTil_sup {V₀ V A B : Subgroup G} (hV : IsElemAbelian 2 V) (hA : A ≤ V)
    (hB : B ≤ V) :
    imgTil V₀ V hV (A ⊔ B) = imgTil V₀ V hV A ⊔ imgTil V₀ V hV B := by
  unfold imgTil
  rw [← Subgroup.map_sup]
  congr 1
  have hcomap : ∀ U : Subgroup G, intSub V hV U = U.comap (valHom V hV) := fun U => rfl
  have hinj : Function.Injective (valHom V hV) := fun _ _ h => IntMod.val_injective h
  have hrange : (valHom V hV).range = V := by
    ext g
    exact ⟨fun ⟨x, hx⟩ => hx ▸ x.val_mem, fun hg => ⟨IntMod.mk hV ⟨g, hg⟩, rfl⟩⟩
  apply Subgroup.map_injective hinj
  rw [Subgroup.map_sup]
  simp only [hcomap, Subgroup.map_comap_eq, hrange]
  rw [inf_eq_right.mpr (sup_le hA hB), inf_eq_right.mpr hA, inf_eq_right.mpr hB]

theorem s15_Core_imgTil_eq_bot_of_le {V₀ V U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ≤ V₀) : imgTil V₀ V hV U = ⊥ := by
  rw [eq_bot_iff]
  rintro q hq
  rw [mem_imgTil] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  rw [Subgroup.mem_bot, ← map_one (mkTil V₀ V hV), mkTil_eq_iff]
  simpa using hU hx

theorem s15_Core_commSub_map_conj {W : Type*} [CommGroup W]
    (U : Subgroup W) (Y : Subgroup (MulAut W)) (α : MulAut W) :
    commSub (U.map α.toMonoidHom) (Y.map (MulAut.conj α).toMonoidHom) =
      (commSub U Y).map α.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, w, hw, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    refine ⟨x₀ w₀ * w₀⁻¹, ⟨x₀, hx₀, w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨x₀, hx₀, w₀, hw₀, rfl⟩ := hs
    refine ⟨MulAut.conj α x₀, ⟨x₀, hx₀, rfl⟩, α w₀, ⟨w₀, hw₀, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply,
      MulAut.apply_inv_self, MulAut.inv_apply_self, map_mul, map_inv]

theorem s15_Core_map_eq_self_of_card_le_two {A : Type*} [Group A] [Finite A] (U : Subgroup A)
    (e : MulAut A) (hU : Nat.card U ≤ 2) (hmap : ∀ u ∈ U, e u ∈ U) : ∀ u ∈ U, e u = u := by
  classical
  haveI := Fintype.ofFinite U
  intro u hu
  by_cases hu1 : u = 1
  · rw [hu1, map_one]
  · have heu : e u ∈ U := hmap u hu
    have heu1 : e u ≠ 1 := by
      intro h
      apply hu1
      apply e.injective
      rw [h, map_one]
    by_contra hne
    have hcard3 : 3 ≤ Nat.card U := by
      let a : U := ⟨1, U.one_mem⟩
      let b : U := ⟨u, hu⟩
      let c : U := ⟨e u, heu⟩
      have hab : a ≠ b := fun h => hu1 (Subtype.ext_iff.mp h).symm
      have hac : a ≠ c := fun h => heu1 (Subtype.ext_iff.mp h).symm
      have hbc : b ≠ c := fun h => hne (Subtype.ext_iff.mp h).symm
      have hc : ({a, b, c} : Finset U).card = 3 :=
        Finset.card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
      have hle : ({a, b, c} : Finset U).card ≤ Nat.card U := by
        have h := Finset.card_le_univ ({a, b, c} : Finset U)
        rwa [Nat.card_eq_fintype_card]
      rw [hc] at hle
      exact hle
    omega

theorem s15_Core_ncard_range_eq {α β γ : Type*} (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) : (Set.range f).ncard = (Set.range g).ncard := by
  refine Set.ncard_congr (s := Set.range f) (t := Set.range g)
    (fun y hy => g (Classical.choose hy)) ?_ ?_ ?_
  · intro y hy
    exact ⟨Classical.choose hy, rfl⟩
  · intro y z hy hz hEq
    have hf : f (Classical.choose hy) = f (Classical.choose hz) := (h _ _).2 hEq
    rw [← Classical.choose_spec hy, hf, Classical.choose_spec hz]
  · intro b hb
    obtain ⟨a, rfl⟩ := hb
    refine ⟨f a, ⟨a, rfl⟩, ?_⟩
    exact (h _ _).1 (Classical.choose_spec (show f a ∈ Set.range f from ⟨a, rfl⟩))

theorem s15_Core_barSub_conj_eq_bot_iff {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {m : G} (hm : m ∈ D.M) :
    barSub V₀ V h.isElemAbelian (conjSubgroup L m) = ⊥ ↔
      barSub V₀ V h.isElemAbelian L = ⊥ := by
  have hm₁ : m ∈ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hm
  rw [s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian hm₁ L]
  exact Subgroup.map_eq_bot_iff_of_injective (barSub V₀ V h.isElemAbelian L)
    (MulAut.conj _).injective

theorem s15_Core_commSub_wTil_conj {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {m : G} (hm : m ∈ D.M) :
    commSub (wTil V₀ V h.isElemAbelian (conjSubgroup L m))
        (barSub V₀ V h.isElemAbelian (conjSubgroup L m)) =
      wTil V₀ V h.isElemAbelian (conjSubgroup L m) := by
  have hV := h.isElemAbelian
  have hm₁ : m ∈ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ hm
  have hW := s15_Infra_wTil_conjSubgroup V₀ V L hV hm₁
  have hK := s15_Infra_barSub_conjSubgroup V₀ V hV hm₁ L
  have hmain : commSub (wTil V₀ V hV L) (barSub V₀ V hV L) = wTil V₀ V hV L := by
    have h1 := s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (s15_Kbar_no_two_quotient h)
    simpa only [wTil] using h1
  rw [hW, hK, s15_Core_commSub_map_conj, hmain]

theorem s15_Core_wTil_conj_eq_iff {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) {m m' : G} (hm : m ∈ D.M) (hm' : m' ∈ D.M) :
    wTil V₀ V h.isElemAbelian (conjSubgroup L m) =
        wTil V₀ V h.isElemAbelian (conjSubgroup L m') ↔
      barSub V₀ V h.isElemAbelian (conjSubgroup L m) =
        barSub V₀ V h.isElemAbelian (conjSubgroup L m') := by
  constructor
  · intro hW
    by_contra hK
    have hV := h.isElemAbelian
    have hne : (m' * m⁻¹) ∉ nBar D.M V₀ V hV L := fun hmem =>
      hK ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV hm hm').1 hmem).symm
    have hc := (s15_Kbar_commute_conj h hm hm' hne).2
    have hbot : wTil V₀ V hV (conjSubgroup L m') = ⊥ := by
      rw [← s15_Core_commSub_wTil_conj h hm']
      rw [← hW]
      exact hc
    have hKbot : barSub V₀ V hV (conjSubgroup L m') = ⊥ :=
      s15_Lin_eq_bot_of_commSub_top_eq_bot hbot
    exact hL ((s15_Core_barSub_conj_eq_bot_iff h hm').1 hKbot)
  · intro hK
    exact congrArg (fun X => commSub ⊤ X) hK

theorem s15_Core_imgTil_v1Sub_le_fixV {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) {m : G} (hm : m ∈ D.M) :
    imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) ≤
      fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L m)) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  by_cases h0 : V₀ = ⊥
  ·
    rw [s15_Infra_v1Sub_eq_iSup h.hyp125 hV h0,
      s15_Core_imgTil_iSup V₀ V hV
        (fun m' : D.M => wSub V₀ V hV (conjSubgroup L (m' : G)) ⊓
          centralizer (conjSubgroup L (m' : G) : Set G))
        (fun m' => inf_le_left.trans (preTil_le V₀ V hV _))]
    refine iSup_le fun m' => ?_
    intro q hq
    rw [mem_fixV]
    intro k hk
    rw [mem_imgTil] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    by_cases hKm : barSub V₀ V hV (conjSubgroup L (m' : G)) =
        barSub V₀ V hV (conjSubgroup L m)
    ·
      obtain ⟨l, hlX, hlk⟩ :=
        (mem_barSub V₀ V hV (conjSubgroup L (m' : G)) k).1 (hKm.symm ▸ hk)
      rw [← hlk, ← hzq, actTil_mk, mkTil_eq_iff]
      have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 (l : G) hlX
      have h1 : (actStab V₀ V hV l z).val * z.val⁻¹ = 1 := by
        rw [actStab_apply_val, hcomm]
        group
      rw [h1]
      exact Subgroup.one_mem V₀
    ·
      have hne : ((m : G) * (m' : G)⁻¹) ∉ nBar D.M V₀ V hV L := fun hmem =>
        hKm ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m'.2 hm).1 hmem).symm
      have hfixW : wTil V₀ V hV (conjSubgroup L (m' : G)) ≤
          fixV (barSub V₀ V hV (conjSubgroup L m)) :=
        commSub_eq_bot_iff.mp (s15_Kbar_commute_conj h m'.2 hm hne).2
      have hmono : imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (m' : G)) ⊓
            centralizer (conjSubgroup L (m' : G) : Set G)) ≤
          imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (m' : G))) := by
        rintro p hp
        rw [mem_imgTil] at hp ⊢
        obtain ⟨y, hy, hyq⟩ := hp
        exact ⟨y, hy.1, hyq⟩
      have hqW : q ∈ wTil V₀ V hV (conjSubgroup L (m' : G)) := by
        have h2 : q ∈ imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (m' : G))) :=
          hmono ((mem_imgTil V₀ V hV _ q).2 ⟨z, hz, hzq⟩)
        rwa [wSub, imgTil_preTil] at h2
      exact mem_fixV.mp (hfixW hqW) k hk
  ·
    rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    rw [s15_Core_imgTil_eq_bot_of_le hV le_rfl]
    exact bot_le

private theorem s15_Core_imgTil_iSup_ne {D : Data G} {V₀ V W₀ L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (m : D.M) :
    (⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
        barSub V₀ V hV (conjSubgroup L (m : G))),
      imgTil W₀ V hV (conjSubgroup (wSub V₀ V hV L) (m' : G))) =
      imgTil W₀ V hV (⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
        barSub V₀ V hV (conjSubgroup L (m : G))),
        conjSubgroup (wSub V₀ V hV L) (m' : G)) := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.pairFacts.le_normalizer h.pairFacts.le_normalizer₀
  let P : D.M → Prop := fun m' => barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
    barSub V₀ V hV (conjSubgroup L (m : G))
  let A : D.M → Subgroup G := fun m' => conjSubgroup (wSub V₀ V hV L) (m' : G)
  have hA : ∀ m', A m' ≤ V := by
    intro m'
    change conjSubgroup (wSub V₀ V hV L) (m' : G) ≤ V
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m'.2)]
    exact preTil_le V₀ V hV _
  change (⨆ m', ⨆ (_ : P m'), imgTil W₀ V hV (A m')) =
    imgTil W₀ V hV (⨆ m', ⨆ (_ : P m'), A m')
  have houter : imgTil W₀ V hV (⨆ m', ⨆ (_ : P m'), A m') =
      ⨆ m', imgTil W₀ V hV (⨆ (_ : P m'), A m') :=
    s15_Core_imgTil_iSup W₀ V hV (fun m' => ⨆ (_ : P m'), A m')
      (fun m' => iSup_le fun _ => hA m')
  have hinner : ∀ m', imgTil W₀ V hV (⨆ (_ : P m'), A m') =
      ⨆ (_ : P m'), imgTil W₀ V hV (A m') :=
    fun m' => s15_Core_imgTil_iSup W₀ V hV (fun _ : P m' => A m') (fun _ => hA m')
  exact (iSup_congr hinner).symm.trans houter.symm

theorem s15_Core_inf_fixV_le_imgTil_v1Sub {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) (m : D.M) :
    wTil V₀ V h.isElemAbelian (conjSubgroup L (m : G)) ⊓
        fixV (⨆ j : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (j : G))) ≤
      imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  by_cases h0 : V₀ = ⊥
  ·
    intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hqW, hqfix⟩ := hq
    rw [mem_imgTil]
    have hqW' : q ∈ imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (m : G))) := by
      rw [wSub, imgTil_preTil]
      exact hqW
    obtain ⟨z, hzW, hzq⟩ := (mem_imgTil V₀ V hV _ q).1 hqW'
    refine ⟨z, ?_, hzq⟩
    rw [s15_Infra_v1Sub_eq_iSup h.hyp125 hV h0]
    refine le_iSup (fun m' : D.M => wSub V₀ V hV (conjSubgroup L (m' : G)) ⊓
        centralizer (conjSubgroup L (m' : G) : Set G)) m ?_
    refine Subgroup.mem_inf.mpr ⟨hzW, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hlM : l ∈ D.M := by
      have hl' : l ∈ conjSubgroup L (m : G) := hl
      rw [mem_conjSubgroup_iff] at hl'
      rw [show l = (m : G)⁻¹ * ((m : G) * l * (m : G)⁻¹) * (m : G) by group]
      exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem m.2) (h.le hl')) m.2
    have hl_st : l ∈ stabTil V₀ V := hMs hlM
    have hkY : actTil V₀ V hV ⟨l, hl_st⟩ ∈
        ⨆ j : D.M, barSub V₀ V hV (conjSubgroup L (j : G)) :=
      le_iSup (fun j : D.M => barSub V₀ V hV (conjSubgroup L (j : G))) m
        (actTil_mem_barSub V₀ V hV hl hl_st)
    have hfixl : actTil V₀ V hV ⟨l, hl_st⟩ q = q := mem_fixV.mp hqfix _ hkY
    have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨l, hl_st⟩ z) = mkTil V₀ V hV z := by
      rw [← actTil_mk]
      rw [hzq, hfixl]
    have h1' : (actStab V₀ V hV ⟨l, hl_st⟩ z).val * z.val⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← h0]
      exact (mkTil_eq_iff V₀ V hV _ _).1 h1
    have h2 : (actStab V₀ V hV ⟨l, hl_st⟩ z).val * z.val⁻¹ = 1 := Subgroup.mem_bot.mp h1'
    rw [actStab_apply_val] at h2
    have h3 : l * z.val * l⁻¹ = z.val := mul_inv_eq_one.mp h2
    calc l * z.val = (l * z.val * l⁻¹) * l := by group
      _ = z.val * l := by rw [h3]
  ·
    have hfix0 : fixV (⨆ j : D.M, barSub V₀ V hV (conjSubgroup L (j : G))) = ⊥ := by
      refine s15_Kbar_fixV_eq_bot_of_ne_bot h.hyp125 h0 (s15_Infra_iSup_barSub_le h)
        (s15_Infra_iSup_barSub_normal h) ?_
      intro hYbot
      apply hL
      have hle : barSub V₀ V hV L ≤
          ⨆ j : D.M, barSub V₀ V hV (conjSubgroup L (j : G)) := by
        have h1 := le_iSup (fun j : D.M => barSub V₀ V hV (conjSubgroup L (j : G))) (1 : D.M)
        simpa only [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one] using h1
      exact le_bot_iff.mp (hle.trans (le_of_eq hYbot))
    have hV₁bot : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) = ⊥ := by
      rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
      exact s15_Core_imgTil_eq_bot_of_le hV le_rfl
    rw [hfix0, hV₁bot]
    simp

theorem s15_Core_imgTil_wSub_conj_eq_iff {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) {m m' : G} (hm : m ∈ D.M)
    (hm' : m' ∈ D.M) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) m) =
      imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) m') ↔
      barSub V₀ V h.isElemAbelian (conjSubgroup L m) =
        barSub V₀ V h.isElemAbelian (conjSubgroup L m') := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  constructor
  · intro hImg
    by_contra hK
    have hne : (m' * m⁻¹) ∉ nBar D.M V₀ V hV L := fun hmem =>
      hK ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV hm hm').1 hmem).symm
    have hle : conjSubgroup (wSub V₀ V hV L) m' ≤
        conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L := by
      intro w hw
      have hwV : w ∈ V := by
        have hsub := s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm')
        exact preTil_le V₀ V hV _ (hsub.symm ▸ hw)
      have hmem : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
          imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m) := by
        rw [hImg]
        exact (mem_imgTil (v1Sub D.M V₀ V hV L) V hV _ _).2
          ⟨IntMod.mk hV ⟨w, hwV⟩, hw, rfl⟩
      obtain ⟨x, hx, hxq⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV _ _).1 hmem
      rw [mkTil_eq_iff] at hxq
      have hxq' : w * x.val⁻¹ ∈ v1Sub D.M V₀ V hV L := by
        have h := (v1Sub D.M V₀ V hV L).inv_mem hxq
        rw [show (x.val * (IntMod.mk hV ⟨w, hwV⟩).val⁻¹)⁻¹ = w * x.val⁻¹ by
          rw [mul_inv_rev, inv_inv]
          rfl] at h
        exact h
      rw [show w = (w * x.val⁻¹) * x.val by group]
      simpa only [sup_comm] using Subgroup.mul_mem_sup hxq' hx
    have hwV : ∀ j : D.M, conjSubgroup (wSub V₀ V hV L) (j : G) ≤ V := by
      intro j
      rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs j.2)]
      exact preTil_le V₀ V hV _
    have hWtil_le : wTil V₀ V hV (conjSubgroup L m') ≤
        wTil V₀ V hV (conjSubgroup L m) ⊔ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
      have hmono : imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m') ≤
          imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L) := by
        rintro q hq
        rw [mem_imgTil] at hq ⊢
        obtain ⟨x, hx, hxq⟩ := hq
        exact ⟨x, hle hx, hxq⟩
      calc wTil V₀ V hV (conjSubgroup L m')
          = imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m') := by
            rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm')]
            exact (imgTil_preTil V₀ V hV (wTil V₀ V hV (conjSubgroup L m'))).symm
        _ ≤ imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L) := hmono
        _ = imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m) ⊔
              imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
            s15_Core_imgTil_sup hV (hwV ⟨m, hm⟩) (s15_Infra_v1Sub_le h.hyp125 hV)
        _ = wTil V₀ V hV (conjSubgroup L m) ⊔ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) := by
            rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm), wSub, imgTil_preTil]
    have hfix1 : wTil V₀ V hV (conjSubgroup L m) ≤
        fixV (barSub V₀ V hV (conjSubgroup L m')) :=
      commSub_eq_bot_iff.mp (s15_Kbar_commute_conj h hm hm' hne).2
    have hfix2 : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤
        fixV (barSub V₀ V hV (conjSubgroup L m')) := s15_Core_imgTil_v1Sub_le_fixV h hm'
    have hfix : wTil V₀ V hV (conjSubgroup L m') ≤
        fixV (barSub V₀ V hV (conjSubgroup L m')) :=
      hWtil_le.trans (sup_le hfix1 hfix2)
    have hWbot : wTil V₀ V hV (conjSubgroup L m') = ⊥ := by
      rw [← s15_Core_commSub_wTil_conj h hm']
      exact commSub_eq_bot_iff.mpr hfix
    have hKbot : barSub V₀ V hV (conjSubgroup L m') = ⊥ :=
      s15_Lin_eq_bot_of_commSub_top_eq_bot hWbot
    exact hL ((s15_Core_barSub_conj_eq_bot_iff h hm').1 hKbot)
  · intro hK
    have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV (conjSubgroup L m') := by
      rw [wTil, wTil, hK]
    have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV (conjSubgroup L m') := by
      rw [wSub, wSub, hWt]
    have h1 : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV (conjSubgroup L m) :=
      (s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)).symm
    have h2 : conjSubgroup (wSub V₀ V hV L) m' = wSub V₀ V hV (conjSubgroup L m') :=
      (s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm')).symm
    rw [h1, h2, hsub]

theorem s15_Core_inf_iSup_imgTil_wSub_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) (m : D.M) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) (m : G)) ⊓
      ⨆ (m' : D.M) (_ : barSub V₀ V h.isElemAbelian (conjSubgroup L (m' : G)) ≠
          barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))),
        imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
          (conjSubgroup (wSub V₀ V h.isElemAbelian L) (m' : G)) = ⊥ := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  let V₁ : Subgroup G := v1Sub D.M V₀ V hV L
  let W : D.M → Subgroup G := fun j => conjSubgroup (wSub V₀ V hV L) (j : G)
  let K : D.M → Subgroup (MulAut (Vtil V₀ V hV)) :=
    fun j => barSub V₀ V hV (conjSubgroup L (j : G))
  let P : D.M → Prop := fun j => K j ≠ K m
  let Y : Subgroup G := ⨆ (j : D.M) (_ : P j), W j
  have hsup : (⨆ (j : D.M) (_ : P j), imgTil V₁ V hV (W j)) = imgTil V₁ V hV Y := by
    simpa only [V₁, W, K, P, Y] using
      s15_Core_imgTil_iSup_ne (V₀ := V₀) (V := V) (W₀ := V₁) (L := L) h.hyp125 hV m
  have hsup0 : (⨆ (j : D.M) (_ : P j), imgTil V₀ V hV (W j)) = imgTil V₀ V hV Y := by
    simpa only [W, K, P, Y] using
      s15_Core_imgTil_iSup_ne (V₀ := V₀) (V := V) (W₀ := V₀) (L := L) h.hyp125 hV m
  change imgTil V₁ V hV (W m) ⊓ (⨆ (j : D.M) (_ : P j), imgTil V₁ V hV (W j)) = ⊥
  rw [hsup, eq_bot_iff]
  rintro q ⟨hqW, hqY⟩
  obtain ⟨z, hzW, hzq⟩ := (mem_imgTil V₁ V hV (W m) q).1 hqW
  obtain ⟨x, hxY, hxq⟩ := (mem_imgTil V₁ V hV Y q).1 hqY
  have hxz : (z * x⁻¹).val ∈ V₁ := by
    have h1 : x.val * z.val⁻¹ ∈ V₁ := (mkTil_eq_iff V₁ V hV x z).1 (hxq.trans hzq.symm)
    simpa only [IntMod.val_mul, IntMod.val_inv, mul_inv_rev, inv_inv] using V₁.inv_mem h1
  have hwt : mkTil V₀ V hV z ∈ wTil V₀ V hV (conjSubgroup L (m : G)) := by
    have h1 : z.val ∈ preTil V₀ V hV (wTil V₀ V hV (conjSubgroup L (m : G))) := by
      have h2 : z.val ∈ wSub V₀ V hV (conjSubgroup L (m : G)) := by
        rw [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs m.2)]
        exact hzW
      exact h2
    obtain ⟨y, hyval, hymem⟩ := (mem_preTil V₀ V hV _).1 h1
    rwa [IntMod.val_injective hyval] at hymem
  have hxY0 : mkTil V₀ V hV x ∈
      ⨆ (j : D.M) (_ : P j), wTil V₀ V hV (conjSubgroup L (j : G)) := by
    have h1 : mkTil V₀ V hV x ∈ imgTil V₀ V hV Y :=
      (mem_imgTil V₀ V hV Y x).2 ⟨x, hxY, rfl⟩
    rw [← hsup0] at h1
    have hcongr : (⨆ (j : D.M) (_ : P j), imgTil V₀ V hV (W j)) =
        ⨆ (j : D.M) (_ : P j), wTil V₀ V hV (conjSubgroup L (j : G)) := by
      refine iSup_congr fun j => iSup_congr fun _ => ?_
      rw [show W j = wSub V₀ V hV (conjSubgroup L (j : G)) from
        (s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs j.2)).symm]
      rw [wSub, imgTil_preTil]
    rwa [hcongr] at h1
  have hleKm : (⨆ (j : D.M) (_ : P j), wTil V₀ V hV (conjSubgroup L (j : G))) ≤
      fixV (K m) := by
    refine iSup₂_le fun j hj => ?_
    have hne : (m : G) * (j : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
      hj ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV j.2 m.2).1 hmem).symm
    exact commSub_eq_bot_iff.mp (s15_Kbar_commute_conj h j.2 m.2 hne).2
  have hxKm : mkTil V₀ V hV x ∈ fixV (K m) := hleKm hxY0
  have hzx : mkTil V₀ V hV (z * x⁻¹) ∈ imgTil V₀ V hV V₁ :=
    (mem_imgTil V₀ V hV V₁ _).2 ⟨z * x⁻¹, hxz, rfl⟩
  have hzxKm : mkTil V₀ V hV (z * x⁻¹) ∈ fixV (K m) :=
    s15_Core_imgTil_v1Sub_le_fixV h (m := (m : G)) m.2 hzx
  have hwz : mkTil V₀ V hV z = mkTil V₀ V hV (z * x⁻¹) * mkTil V₀ V hV x := by
    have hzxz : (z * x⁻¹) * x = z := by group
    rw [← map_mul, hzxz]
  have hwKm : mkTil V₀ V hV z ∈ fixV (K m) := by
    rw [hwz]
    exact (fixV (K m)).mul_mem hzxKm hxKm
  have hfix : mkTil V₀ V hV z ∈ fixV (⨆ j : D.M, K j) := by
    rw [mem_fixV]
    intro k hk
    refine Subgroup.iSup_induction K
      (C := fun k => k (mkTil V₀ V hV z) = mkTil V₀ V hV z) hk ?_ ?_ ?_
    · intro j y hy
      by_cases hjm : K j = K m
      · exact mem_fixV.mp (by rw [hjm]; exact hwKm) y hy
      · have hne : (j : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
          hjm ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m.2 j.2).1 hmem)
        have hle : wTil V₀ V hV (conjSubgroup L (m : G)) ≤ fixV (K j) :=
          commSub_eq_bot_iff.mp (s15_Kbar_commute_conj h m.2 j.2 hne).2
        exact mem_fixV.mp (hle hwt) y hy
    · exact MulAut.one_apply _ _
    · intro a b ha hb
      rw [MulAut.mul_apply, hb, ha]
  have hV₁mem := s15_Core_inf_fixV_le_imgTil_v1Sub h hL m
    (Subgroup.mem_inf.mpr ⟨hwt, hfix⟩)
  obtain ⟨v, hvV₁, hvq⟩ := (mem_imgTil V₀ V hV V₁ _).1 hV₁mem
  have hvz : v.val * z.val⁻¹ ∈ V₀ := (mkTil_eq_iff V₀ V hV v z).1 hvq
  have hzv : (z * v⁻¹).val ∈ V₁ := by
    have h2 : (v.val * z.val⁻¹)⁻¹ ∈ V₁ :=
      s15_Infra_le_v1Sub D.M V₀ V hV L (V₀.inv_mem hvz)
    simpa only [IntMod.val_mul, IntMod.val_inv, mul_inv_rev, inv_inv] using h2
  have hzV₁ : z.val ∈ V₁ := by
    rw [show z.val = (z * v⁻¹).val * v.val by
      rw [← IntMod.val_mul]
      congr 1
      group]
    exact V₁.mul_mem hzv hvV₁
  have hq1 : mkTil V₁ V hV z = 1 := by
    rw [← map_one (mkTil V₁ V hV), mkTil_eq_iff]
    show z.val * (1 : IntMod V hV).val⁻¹ ∈ V₁
    simpa using hzV₁
  rw [Subgroup.mem_bot, ← hzq]
  exact hq1

theorem sSupIndep_wStarConj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    sSupIndep (wStarConj D.M V₀ V hV L) := by
  intro X hX
  obtain ⟨m, hm, rfl⟩ := hX
  rw [disjoint_iff, eq_bot_iff]
  have hle : sSup (wStarConj D.M V₀ V hV L \
        {imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m : G))}) ≤
      ⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
          barSub V₀ V hV (conjSubgroup L (m : G))),
        imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m' : G)) := by
    apply sSup_le
    rintro Y ⟨hY, hYX⟩
    obtain ⟨m', hm', rfl⟩ := hY
    have hne : (imgTil (v1Sub D.M V₀ V hV L) V hV
        (conjSubgroup (wSub V₀ V hV L) (m' : G))) ≠
        imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m : G)) := by
      simpa using hYX
    have hKne : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
        barSub V₀ V hV (conjSubgroup L (m : G)) := fun hEq =>
      hne ((s15_Core_imgTil_wSub_conj_eq_iff h hL hm' hm).mpr hEq)
    exact le_iSup₂ (f := fun (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
        barSub V₀ V hV (conjSubgroup L (m : G))) =>
        imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m' : G))) ⟨m', hm'⟩ hKne
  calc imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) (m : G)) ⊓
        sSup (wStarConj D.M V₀ V hV L \
          {imgTil (v1Sub D.M V₀ V hV L) V hV
            (conjSubgroup (wSub V₀ V hV L) (m : G))})
      ≤ imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) (m : G)) ⊓
        ⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
            barSub V₀ V hV (conjSubgroup L (m : G))),
          imgTil (v1Sub D.M V₀ V hV L) V hV
            (conjSubgroup (wSub V₀ V hV L) (m' : G)) := inf_le_inf_left _ hle
    _ ≤ ⊥ := le_of_eq (s15_Core_inf_iSup_imgTil_wSub_eq_bot h hL ⟨m, hm⟩)

theorem s15_Core_wTil_le_imgTil_v1Sub_of_gamma_le_one {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hγ : gamma15 D.M V₀ V h.isElemAbelian L ≤ 1) :
    wTil V₀ V h.isElemAbelian L ≤
      imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hWcomm : commSub (wTil V₀ V hV L) (barSub V₀ V hV L) = wTil V₀ V hV L := by
    have h1 := s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (s15_Kbar_no_two_quotient h)
    simpa only [wTil] using h1
  have hinv : ∀ x' ∈ barSub V₀ V hV L, ∀ u ∈ wTil V₀ V hV L, x' u ∈ wTil V₀ V hV L := by
    intro x' hx' u hu
    have h1 : x' u * u⁻¹ ∈ wTil V₀ V hV L := by
      have hmem : x' u * u⁻¹ ∈ commSub (wTil V₀ V hV L) (barSub V₀ V hV L) :=
        Subgroup.subset_closure ⟨x', hx', u, hu, rfl⟩
      rwa [hWcomm] at hmem
    rw [show x' u = (x' u * u⁻¹) * u by group]
    exact (wTil V₀ V hV L).mul_mem h1 hu
  have hcard : Nat.card (wStar D.M V₀ V hV L) ≤ 2 := by
    rw [card_eq_two_pow (s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV)
      (wStar D.M V₀ V hV L)]
    have hγ' : gamma15 D.M V₀ V hV L ≤ 1 := hγ
    calc 2 ^ rk ↥(wStar D.M V₀ V hV L) = 2 ^ gamma15 D.M V₀ V hV L := rfl
      _ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hγ'
      _ = 2 := by norm_num
  rw [show wTil V₀ V hV L = commSub (wTil V₀ V hV L) (barSub V₀ V hV L) from hWcomm.symm]
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨x, hx, w, hw, rfl⟩
  obtain ⟨l, hlX, hlx⟩ := (mem_barSub V₀ V hV L x).1 hx
  have hl0 : (l : G) ∈ stabTil V₀ V := l.2
  have hlM : (l : G) ∈ D.M := h.le hlX
  have hl1 : (l : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer
      (s15_Infra_le_normalizer_v1Sub h.hyp125 hV) hlM
  have hw' : w ∈ imgTil V₀ V hV (wSub V₀ V hV L) := by
    rw [wSub, imgTil_preTil]
    exact hw
  obtain ⟨z, hzW, hzq⟩ := (mem_imgTil V₀ V hV (wSub V₀ V hV L) w).1 hw'
  have hmapW : ∀ u ∈ wStar D.M V₀ V hV L,
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩ u ∈ wStar D.M V₀ V hV L := by
    intro u hu
    obtain ⟨y, hyW, hyq⟩ :=
      (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) u).1 hu
    refine (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) _).2
      ⟨actStab (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩ y, ?_, ?_⟩
    · rw [wSub, mem_preTil]
      refine ⟨actStab (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩ y, rfl, ?_⟩
      have hyWtil : mkTil V₀ V hV y ∈ wTil V₀ V hV L := by
        obtain ⟨a, ha, hamem⟩ := (mem_preTil V₀ V hV (wTil V₀ V hV L)).1 hyW
        rwa [IntMod.val_injective ha] at hamem
      have hEq : mkTil V₀ V hV
          (actStab (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩ y) =
          actTil V₀ V hV ⟨(l : G), hl0⟩ (mkTil V₀ V hV y) := by
        have hstab : actStab (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩ y =
            actStab V₀ V hV ⟨(l : G), hl0⟩ y := by
          apply IntMod.val_injective
          rw [actStab_apply_val, actStab_apply_val]
        rw [hstab, ← actTil_mk]
      rw [hEq]
      exact hinv _ (actTil_mem_barSub V₀ V hV hlX hl0) _ hyWtil
    · rw [← hyq, actTil_mk]
  have hmap_eq := s15_Core_map_eq_self_of_card_le_two (wStar D.M V₀ V hV L)
    (actTil (v1Sub D.M V₀ V hV L) V hV ⟨(l : G), hl1⟩) hcard hmapW
  have hzWstar : mkTil (v1Sub D.M V₀ V hV L) V hV z ∈ wStar D.M V₀ V hV L :=
    (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) _).2 ⟨z, hzW, rfl⟩
  have heq := hmap_eq _ hzWstar
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at heq
  refine (mem_imgTil V₀ V hV (v1Sub D.M V₀ V hV L) _).2
    ⟨actStab V₀ V hV ⟨(l : G), hl0⟩ z * z⁻¹, ?_, ?_⟩
  · rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
    exact heq
  · rw [map_mul, map_inv, ← actTil_mk, ← hlx, ← hzq]

theorem two_le_gamma15 (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) :
    2 ≤ gamma15 D.M V₀ V hV L := by
  by_contra hγ
  have hγ' : gamma15 D.M V₀ V hV L ≤ 1 := by have := not_le.1 hγ; omega
  have hWle : wTil V₀ V hV L ≤ imgTil V₀ V hV (v1Sub D.M V₀ V hV L) :=
    s15_Core_wTil_le_imgTil_v1Sub_of_gamma_le_one h hγ'
  have hfix : imgTil V₀ V hV (v1Sub D.M V₀ V hV L) ≤ fixV (barSub V₀ V hV L) := by
    have h1 := s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
    simpa only [conjSubgroup_one] using h1
  have hcomm : commSub (wTil V₀ V hV L) (barSub V₀ V hV L) = ⊥ :=
    commSub_eq_bot_iff.mpr (hWle.trans hfix)
  have hWcomm : commSub (wTil V₀ V hV L) (barSub V₀ V hV L) = wTil V₀ V hV L := by
    have h1 := s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one V₀ V hV)
      (s15_Kbar_no_two_quotient h)
    simpa only [wTil] using h1
  have hWbot : wTil V₀ V hV L = ⊥ := by rw [← hWcomm]; exact hcomm
  exact hL (s15_Lin_eq_bot_of_commSub_top_eq_bot hWbot)

theorem inf_normalizer_wSub_eq_nBar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    D.M ⊓ normalizer (wSub V₀ V hV L : Set G) = nBar D.M V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  ext m
  by_cases hL : barSub V₀ V hV L = ⊥
  · rw [s15_Infra_nBar_eq_of_barSub_eq_bot h.hyp125 hV hL,
      s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL]
    constructor
    · rintro ⟨hm, -⟩
      exact hm
    · intro hm
      exact ⟨hm, h.hyp125.pairFacts.le_normalizer₀ hm⟩
  · constructor
    · rintro ⟨hm, hnorm⟩
      have hconj : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L :=
        conjSubgroup_eq_iff_mem_normalizer.mpr hnorm
      have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV L := by
        rw [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)]
        exact hconj
      have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV L := by
        have h1 : imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L m)) =
            imgTil V₀ V hV (wSub V₀ V hV L) := by rw [hsub]
        rwa [wSub, wSub, imgTil_preTil, imgTil_preTil] at h1
      have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L := by
        have h1 := (s15_Core_wTil_conj_eq_iff h hL hm D.M.one_mem)
        have h2 : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV (conjSubgroup L 1) := by
          simpa only [conjSubgroup_one] using hWt
        simpa only [conjSubgroup_one] using h1.mp h2
      exact (s15_Infra_mem_nBar_iff h.hyp125 hV hm).2 hK
    · intro hm
      have hmM : m ∈ D.M := ((mem_preBarSub D.M V₀ V hV _).1 hm).1
      have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L :=
        (s15_Infra_mem_nBar_iff h.hyp125 hV hmM).1 hm
      have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV L := by
        have h1 := (s15_Core_wTil_conj_eq_iff h hL hmM D.M.one_mem).mpr ?_
        · simpa only [conjSubgroup_one] using h1
        · simpa only [conjSubgroup_one] using hK
      have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV L := by
        rw [wSub, wSub, hWt]
      have hconj : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L := by
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hmM)]
        exact hsub
      exact ⟨hmM, conjSubgroup_eq_iff_mem_normalizer.mp hconj⟩

theorem inf_normalizer_wSub_sup_v1Sub_eq_nBar (D : Data G)
    {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    D.M ⊓ normalizer ((wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L : Subgroup G) : Set G) =
      nBar D.M V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  ext m
  by_cases hL : barSub V₀ V hV L = ⊥
  · rw [s15_Infra_nBar_eq_of_barSub_eq_bot h.hyp125 hV hL,
      s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL,
      s15_Infra_v1Sub_eq_of_barSub_eq_bot h.hyp125 hV hL, sup_idem]
    constructor
    · rintro ⟨hm, -⟩
      exact hm
    · intro hm
      exact ⟨hm, h.hyp125.pairFacts.le_normalizer₀ hm⟩
  · constructor
    · rintro ⟨hm, hnorm⟩
      have hV₁V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
      have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
      have hconj : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m =
          wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L :=
        conjSubgroup_eq_iff_mem_normalizer.mpr hnorm
      have hsplit : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m =
          conjSubgroup (wSub V₀ V hV L) m ⊔ conjSubgroup (v1Sub D.M V₀ V hV L) m :=
        Subgroup.map_sup _ _ _
      have hWm : conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L =
          wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
        rw [← s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hm]
        rw [← hsplit, hconj, s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hm]
      have hU : conjSubgroup (wSub V₀ V hV L) m ≤ V := by
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm)]
        exact preTil_le V₀ V hV _
      have hImg : imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L) =
          imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m) :=
        s15_Infra_imgTil_sup_left (V₀ := v1Sub D.M V₀ V hV L)
          (U := conjSubgroup (wSub V₀ V hV L) m) hV hU hV₁V
      have hWst : wStar D.M V₀ V hV L =
          imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) m) := by
        rw [wStar]
        rw [← s15_Infra_imgTil_sup_left (V₀ := v1Sub D.M V₀ V hV L)
          (U := wSub V₀ V hV L) hV hWV hV₁V]
        rw [show wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L =
            conjSubgroup (wSub V₀ V hV L) m ⊔ v1Sub D.M V₀ V hV L from hWm.symm]
        exact hImg
      have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L := by
        have h1 : imgTil (v1Sub D.M V₀ V hV L) V hV
              (conjSubgroup (wSub V₀ V hV L) m) =
            imgTil (v1Sub D.M V₀ V hV L) V hV
              (conjSubgroup (wSub V₀ V hV L) (1 : G)) := by
          rw [conjSubgroup_one]
          exact hWst.symm
        have h2 := (s15_Core_imgTil_wSub_conj_eq_iff h hL hm D.M.one_mem).mp h1
        simpa only [conjSubgroup_one] using h2
      exact (s15_Infra_mem_nBar_iff h.hyp125 hV hm).2 hK
    · intro hm
      have hmM : m ∈ D.M := ((mem_preBarSub D.M V₀ V hV _).1 hm).1
      have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L :=
        (s15_Infra_mem_nBar_iff h.hyp125 hV hmM).1 hm
      have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV L := by
        have h1 := (s15_Core_wTil_conj_eq_iff h hL hmM D.M.one_mem).mpr ?_
        · simpa only [conjSubgroup_one] using h1
        · simpa only [conjSubgroup_one] using hK
      have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV L := by
        rw [wSub, wSub, hWt]
      have hconjW : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L := by
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hmM)]
        exact hsub
      have hconj : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m =
          wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L := by
        rw [show conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m =
            conjSubgroup (wSub V₀ V hV L) m ⊔ conjSubgroup (v1Sub D.M V₀ V hV L) m from
            Subgroup.map_sup _ _ _,
          hconjW, s15_Infra_conjSubgroup_v1Sub h.hyp125 hV hmM]
      exact ⟨hmM, conjSubgroup_eq_iff_mem_normalizer.mp hconj⟩

theorem preBarSub_stabSub_wStar (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    preBarSub D.M (v1Sub D.M V₀ V hV L) V hV (stabSub (wStar D.M V₀ V hV L)) =
      nBar D.M V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  let V₁ : Subgroup G := v1Sub D.M V₀ V hV L
  have hV₁V : V₁ ≤ V := s15_Infra_v1Sub_le h.hyp125 hV
  have hMnorm₁ : D.M ≤ normalizer (V₁ : Set G) :=
    s15_Infra_le_normalizer_v1Sub h.hyp125 hV
  ext m
  rw [mem_preBarSub]
  by_cases hL : barSub V₀ V hV L = ⊥
  · rw [s15_Infra_nBar_eq_of_barSub_eq_bot h.hyp125 hV hL]
    constructor
    · rintro ⟨hm, -⟩
      exact hm
    · intro hm
      have hmst : m ∈ stabTil V₁ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer hMnorm₁ hm
      have hWeq : wSub V₀ V hV L = V₀ := s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL
      have hWbot : wStar D.M V₀ V hV L = ⊥ :=
        s15_Core_imgTil_eq_bot_of_le (V₀ := V₁) (V := V) (U := wSub V₀ V hV L) hV
          (by rw [hWeq]; exact s15_Infra_le_v1Sub D.M V₀ V hV L)
      have hstab : stabSub (⊥ : Subgroup (vStar D.M V₀ V hV L)) = ⊤ := by
        apply top_le_iff.mp
        intro g _
        rw [mem_stabSub]
        intro u
        rw [Subgroup.mem_bot, Subgroup.mem_bot]
        constructor
        · intro h
          exact g.injective (h.trans (map_one g).symm)
        · intro h
          rw [h, map_one]
      refine ⟨hm, hmst, ?_⟩
      rw [hWbot, hstab]
      exact Subgroup.mem_top _
  · constructor
    · rintro ⟨hm, hh, he⟩
      have hm₁ : m ∈ stabTil V₁ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer hMnorm₁ hm
      have he' : actTil V₁ V hV ⟨m, hm₁⟩ ∈ stabSub (wStar D.M V₀ V hV L) := by
        simpa using he
      have heinv : (actTil V₁ V hV ⟨m, hm₁⟩)⁻¹ ∈ stabSub (wStar D.M V₀ V hV L) :=
        Subgroup.inv_mem _ he'
      have hWm : imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m) =
          wStar D.M V₀ V hV L := by
        rw [s15_Infra_imgTil_conjSubgroup V₁ V (wSub V₀ V hV L) hV hm₁]
        exact (s15_Lin_map_eq_iff_mem_stabSub _ _).mpr heinv
      have h1 : imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m) =
          imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) (1 : G)) := by
        rw [conjSubgroup_one]
        exact hWm
      have hK := (s15_Core_imgTil_wSub_conj_eq_iff h hL hm D.M.one_mem).mp h1
      exact (s15_Infra_mem_nBar_iff h.hyp125 hV hm).2
        (by simpa only [conjSubgroup_one] using hK)
    · intro hm
      have hmM : m ∈ D.M := ((mem_preBarSub D.M V₀ V hV _).1 hm).1
      have hm₁ : m ∈ stabTil V₁ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer hMnorm₁ hmM
      have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L :=
        (s15_Infra_mem_nBar_iff h.hyp125 hV hmM).1 hm
      have hK1 : barSub V₀ V hV (conjSubgroup L m) =
          barSub V₀ V hV (conjSubgroup L (1 : G)) := by
        simpa only [conjSubgroup_one] using hK
      have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV L := by
        have h1 := (s15_Core_wTil_conj_eq_iff h hL hmM D.M.one_mem).mpr hK1
        simpa only [conjSubgroup_one] using h1
      have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV L := by
        rw [wSub, wSub, hWt]
      have hconjW : conjSubgroup (wSub V₀ V hV L) m = wSub V₀ V hV L := by
        rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hmM)]
        exact hsub
      have hWst : imgTil V₁ V hV (conjSubgroup (wSub V₀ V hV L) m) =
          wStar D.M V₀ V hV L := by
        rw [hconjW, wStar]
      have he : actTil V₁ V hV ⟨m, hm₁⟩ ∈ stabSub (wStar D.M V₀ V hV L) := by
        have h1 : (actTil V₁ V hV ⟨m, hm₁⟩)⁻¹ ∈ stabSub (wStar D.M V₀ V hV L) := by
          apply (s15_Lin_map_eq_iff_mem_stabSub _ _).mp
          rw [wStar, ← s15_Infra_imgTil_conjSubgroup V₁ V (wSub V₀ V hV L) hV hm₁]
          exact hWst
        exact Subgroup.inv_mem _ h1
      exact ⟨hmM, hm₁, he⟩

theorem s15_Core_s15_eq_ncard_range {D : Data G} {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    s15 D.M V₀ V h.isElemAbelian L =
      (Set.range fun m : D.M =>
        barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))).ncard := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hset : {X : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) |
      ∃ φ ∈ Mbar D.M V₀ V h.isElemAbelian,
        X = (barSub V₀ V h.isElemAbelian L).map (MulAut.conj φ).toMonoidHom} =
      Set.range (fun m : D.M =>
        barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) := by
    ext X
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V h.isElemAbelian D.M φ).1 hφ
      have hgm : (g : G)⁻¹ ∈ stabTil V₀ V := (stabTil _ _).inv_mem g.2
      have hgt : actTil V₀ V h.isElemAbelian ⟨(g : G)⁻¹, hgm⟩ =
          (actTil V₀ V h.isElemAbelian g)⁻¹ := by
        rw [show (⟨(g : G)⁻¹, hgm⟩ : stabTil V₀ V) = ⟨g, g.2⟩⁻¹ from rfl, map_inv]
      refine ⟨⟨(g : G)⁻¹, D.M.inv_mem hgM⟩, ?_⟩
      change barSub V₀ V h.isElemAbelian (conjSubgroup L (g : G)⁻¹) =
        (barSub V₀ V h.isElemAbelian L).map (MulAut.conj φ).toMonoidHom
      rw [← hgφ, s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian hgm L]
      congr 1
      rw [hgt, inv_inv]
    · rintro ⟨m, rfl⟩
      have hm : (m : G) ∈ stabTil V₀ V := hMs m.2
      refine ⟨(actTil V₀ V h.isElemAbelian ⟨(m : G), hm⟩)⁻¹, ?_, ?_⟩
      · exact Subgroup.inv_mem _ (actTil_mem_barSub V₀ V h.isElemAbelian m.2 hm)
      · exact s15_Infra_barSub_conjSubgroup V₀ V h.isElemAbelian hm L
  unfold s15
  rw [hset]

theorem ncard_wStarConj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    (wStarConj D.M V₀ V hV L).ncard = s15 D.M V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  by_cases hL : barSub V₀ V hV L = ⊥
  · have hrange : (Set.range fun m : D.M =>
        barSub V₀ V hV (conjSubgroup L (m : G))) = {⊥} := by
      ext X
      constructor
      · rintro ⟨m, rfl⟩
        exact (s15_Core_barSub_conj_eq_bot_iff h m.2).2 hL
      · intro hX
        rw [Set.mem_singleton_iff] at hX
        refine ⟨1, ?_⟩
        rw [hX]
        change barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G)) = ⊥
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
        exact hL
    have hrangeW : wStarConj D.M V₀ V hV L = {⊥} := by
      ext X
      constructor
      · rintro ⟨m, hm, rfl⟩
        rw [Set.mem_singleton_iff]
        refine s15_Core_imgTil_eq_bot_of_le hV ?_
        rw [s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL,
          conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp125.pairFacts.le_normalizer₀ hm)]
        exact s15_Infra_le_v1Sub D.M V₀ V hV L
      · intro hX
        rw [Set.mem_singleton_iff] at hX
        refine ⟨1, D.M.one_mem, ?_⟩
        rw [hX]
        show (⊥ : Subgroup (vStar D.M V₀ V hV L)) =
          imgTil (v1Sub D.M V₀ V hV L) V hV
            (conjSubgroup (wSub V₀ V hV L) ((1 : D.M) : G))
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one,
          s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL]
        exact (s15_Core_imgTil_eq_bot_of_le (V₀ := v1Sub D.M V₀ V hV L) (V := V) hV
          (s15_Infra_le_v1Sub D.M V₀ V hV L)).symm
    simp only [hrangeW, Set.ncard_singleton, s15_Core_s15_eq_ncard_range h, hrange]
  · have hrangeW : wStarConj D.M V₀ V hV L = Set.range (fun m : D.M =>
        imgTil (v1Sub D.M V₀ V hV L) V hV (conjSubgroup (wSub V₀ V hV L) (m : G))) := by
      ext X
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
      · rintro ⟨m, rfl⟩
        exact ⟨m, m.2, rfl⟩
    rw [hrangeW, s15_Core_ncard_range_eq
      (f := fun m : D.M => imgTil (v1Sub D.M V₀ V hV L) V hV
        (conjSubgroup (wSub V₀ V hV L) (m : G)))
      (g := fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))
      (fun a b => s15_Core_imgTil_wSub_conj_eq_iff h hL a.2 b.2)]
    exact (s15_Core_s15_eq_ncard_range h).symm

theorem ncard_wConj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) :
    (wConj D.M V₀ V hV L).ncard = s15 D.M V₀ V hV L := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  by_cases hL : barSub V₀ V hV L = ⊥
  · have hrange : (Set.range fun m : D.M =>
        barSub V₀ V hV (conjSubgroup L (m : G))) = {⊥} := by
      ext X
      constructor
      · rintro ⟨m, rfl⟩
        exact (s15_Core_barSub_conj_eq_bot_iff h m.2).2 hL
      · intro hX
        rw [Set.mem_singleton_iff] at hX
        refine ⟨1, ?_⟩
        rw [hX]
        change barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G)) = ⊥
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
        exact hL
    have hrangeW : wConj D.M V₀ V hV L = {V₀} := by
      ext X
      constructor
      · rintro ⟨m, hm, rfl⟩
        rw [Set.mem_singleton_iff]
        rw [s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL,
          conjSubgroup_eq_iff_mem_normalizer.mpr (h.hyp125.pairFacts.le_normalizer₀ hm)]
      · intro hX
        rw [Set.mem_singleton_iff] at hX
        refine ⟨1, D.M.one_mem, ?_⟩
        rw [hX]
        change V₀ = conjSubgroup (wSub V₀ V hV L) ((1 : D.M) : G)
        rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one,
          s15_Infra_wSub_eq_of_barSub_eq_bot h.hyp125 hV hL]
    simp only [hrangeW, Set.ncard_singleton, s15_Core_s15_eq_ncard_range h, hrange]
  · have hrangeW : wConj D.M V₀ V hV L = Set.range (fun m : D.M =>
        conjSubgroup (wSub V₀ V hV L) (m : G)) := by
      ext X
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, hm⟩, rfl⟩
      · rintro ⟨m, rfl⟩
        exact ⟨m, m.2, rfl⟩
    rw [hrangeW, s15_Core_ncard_range_eq
      (f := fun m : D.M => conjSubgroup (wSub V₀ V hV L) (m : G))
      (g := fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G)))
      (fun a b => by
        constructor
        · intro hconj
          have hsub : wSub V₀ V hV (conjSubgroup L (a : G)) =
              wSub V₀ V hV (conjSubgroup L (b : G)) := by
            rw [s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs a.2),
              s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs b.2)]
            exact hconj
          have hWt : wTil V₀ V hV (conjSubgroup L (a : G)) =
              wTil V₀ V hV (conjSubgroup L (b : G)) := by
            have h1 : imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (a : G))) =
                imgTil V₀ V hV (wSub V₀ V hV (conjSubgroup L (b : G))) := by rw [hsub]
            rwa [wSub, wSub, imgTil_preTil, imgTil_preTil] at h1
          exact (s15_Core_wTil_conj_eq_iff h hL a.2 b.2).mp hWt
        · intro hK
          have hWt : wTil V₀ V hV (conjSubgroup L (a : G)) =
              wTil V₀ V hV (conjSubgroup L (b : G)) :=
            (s15_Core_wTil_conj_eq_iff h hL a.2 b.2).mpr hK
          have hsub : wSub V₀ V hV (conjSubgroup L (a : G)) =
              wSub V₀ V hV (conjSubgroup L (b : G)) := by
            rw [wSub, wSub, hWt]
          rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs a.2),
            ← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs b.2)]
          exact hsub)]
    exact (s15_Core_s15_eq_ncard_range h).symm

theorem mem_v1Sub_of_commutator_mem (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) {w : G}
    (hw : w ∈ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L)
    (hxw : x * w * x⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L) : w ∈ v1Sub D.M V₀ V hV L := by
  have hL : barSub V₀ V hV L ≠ ⊥ := by
    intro hbot
    apply hxn
    rw [s15_Infra_nBar_eq_of_barSub_eq_bot h.hyp125 hV hbot]
    exact hx
  have hWV : w ∈ V :=
    (sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp125 hV)) hw
  set z : IntMod V hV := IntMod.mk hV ⟨w, hWV⟩ with hzdef
  set wstar : vStar D.M V₀ V hV L :=
    mkTil (v1Sub D.M V₀ V hV L) V hV z with hwdef
  have hxst : x ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV) hx
  have hw_mem : wstar ∈ wStar D.M V₀ V hV L := by
    have h1 : wstar ∈ imgTil (v1Sub D.M V₀ V hV L) V hV
        (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) :=
      (mem_imgTil (v1Sub D.M V₀ V hV L) V hV _ z).2 ⟨z, hw, rfl⟩
    rw [s15_Core_imgTil_sup (V₀ := v1Sub D.M V₀ V hV L) (V := V)
      (A := wSub V₀ V hV L) (B := v1Sub D.M V₀ V hV L) hV
      (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp125 hV),
      s15_Core_imgTil_eq_bot_of_le hV le_rfl, sup_bot_eq] at h1
    rwa [← wStar] at h1
  have hfixw : actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, hxst⟩ wstar = wstar := by
    rw [hwdef, actTil_mk, mkTil_eq_iff, actStab_apply_val]
    show x * w * x⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L
    exact hxw
  have hxinv : (x : G)⁻¹ ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    (stabTil _ _).inv_mem hxst
  have hw_x : wstar ∈ imgTil (v1Sub D.M V₀ V hV L) V hV
      (conjSubgroup (wSub V₀ V hV L) (x : G)⁻¹) := by
    have h1 : wstar ∈ (wStar D.M V₀ V hV L).map
        (actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, hxst⟩).toMonoidHom := by
      have h2 := Subgroup.mem_map_of_mem
        (actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, hxst⟩).toMonoidHom hw_mem
      simpa only [MulEquiv.coe_toMonoidHom, hfixw] using h2
    have hEq : (wStar D.M V₀ V hV L).map
        (actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, hxst⟩).toMonoidHom =
        imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (x : G)⁻¹) := by
      have hxinv_eq : actTil (v1Sub D.M V₀ V hV L) V hV ⟨(x : G)⁻¹, hxinv⟩ =
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, hxst⟩)⁻¹ := by
        rw [show (⟨(x : G)⁻¹, hxinv⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
          ⟨x, hxst⟩⁻¹ from rfl, map_inv]
      rw [s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hxinv]
      congr 1
      rw [hxinv_eq, inv_inv]
    rwa [hEq] at h1
  have hxn' : (x : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
    simpa only [inv_mem_iff] using hxn
  have hKne : barSub V₀ V hV (conjSubgroup L (x : G)⁻¹) ≠ barSub V₀ V hV L := by
    intro heq
    apply hxn'
    rwa [s15_Infra_mem_nBar_iff h.hyp125 hV (D.M.inv_mem hx)]
  have hwbot : wstar ∈ imgTil (v1Sub D.M V₀ V hV L) V hV
        (conjSubgroup (wSub V₀ V hV L) ((1 : D.M) : G)) ⊓
      ⨆ (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
          barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G))),
        imgTil (v1Sub D.M V₀ V hV L) V hV
          (conjSubgroup (wSub V₀ V hV L) (m' : G)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]
      exact hw_mem
    · refine le_iSup₂ (f := fun (m' : D.M) (_ : barSub V₀ V hV (conjSubgroup L (m' : G)) ≠
          barSub V₀ V hV (conjSubgroup L ((1 : D.M) : G))) =>
          imgTil (v1Sub D.M V₀ V hV L) V hV
            (conjSubgroup (wSub V₀ V hV L) (m' : G))) ⟨x⁻¹, D.M.inv_mem hx⟩
        (by simpa only [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one] using hKne)
        hw_x
  have hbot := s15_Core_inf_iSup_imgTil_wSub_eq_bot h hL (1 : D.M)
  have hwstar1 : wstar = 1 := by
    rw [hbot] at hwbot
    exact Subgroup.mem_bot.mp hwbot
  have h1 : mkTil (v1Sub D.M V₀ V hV L) V hV z = 1 := by
    rw [← hwdef]
    exact hwstar1
  rw [← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV), mkTil_eq_iff] at h1
  have h1' : z.val * (1 : IntMod V hV).val⁻¹ = w := by
    rw [hzdef]
    simp only [IntMod.val_one, inv_one, mul_one]
    rfl
  rw [h1'] at h1
  exact h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
