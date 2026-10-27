module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeAbs
import CFSG.GroupTheory.Fitting.MulEquiv
import CFSG.Quasithin.Background.D216Restrict
import CFSG.Quasithin.EmptyFaithful.S146zUG1Core
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Generic

variable {W : Type} [CommGroup W]

theorem s15_Three_autSub_zpowers {x : MulAut W} {U : Subgroup W} (hx : x ∈ stabSub U) :
    autSub (Subgroup.zpowers x) U = Subgroup.zpowers (resHom U ⟨x, hx⟩) := by
  ext φ
  rw [mem_autSub, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, ?_⟩
    have hgn : g = (⟨x, hx⟩ : stabSub U) ^ n :=
      Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
    rw [hgn, map_zpow]
  · rintro ⟨n, rfl⟩
    refine ⟨(⟨x, hx⟩ : stabSub U) ^ n, ?_, ?_⟩
    · rw [Subgroup.coe_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) n
    · rw [map_zpow]

theorem s15_Three_inducesTransvection_resHom {U : Subgroup W} {φ : MulAut W}
    (hφ : InducesTransvection φ U) :
    InducesTransvection (resHom U ⟨φ, hφ.1⟩) (⊤ : Subgroup ↥U) := by
  refine ⟨fun u => Iff.rfl, ?_⟩
  have h1 := commSub_eq_map_commV (U := U) (A := Subgroup.zpowers φ)
    ((Subgroup.zpowers_le).2 hφ.1)
  rw [s15_Three_autSub_zpowers hφ.1] at h1
  have h2 := hφ.2
  rw [h1] at h2
  unfold rk at h2 ⊢
  rw [Subgroup.card_map_of_injective U.subtype_injective] at h2
  rwa [← commV_eq_commSub]

theorem s15_Three_fstar_of_mulEquiv {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (e : ↥A ≃* ↥B) (h : Fstar A = A) : Fstar B = B := by
  have hA : CFSG.generalizedFitting ↥A = ⊤ := by
    unfold Fstar at h
    rw [CFSG.Adapters.genFittingFStar_eq_foundations] at h
    apply Subgroup.map_injective A.subtype_injective
    rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hB : CFSG.generalizedFitting ↥B = ⊤ := by
    rw [← CFSG.WholeGroup.generalizedFitting_map_mulEquiv e, hA]
    exact Subgroup.map_top_of_surjective _ e.surjective
  unfold Fstar
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hB, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem s15_Three_twoCoreTrivial_of_mulEquiv {W' : Type} [CommGroup W']
    {A : Subgroup (MulAut W)} {B : Subgroup (MulAut W')} (e : ↥A ≃* ↥B)
    (h : s15TwoCoreTrivial A) : s15TwoCoreTrivial B := by
  intro P hPn hP2
  have hinj : Function.Injective (e.toMonoidHom.subgroupComap P) := fun x y hxy =>
    Subtype.ext (e.injective (congrArg Subtype.val hxy))
  have hcp : IsPGroup 2 ↥(P.comap e.toMonoidHom) := hP2.of_injective _ hinj
  have hbot := h (P.comap e.toMonoidHom) (hPn.comap e.toMonoidHom) hcp
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hmem : e.symm x ∈ P.comap e.toMonoidHom := by
    rw [Subgroup.mem_comap]
    simpa using hx
  rw [hbot, Subgroup.mem_bot] at hmem
  simpa using congrArg e hmem

end Generic

section Bridge

variable {D : Data G} {V₀ V L : Subgroup G}

theorem s15_Three_nBar_le_M (h : Hyp151 D V₀ V L) : nBar D.M V₀ V h.isElemAbelian L ≤ D.M :=
  inf_le_left

theorem s15_Three_M_le_stabTil (h : Hyp151 D V₀ V L) : D.M ≤ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀

theorem s15_Three_M_le_stabTil_star (h : Hyp151 D V₀ V L) :
    D.M ≤ stabTil (v1Sub D.M V₀ V h.isElemAbelian L) V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer
    (s15_Infra_le_normalizer_v1Sub h.hyp125 h.isElemAbelian)

@[expose] noncomputable def s15Psi (h : Hyp151 D V₀ V L) :
    ↥(nBar D.M V₀ V h.isElemAbelian L) →* MulAut (Vtil V₀ V h.isElemAbelian) :=
  (actTil V₀ V h.isElemAbelian).comp
    (Subgroup.inclusion ((s15_Three_nBar_le_M h).trans (s15_Three_M_le_stabTil h)))

@[expose] noncomputable def s15PsiStar (h : Hyp151 D V₀ V L) :
    ↥(nBar D.M V₀ V h.isElemAbelian L) →* MulAut (vStar D.M V₀ V h.isElemAbelian L) :=
  (actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian).comp
    (Subgroup.inclusion ((s15_Three_nBar_le_M h).trans (s15_Three_M_le_stabTil_star h)))

theorem s15PsiStar_mem_stabSub (h : Hyp151 D V₀ V L)
    (g : ↥(nBar D.M V₀ V h.isElemAbelian L)) :
    s15PsiStar h g ∈ stabSub (wStar D.M V₀ V h.isElemAbelian L) := by
  have hg : (g : G) ∈ preBarSub D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (stabSub (wStar D.M V₀ V h.isElemAbelian L)) := by
    rw [preBarSub_stabSub_wStar D h h.isElemAbelian]
    exact g.2
  obtain ⟨-, hst, hmem⟩ := (mem_preBarSub _ _ _ _ _).1 hg
  exact hmem

@[expose] noncomputable def s15Phi (h : Hyp151 D V₀ V L) :
    ↥(nBar D.M V₀ V h.isElemAbelian L) →* MulAut ↥(wStar D.M V₀ V h.isElemAbelian L) :=
  (resHom (wStar D.M V₀ V h.isElemAbelian L)).comp
    ((s15PsiStar h).codRestrict (stabSub (wStar D.M V₀ V h.isElemAbelian L))
      (s15PsiStar_mem_stabSub h))

@[expose] noncomputable def s15AW (h : Hyp151 D V₀ V L) :
    Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) :=
  autSub (lStar D.M V₀ V h.isElemAbelian L) (wStar D.M V₀ V h.isElemAbelian L)

@[expose] noncomputable def s15NW (h : Hyp151 D V₀ V L) :
    Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) :=
  autSub (Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian)
    (wStar D.M V₀ V h.isElemAbelian L)

theorem s15_Three_AW_le_NW (h : Hyp151 D V₀ V L) : s15AW h ≤ s15NW h :=
  autSub_mono (barSub_mono (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian h.le) _

theorem s15_Three_L_le_nBar (h : Hyp151 D V₀ V L) : L ≤ nBar D.M V₀ V h.isElemAbelian L := by
  intro g hgL
  have hgM : g ∈ D.M := h.le hgL
  rw [s15_Infra_mem_nBar_iff h.hyp125 h.isElemAbelian hgM,
    conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer hgL)]

theorem s15_Three_AW_eq (h : Hyp151 D V₀ V L) :
    s15AW h = (L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)).map (s15Phi h) := by
  ext a
  rw [s15AW, mem_autSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', rfl⟩
    obtain ⟨x, hxL, hx⟩ := (mem_barSub _ _ _ _ _).1 hg'
    refine ⟨⟨(x : G), s15_Three_L_le_nBar h hxL⟩, hxL, ?_⟩
    change resHom _ _ = resHom _ g'
    congr 1
    exact Subtype.ext hx
  · rintro ⟨g, hgL, rfl⟩
    refine ⟨(s15PsiStar h).codRestrict _ (s15PsiStar_mem_stabSub h) g, ?_, rfl⟩
    exact actTil_mem_barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian hgL
      (s15_Three_M_le_stabTil_star h (s15_Three_nBar_le_M h g.2))

theorem s15_Three_NW_eq (h : Hyp151 D V₀ V L) : s15NW h = (s15Phi h).range := by
  ext a
  rw [s15NW, mem_autSub, MonoidHom.mem_range]
  constructor
  · rintro ⟨g', hg'M, rfl⟩
    obtain ⟨x, hxM, hx⟩ := (mem_barSub _ _ _ _ _).1 hg'M
    have hxn : (x : G) ∈ nBar D.M V₀ V h.isElemAbelian L := by
      rw [← preBarSub_stabSub_wStar D h h.isElemAbelian, mem_preBarSub]
      refine ⟨hxM, x.2, ?_⟩
      have : actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian ⟨(x : G), x.2⟩ =
          (g' : MulAut _) := hx
      rw [this]
      exact g'.2
    refine ⟨⟨(x : G), hxn⟩, ?_⟩
    change resHom _ _ = resHom _ g'
    congr 1
    exact Subtype.ext hx
  · rintro ⟨g, rfl⟩
    refine ⟨(s15PsiStar h).codRestrict _ (s15PsiStar_mem_stabSub h) g, ?_, rfl⟩
    exact actTil_mem_barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (s15_Three_nBar_le_M h g.2) (s15_Three_M_le_stabTil_star h (s15_Three_nBar_le_M h g.2))

theorem s15_Three_ker_psi_eq (h1217 : R1217 D) (h : Hyp151 D V₀ V L) :
    (s15Psi h).ker = (s15PsiStar h).ker := by
  have hV := h.isElemAbelian
  have hM := h.hyp125.pairFacts.le_normalizer
  have hc := fifteen_two_cent D h1217 h hV
  ext g
  have key : ∀ (W₀ : Subgroup G) (hs : D.M ≤ stabTil W₀ V),
      actTil W₀ V hV (Subgroup.inclusion ((s15_Three_nBar_le_M h).trans hs) g) = 1 ↔
        (g : G) ∈ F11.CTilde D.M W₀ V := by
    intro W₀ hs
    rw [mem_cTilde_iff hV hM]
    constructor
    · intro h1
      exact ⟨s15_Three_nBar_le_M h g.2, hs (s15_Three_nBar_le_M h g.2), h1⟩
    · rintro ⟨-, hst, h1⟩
      exact h1
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change actTil V₀ V hV (Subgroup.inclusion _ g) = 1 ↔
    actTil (v1Sub D.M V₀ V hV L) V hV (Subgroup.inclusion _ g) = 1
  rw [key V₀ (s15_Three_M_le_stabTil h), key _ (s15_Three_M_le_stabTil_star h), hc]

theorem s15_Three_ker_psi_le_phi (h1217 : R1217 D) (h : Hyp151 D V₀ V L) :
    (s15Psi h).ker ≤ (s15Phi h).ker := by
  intro g hg
  rw [s15_Three_ker_psi_eq h1217 h, MonoidHom.mem_ker] at hg
  rw [MonoidHom.mem_ker]
  change resHom _ ((s15PsiStar h).codRestrict _ (s15PsiStar_mem_stabSub h) g) = 1
  have : (s15PsiStar h).codRestrict (stabSub (wStar D.M V₀ V h.isElemAbelian L))
      (s15PsiStar_mem_stabSub h) g = 1 := Subtype.ext hg
  rw [this, map_one]

theorem s15_Three_wStar_exp (h : Hyp151 D V₀ V L) :
    ∀ w : ↥(wStar D.M V₀ V h.isElemAbelian L), w ^ 2 = 1 := by
  intro w
  apply Subtype.ext
  exact s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian w.1

theorem s15_Three_psi_mem_normalizer (h : Hyp151 D V₀ V L)
    (g : ↥(nBar D.M V₀ V h.isElemAbelian L)) :
    s15Psi h g ∈ normalizer
      ((barSub V₀ V h.isElemAbelian L : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))) :
        Set _) := by
  obtain ⟨-, hst, hmem⟩ := (mem_preBarSub _ _ _ _ _).1 g.2
  exact hmem

theorem s15_Three_psi_mem_barSub (h : Hyp151 D V₀ V L)
    (l : ↥(nBar D.M V₀ V h.isElemAbelian L)) (hl : (l : G) ∈ L) :
    s15Psi h l ∈ barSub V₀ V h.isElemAbelian L :=
  actTil_mem_barSub V₀ V h.isElemAbelian hl (s15_Three_M_le_stabTil h (h.le hl))

theorem s15_Three_exists_mem_L (h : Hyp151 D V₀ V L)
    {x : MulAut (Vtil V₀ V h.isElemAbelian)} (hx : x ∈ barSub V₀ V h.isElemAbelian L) :
    ∃ l : ↥(nBar D.M V₀ V h.isElemAbelian L), (l : G) ∈ L ∧ s15Psi h l = x := by
  obtain ⟨g, hgL, rfl⟩ := (mem_barSub _ _ _ _ _).1 hx
  exact ⟨⟨(g : G), s15_Three_L_le_nBar h hgL⟩, hgL, rfl⟩

theorem s15_Three_conj_mem_AW (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {n a : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)}
    (hn : n ∈ s15NW h) (ha : a ∈ s15AW h) : n * a * n⁻¹ ∈ s15AW h := by
  rw [s15_Three_NW_eq] at hn
  rw [s15_Three_AW_eq] at ha ⊢
  obtain ⟨g, rfl⟩ := hn
  obtain ⟨l, hl, rfl⟩ := ha
  have hlL : (l : G) ∈ L := hl
  have hnorm := s15_Three_psi_mem_normalizer h g
  have hl' := s15_Three_psi_mem_barSub h ⟨(l : G), l.2⟩ hlL
  have hconj : s15Psi h (g * ⟨(l : G), l.2⟩ * g⁻¹) ∈ barSub V₀ V h.isElemAbelian L := by
    rw [map_mul, map_mul, map_inv]
    have := (Subgroup.mem_normalizer_iff.1 hnorm (s15Psi h ⟨(l : G), l.2⟩)).1 hl'
    simpa [mul_assoc] using this
  obtain ⟨l', hl'L, hl'eq⟩ := s15_Three_exists_mem_L h hconj
  refine ⟨l', hl'L, ?_⟩
  have hker : g * l * g⁻¹ * l'⁻¹ ∈ (s15Psi h).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hl'eq]
    simp
  have := s15_Three_ker_psi_le_phi h1217 h hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
  simpa [map_mul, map_inv] using this.symm

theorem s15_Three_NW_normalizes (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    {n : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)} (hn : n ∈ s15NW h)
    (a : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) :
    a ∈ s15AW h ↔ n * a * n⁻¹ ∈ s15AW h := by
  refine ⟨fun ha => s15_Three_conj_mem_AW h1217 h hn ha, fun ha => ?_⟩
  have := s15_Three_conj_mem_AW h1217 h ((s15NW h).inv_mem hn) ha
  simpa [mul_assoc] using this

private theorem s15_Three_commSub_le_fixV_of_commSub_le_fixV {W : Type} [CommGroup W]
    {A B : Subgroup (MulAut W)} (hab : ⁅A, B⁆ = ⊥) (hAB : commSub ⊤ A ≤ fixV B) :
    commSub ⊤ B ≤ fixV A := by
  rw [commSub, Subgroup.closure_le]
  rintro c ⟨b, hb, v, -, rfl⟩
  refine mem_fixV.mpr fun a ha => ?_
  refine CFSG.Quasithin.S146zU.UG1.fix_swap (a := b) (b := a) ?_ ?_ v
  · have hmem : ⁅b, a⁆ ∈ ⁅A, B⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb ha
    rw [hab, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  · intro y
    exact mem_fixV.mp (hAB (Subgroup.subset_closure ⟨a, ha, y, Subgroup.mem_top y, rfl⟩)) b hb

private theorem s15_Three_wStar_le_fixV_zpowers_psiStar {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (g : ↥(nBar D.M V₀ V h.isElemAbelian L))
    (hg : s15Phi h g = 1) :
    wStar D.M V₀ V h.isElemAbelian L ≤
      fixV (Subgroup.zpowers (s15PsiStar h g)) := by
  intro u hu
  rw [mem_fixV_zpowers]
  have h1 := congrArg (fun φ : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L) =>
    (φ ⟨u, hu⟩ : vStar D.M V₀ V h.isElemAbelian L)) hg
  rw [MulAut.one_apply] at h1
  simpa only [s15Phi, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, resHom_apply,
    Subtype.coe_mk] using h1

private theorem s15_Three_wStarConj_nBar {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) {m : G} (hmM : m ∈ D.M)
    (hmn : m ∈ nBar D.M V₀ V h.isElemAbelian L) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) m) =
      wStar D.M V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hK : barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L :=
    (s15_Infra_mem_nBar_iff h.hyp125 hV hmM).1 hmn
  have hWt : wTil V₀ V hV (conjSubgroup L m) = wTil V₀ V hV L := by
    have h1 := (s15_Core_wTil_conj_eq_iff h hL hmM D.M.one_mem).mpr
      (by simpa only [conjSubgroup_one] using hK)
    simpa only [conjSubgroup_one] using h1
  have hsub : wSub V₀ V hV (conjSubgroup L m) = wSub V₀ V hV L := by
    rw [wSub, wSub, hWt]
  rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hmM), hsub]
  rfl

private theorem s15_Three_psiStar_fix_of_psi_fix {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (g : ↥(nBar D.M V₀ V h.isElemAbelian L))
    (hgL : (g : G) ∈ L) {m : G}
    (hfix : imgTil V₀ V h.isElemAbelian (conjSubgroup (wSub V₀ V h.isElemAbelian L) m) ≤
      fixV (barSub V₀ V h.isElemAbelian L)) :
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) m) ≤
      fixV (Subgroup.zpowers (s15PsiStar h g)) := by
  have hV := h.isElemAbelian
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hMs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := s15_Three_M_le_stabTil_star h
  have hgM : (g : G) ∈ D.M := s15_Three_nBar_le_M h g.2
  have hgs₀ : (g : G) ∈ stabTil V₀ V := hMs₀ hgM
  have hgs₁ : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := hMs₁ hgM
  intro q hq
  rw [mem_fixV_zpowers]
  obtain ⟨x, hx, hxq⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV _ q).1 hq
  rw [← hxq]
  have hx0 : mkTil V₀ V hV x ∈
      imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m) :=
    (mem_imgTil V₀ V hV _ x).2 ⟨x, hx, rfl⟩
  have hpsi₀ : s15Psi h g (mkTil V₀ V hV x) = mkTil V₀ V hV x :=
    mem_fixV.mp (hfix hx0) (s15Psi h g) (s15_Three_psi_mem_barSub h g hgL)
  have hact₀ : actTil V₀ V hV ⟨(g : G), hgs₀⟩ (mkTil V₀ V hV x) = mkTil V₀ V hV x := by
    rw [show (⟨(g : G), hgs₀⟩ : stabTil V₀ V) =
        Subgroup.inclusion ((s15_Three_nBar_le_M h).trans (s15_Three_M_le_stabTil h)) g from
      Subtype.ext rfl]
    exact hpsi₀
  have hmem₀ : (actStab V₀ V hV ⟨(g : G), hgs₀⟩ x).val * x.val⁻¹ ∈ V₀ := by
    have h1 : mkTil V₀ V hV (actStab V₀ V hV ⟨(g : G), hgs₀⟩ x) = mkTil V₀ V hV x := by
      rw [← actTil_mk]
      exact hact₀
    exact (mkTil_eq_iff V₀ V hV _ _).1 h1
  have hmem₁ : (actStab (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), hgs₁⟩ x).val * x.val⁻¹ ∈
      v1Sub D.M V₀ V hV L := by
    have h0 := hmem₀
    rw [actStab_apply_val] at h0
    rw [actStab_apply_val]
    exact s15_Infra_le_v1Sub D.M V₀ V hV L h0
  have h2 : actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), hgs₁⟩
      (mkTil (v1Sub D.M V₀ V hV L) V hV x) = mkTil (v1Sub D.M V₀ V hV L) V hV x := by
    rw [actTil_mk, mkTil_eq_iff]
    exact hmem₁
  have hge₁ : s15PsiStar h g =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), hgs₁⟩ := by
    rw [show (⟨(g : G), hgs₁⟩ : stabTil (v1Sub D.M V₀ V hV L) V) =
        Subgroup.inclusion ((s15_Three_nBar_le_M h).trans
          (s15_Three_M_le_stabTil_star h)) g from Subtype.ext rfl]
    rfl
  rw [hge₁]
  exact h2

private theorem s15_Three_psiStar_eq_one_of_family_fix {D : Data G} {V₀ V L : Subgroup G}
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (g : ↥(nBar D.M V₀ V h.isElemAbelian L))
    (hfix : ∀ m : D.M, imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) (m : G)) ≤
      fixV (Subgroup.zpowers (s15PsiStar h g))) :
    s15PsiStar h g = 1 := by
  have hV := h.isElemAbelian
  have htop : (⊤ : Subgroup (vStar D.M V₀ V hV L)) ≤
      fixV (Subgroup.zpowers (s15PsiStar h g)) := by
    rw [← (fifteen_two_directSum D h1217 h hV hL).2]
    refine sSup_le ?_
    intro X hX
    rw [s15_Two_wStarConj_eq_range D.M V₀ V L hV] at hX
    obtain ⟨m, rfl⟩ := hX
    exact hfix m
  refine MulEquiv.ext fun q => ?_
  simpa using mem_fixV.mp (htop (Subgroup.mem_top q)) (s15PsiStar h g)
    (Subgroup.mem_zpowers _)

theorem s15_Three_psi_eq_one_of_phi (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) (g : ↥(nBar D.M V₀ V h.isElemAbelian L))
    (hgL : (g : G) ∈ L) (hg : s15Phi h g = 1) : s15Psi h g = 1 := by
  rw [← MonoidHom.mem_ker, s15_Three_ker_psi_eq h1217 h, MonoidHom.mem_ker]
  refine s15_Three_psiStar_eq_one_of_family_fix h1217 h hL g fun m => ?_
  by_cases hmn : (m : G) ∈ nBar D.M V₀ V h.isElemAbelian L
  · rw [s15_Three_wStarConj_nBar h hL m.2 hmn]
    exact s15_Three_wStar_le_fixV_zpowers_psiStar h g hg
  · have hne : (m : G) * (1 : G)⁻¹ ∉ nBar D.M V₀ V h.isElemAbelian L := by simpa using hmn
    obtain ⟨hb1, hb2⟩ := s15_Kbar_commute_conj h D.M.one_mem m.2 hne
    have hb1' : ⁅barSub V₀ V h.isElemAbelian L,
        barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))⁆ = ⊥ := by
      simpa only [conjSubgroup_one] using hb1
    have hb2' : commSub (commSub ⊤ (barSub V₀ V h.isElemAbelian L))
        (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) = ⊥ := by
      simpa only [conjSubgroup_one] using hb2
    have hAB : commSub ⊤ (barSub V₀ V h.isElemAbelian L) ≤
        fixV (barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) :=
      commSub_eq_bot_iff.mp hb2'
    have hswap := s15_Three_commSub_le_fixV_of_commSub_le_fixV hb1' hAB
    have himg : imgTil V₀ V h.isElemAbelian
        (conjSubgroup (wSub V₀ V h.isElemAbelian L) (m : G)) =
        wTil V₀ V h.isElemAbelian (conjSubgroup L (m : G)) := by
      have hMs : D.M ≤ stabTil V₀ V :=
        le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
      rw [← s15_Infra_wSub_conjSubgroup V₀ V L h.isElemAbelian (hMs m.2), wSub, imgTil_preTil]
    exact s15_Three_psiStar_fix_of_psi_fix h g hgL (by rw [himg]; exact hswap)

@[expose] noncomputable def s15PhiL (h : Hyp151 D V₀ V L) :
    ↥(L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)) →* ↥(s15AW h) :=
  ((s15Phi h).comp (L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)).subtype).codRestrict
    (s15AW h)
    (fun x => by rw [s15_Three_AW_eq]; exact ⟨x, x.2, rfl⟩)

@[expose] noncomputable def s15PsiL (h : Hyp151 D V₀ V L) :
    ↥(L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)) →* ↥(barSub V₀ V h.isElemAbelian L) :=
  ((s15Psi h).comp (L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L)).subtype).codRestrict
    (barSub V₀ V h.isElemAbelian L)
    (fun x => s15_Three_psi_mem_barSub h (x : ↥(nBar D.M V₀ V h.isElemAbelian L)) x.2)

theorem s15_Three_psiL_surjective (h : Hyp151 D V₀ V L) : Function.Surjective (s15PsiL h) := by
  rintro ⟨y, hy⟩
  obtain ⟨l, hlL, hl⟩ := s15_Three_exists_mem_L h hy
  exact ⟨⟨l, hlL⟩, Subtype.ext hl⟩

theorem s15_Three_phiL_surjective (h : Hyp151 D V₀ V L) : Function.Surjective (s15PhiL h) := by
  rintro ⟨a, ha⟩
  rw [s15_Three_AW_eq] at ha
  obtain ⟨l, hl, rfl⟩ := ha
  exact ⟨⟨l, hl⟩, rfl⟩

theorem s15_Three_ker_psiL_le (h1217 : R1217 D) (h : Hyp151 D V₀ V L) :
    (s15PsiL h).ker ≤ (s15PhiL h).ker := by
  intro x hx
  have h1 : s15Psi h (x : ↥(nBar D.M V₀ V h.isElemAbelian L)) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have h2 := s15_Three_ker_psi_le_phi h1217 h (MonoidHom.mem_ker.2 h1)
  exact MonoidHom.mem_ker.2 (Subtype.ext (MonoidHom.mem_ker.1 h2))

theorem s15_Three_ker_phiL_le (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) : (s15PhiL h).ker ≤ (s15PsiL h).ker := by
  intro x hx
  have h1 : s15Phi h (x : ↥(nBar D.M V₀ V h.isElemAbelian L)) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  exact MonoidHom.mem_ker.2 (Subtype.ext (s15_Three_psi_eq_one_of_phi h1217 h hL x x.2 h1))

@[expose] noncomputable def s15AWHom (h1217 : R1217 D) (h : Hyp151 D V₀ V L) :
    ↥(barSub V₀ V h.isElemAbelian L) →* ↥(s15AW h) :=
  MonoidHom.liftOfSurjective (s15PsiL h) (s15_Three_psiL_surjective h)
    ⟨s15PhiL h, s15_Three_ker_psiL_le h1217 h⟩

theorem s15AWHom_apply (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (x : ↥(L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L))) :
    s15AWHom h1217 h (s15PsiL h x) = s15PhiL h x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨s15PhiL h, s15_Three_ker_psiL_le h1217 h⟩ x

theorem s15AWHom_bijective (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) : Function.Bijective (s15AWHom h1217 h) := by
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := s15_Three_psiL_surjective h y
    rw [MonoidHom.mem_ker, s15AWHom_apply] at hy
    have := s15_Three_ker_phiL_le h1217 h hL (MonoidHom.mem_ker.2 hy)
    rw [MonoidHom.mem_ker.1 this]
    exact Subgroup.one_mem _
  · intro a
    obtain ⟨x, rfl⟩ := s15_Three_phiL_surjective h a
    exact ⟨s15PsiL h x, s15AWHom_apply h1217 h x⟩

@[expose] noncomputable def s15AWEquiv (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) :
    ↥(barSub V₀ V h.isElemAbelian L) ≃* ↥(s15AW h) :=
  MulEquiv.ofBijective (s15AWHom h1217 h) (s15AWHom_bijective h1217 h hL)

theorem s15AWEquiv_apply (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (x : ↥(L.subgroupOf (nBar D.M V₀ V h.isElemAbelian L))) :
    s15AWEquiv h1217 h hL (s15PsiL h x) = s15PhiL h x :=
  s15AWHom_apply h1217 h x

theorem s15_Three_exists_transvection (h : Hyp151 D V₀ V L)
    (hφ : ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      InducesTransvection φ (wStar D.M V₀ V h.isElemAbelian L)) :
    ∃ t ∈ s15NW h, InducesTransvection t (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) := by
  obtain ⟨φ, hφM, hφ⟩ := hφ
  exact ⟨resHom _ ⟨φ, hφ.1⟩, mem_autSub.2 ⟨⟨φ, hφ.1⟩, hφM, rfl⟩,
    s15_Three_inducesTransvection_resHom hφ⟩

theorem s15_Three_fstar_AW (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) : Fstar (s15AW h) = s15AW h :=
  s15_Three_fstar_of_mulEquiv (s15AWEquiv h1217 h hL) h.fstar_eq

theorem s15_Three_twoCore_barSub (h : Hyp151 D V₀ V L) :
    s15TwoCoreTrivial (barSub V₀ V h.isElemAbelian L) := by
  set Lb := barSub V₀ V h.isElemAbelian L with hLb
  set Mb := Mbar D.M V₀ V h.isElemAbelian with hMb
  intro P hPn hP2
  have hinj : Function.Injective Lb.subtype := Lb.subtype_injective
  have hP'L : P.map Lb.subtype ≤ Lb := Subgroup.map_subtype_le P
  have hP'n : ((P.map Lb.subtype).subgroupOf Lb).Normal := by
    have : (P.map Lb.subtype).subgroupOf Lb = P := Subgroup.comap_map_eq_self_of_injective hinj P
    rw [this]
    exact hPn
  have hsub : CFSG.Open.IsSubnormal (P.map Lb.subtype) Mb :=
    CFSG.Open.IsSubnormal.step hP'L hP'n (s15_Kbar_isSubnormal_barSub h)
  have hP'2 : IsPGroup 2 ↥(P.map Lb.subtype) :=
    hP2.of_surjective (P.equivMapOfInjective Lb.subtype hinj).toMonoidHom
      (P.equivMapOfInjective Lb.subtype hinj).surjective
  have hcore := CFSG.RankThreeEvenClassification.Helpers.subnormal_pSubgroup_le_pCoreOf 2 hsub hP'2
  have hbot : CFSG.Open.pCoreOf 2 Mb = ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 Mb ≤ Mb := CFSG.LieType.BorelTits.pCoreOf_le 2 Mb
    refine s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hle ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Mb)
    exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 Mb Mb le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  rw [hbot] at hcore
  exact (Subgroup.map_eq_bot_iff_of_injective P hinj).1 (le_bot_iff.1 hcore)

theorem s15_Three_twoCore_AW (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) : s15TwoCoreTrivial (s15AW h) :=
  s15_Three_twoCoreTrivial_of_mulEquiv (s15AWEquiv h1217 h hL) (s15_Three_twoCore_barSub h)

theorem s15_Three_lStar_le_stabSub (h : Hyp151 D V₀ V L) :
    lStar D.M V₀ V h.isElemAbelian L ≤ stabSub (wStar D.M V₀ V h.isElemAbelian L) := by
  intro x hx u
  refine ⟨fun hu => ?_, fun hu => s15_Three_stableUnder_wStar h h.isElemAbelian x hx u hu⟩
  have h1 := s15_Three_stableUnder_wStar h h.isElemAbelian x⁻¹
    ((lStar D.M V₀ V h.isElemAbelian L).inv_mem hx) (x u) hu
  simpa [MulAut.inv_apply] using h1

theorem s15_Three_commSub_AW (h : Hyp151 D V₀ V L) :
    commSub (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) (s15AW h) = ⊤ := by
  have h1 := s15_Three_commSub_wStar h h.isElemAbelian
  have h2 := commSub_eq_map_commV (s15_Three_lStar_le_stabSub h)
  rw [h1] at h2
  rw [← commV_eq_commSub]
  apply Subgroup.map_injective (wStar D.M V₀ V h.isElemAbelian L).subtype_injective
  rw [s15AW, ← h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem s15_Three_abstract_AW (hMcL : RMcLaughlin) (hDer : RJPrime153) (hNorm : RNormNat153)
    (h1217 : R1217 D) (h : Hyp151 D V₀ V L) (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (hsemi : s15Semisimple (s15AW h))
    (htrans : ∀ I I' : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L),
      IsIrrOn (s15AW h) I ⊥ → IsIrrOn (s15AW h) I' ⊥ →
        ∃ n ∈ s15NW h, s15SecIso (s15AW h) (I.map (n : MulAut _).toMonoidHom) ⊥ I' ⊥)
    {t : MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)} (htN : t ∈ s15NW h)
    (ht : InducesTransvection t (⊤ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    ∃ B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)),
      B = ⁅s15AW h, Subgroup.zpowers t⁆ ∧ B ≤ s15AW h ∧
      IsDirectProdOfConj (s15AW h) B (s15NW h) ∧ s15KNat ↥B B (commSub ⊤ B) ∧
      sSupIndep {Z : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) | ∃ n ∈ s15NW h,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} ∧
      sSup {Z : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L) | ∃ n ∈ s15NW h,
        Z = commSub ⊤ (B.map (MulAut.conj n).toMonoidHom)} = ⊤ :=
  s15_Three_abstract hMcL hDer hNorm (s15_Three_wStar_exp h)
    (s15_Three_AW_le_NW h) (fun n hn a => s15_Three_NW_normalizes h1217 h hn a)
    htN ht (s15_Three_fstar_AW h1217 h hL) (s15_Three_twoCore_AW h1217 h hL)
    (s15_Three_commSub_AW h) hsemi htrans

end Bridge

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
