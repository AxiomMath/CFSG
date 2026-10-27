module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Natural

theorem s15_Four_realizes_transfer {W V : Type*} [CommGroup W] [CommGroup V] (ι : W →* V)
    (hι : Function.Injective ι) {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut V)}
    (ρ : ↥H' ≃* ↥H)
    (hρ : ∀ (k : ↥H') (w : W), ι ((ρ k : MulAut W) w) = (k : MulAut V) (ι w))
    {U Z : Subgroup W} (M : FFModel) (hM : M.Realizes H U Z) :
    M.Realizes H' (U.map ι) (Z.map ι) := by
  obtain ⟨π, hπsurj, hZU, hker, hUinv, hZinv, hsec, hkerinv, β, hβsurj, hβker, hβeq⟩ := hM
  refine ⟨ρ.symm.toMonoidHom.comp π, ρ.symm.surjective.comp hπsurj,
    Subgroup.map_mono hZU, hker, ?_, ?_, hsec, hkerinv, ?_⟩
  · rintro h u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 hu
    exact Subgroup.mem_map.2 ⟨(ρ h : MulAut W) u₀, hUinv (ρ h) u₀ hu₀, hρ h u₀⟩
  · rintro h z hz
    obtain ⟨z₀, hz₀, rfl⟩ := Subgroup.mem_map.1 hz
    exact Subgroup.mem_map.2 ⟨(ρ h : MulAut W) z₀, hZinv (ρ h) z₀ hz₀, hρ h z₀⟩
  · let e : ↥U ≃* ↥(U.map ι) := Subgroup.equivMapOfInjective U ι hι
    have he : ∀ x : ↥U, ι ((x : ↥U) : W) = ((e x : ↥(U.map ι)) : V) := fun x => by
      rw [Subgroup.coe_equivMapOfInjective_apply]
    refine ⟨β.comp e.symm.toMonoidHom, hβsurj.comp e.symm.surjective, ?_, ?_⟩
    · intro u'
      change β (e.symm u') = 1 ↔ (u' : V) ∈ Z.map ι
      rw [hβker]
      constructor
      · intro hu
        exact Subgroup.mem_map.2 ⟨e.symm u', hu, (he (e.symm u')).trans (by simp)⟩
      · rintro ⟨z, hz, hzι⟩
        have h1 : (e.symm u' : ↥U) = ⟨z, hZU hz⟩ := by
          refine Subtype.ext (hι ?_)
          rw [he (e.symm u'), MulEquiv.apply_symm_apply]
          exact hzι.symm
        rw [h1]
        exact hz
    · rintro γ u' m hu' hm hβ
      change β (e.symm u') = QuotientGroup.mk m at hβ
      change ((ρ.symm (π γ) : ↥H') : MulAut V) (u' : V) ∈ U.map ι at hu'
      have h3 : (u' : V) = ι ((e.symm u' : ↥U) : W) := by
        conv_lhs => rw [← MulEquiv.apply_symm_apply e u']
        exact (he (e.symm u')).symm
      have h1 : ((ρ.symm (π γ) : ↥H') : MulAut V) (u' : V) =
          ι (((π γ : ↥H) : MulAut W) ((e.symm u' : ↥U) : W)) := by
        have h2 := hρ (ρ.symm (π γ)) ((e.symm u' : ↥U) : W)
        rw [MulEquiv.apply_symm_apply] at h2
        rw [h3]
        exact h2.symm
      have hmem : ((π γ : ↥H) : MulAut W) ((e.symm u' : ↥U) : W) ∈ U := by
        have h4 : ι (((π γ : ↥H) : MulAut W) ((e.symm u' : ↥U) : W)) ∈ U.map ι := by
          rw [← h1]
          exact hu'
        obtain ⟨v, hv, hvι⟩ := Subgroup.mem_map.1 h4
        rwa [← hι hvι]
      have hgoal : e.symm ⟨((ρ.symm (π γ) : ↥H') : MulAut V) (u' : V), hu'⟩ =
          ⟨((π γ : ↥H) : MulAut W) ((e.symm u' : ↥U) : W), hmem⟩ := by
        refine Subtype.ext (hι ?_)
        rw [he, MulEquiv.apply_symm_apply]
        exact h1
      change β (e.symm ⟨((ρ.symm (π γ) : ↥H') : MulAut V) (u' : V), hu'⟩) =
        QuotientGroup.mk ⟨M.act γ (m : M.Amb), hm⟩
      rw [hgoal]
      exact hβeq γ (e.symm u') m hmem hm hβ

private theorem s15_Three_isLn_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {n a : ℕ} (h : IsLn X n a) : IsLn X' n a :=
  CFSG.Blueprint.LieModel.of_mulEquiv e h

private theorem s15_Three_isSpn_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {n a : ℕ} (h : IsSpn X n a) : IsSpn X' n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem s15_Three_isOmegaPlus_of_mulEquiv {X X' : Type} [Group X] [Group X']
    (e : X ≃* X') {n a : ℕ} (h : IsOmegaPlus X n a) : IsOmegaPlus X' n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem s15_Three_isOmegaMinus_of_mulEquiv {X X' : Type} [Group X] [Group X']
    (e : X ≃* X') {n a : ℕ} (h : IsOmegaMinus X n a) : IsOmegaMinus X' n a := by
  obtain ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, b, c, hcard, hq, ⟨e.symm.trans e'⟩⟩

private theorem s15_Three_isAlt_of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {n : ℕ} (h : UC22.IsAlt X n) : UC22.IsAlt X' n := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

private theorem s15_Three_cyclicOrd_of_mulEquiv {X X' : Type} [Group X] [Group X']
    (e : X ≃* X') {n : ℕ} (h : IsCyclicOrd X n) : IsCyclicOrd X' n :=
  ⟨(MulEquiv.isCyclic e).1 h.1, by rw [← Nat.card_congr e.toEquiv]; exact h.2⟩

theorem s15_Four_knat_transfer {X X' W V : Type} [Group X] [Group X'] [CommGroup W]
    [CommGroup V] (e : X ≃* X') (ι : W →* V) (hι : Function.Injective ι)
    {H : Subgroup (MulAut W)} {H' : Subgroup (MulAut V)} (ρ : ↥H' ≃* ↥H)
    (hρ : ∀ (k : ↥H') (w : W), ι ((ρ k : MulAut W) w) = (k : MulAut V) (ι w))
    {Z : Subgroup W} (hK : s15KNat X H Z) : s15KNat X' H' (Z.map ι) := by
  rcases hK with hperf | hz3
  · left
    rcases hperf with ⟨n, hn, hLn, hNat⟩ | ⟨n, hn, hSp, hNat⟩ | ⟨n, hn, hOp, hNat⟩ |
      ⟨n, hn, hOm, hNat⟩ | ⟨n, hn, hAlt, hNat⟩
    · refine Or.inl ⟨n, hn, s15_Three_isLn_of_mulEquiv e hLn, ?_⟩
      obtain ⟨K, hK, hKf, hcard, hReal⟩ := hNat
      exact ⟨K, hK, hKf, hcard, by
        have h := s15_Four_realizes_transfer ι hι ρ hρ (FFModel.nat (StatedSL n K)) hReal
        rwa [Subgroup.map_bot] at h⟩
    · refine Or.inr (Or.inl ⟨n, hn, s15_Three_isSpn_of_mulEquiv e hSp, ?_⟩)
      obtain ⟨hn', K, hK, hKf, hcard, hReal⟩ := hNat
      exact ⟨hn', K, hK, hKf, hcard, by
        have h := s15_Four_realizes_transfer ι hι ρ hρ (FFModel.nat (StatedSp (n / 2) K)) hReal
        rwa [Subgroup.map_bot] at h⟩
    · refine Or.inr (Or.inr (Or.inl ⟨n, hn, s15_Three_isOmegaPlus_of_mulEquiv e hOp, ?_⟩))
      obtain ⟨hn', K, hK, hKf, hcard, hReal⟩ := hNat
      exact ⟨hn', K, hK, hKf, hcard, by
        have h := s15_Four_realizes_transfer ι hι ρ hρ
          (FFModel.nat (StatedOmega (StatedQuadPlus (n / 2) K))) hReal
        rwa [Subgroup.map_bot] at h⟩
    · obtain ⟨hn', K, hK, hKf, b, c, hcard, hq, hReal⟩ := hNat
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn,
        s15_Three_isOmegaMinus_of_mulEquiv e hOm, hn', K, hK, hKf, b, c, hcard, hq, ?_⟩)))
      have h := s15_Four_realizes_transfer ι hι ρ hρ
        (FFModel.nat (StatedOmega (StatedQuadMinus (n / 2) K b c))) hReal
      rwa [Subgroup.map_bot] at h
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn,
        s15_Three_isAlt_of_mulEquiv e hAlt, ?_⟩)))
      have h := s15_Four_realizes_transfer ι hι ρ hρ (FFModel.altDn n) hNat
      rwa [Subgroup.map_bot] at h
  · right
    refine ⟨s15_Three_cyclicOrd_of_mulEquiv e hz3.1, ?_⟩
    have h := s15_Four_realizes_transfer ι hι ρ hρ (FFModel.altDn 3) hz3.2
    rwa [Subgroup.map_bot] at h

variable {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_Three_awEquiv_map_K0 (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h) :
    ((barSub V₀ V h.isElemAbelian (s15K0 h B)).subgroupOf
        (barSub V₀ V h.isElemAbelian L)).map (s15AWEquiv h1217 h hL).toMonoidHom =
      B.subgroupOf (s15AW h) := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (s15_Three_mem_barSub_K0_iff h1217 h hL B y).1 hy
  · intro hx
    refine ⟨(s15AWEquiv h1217 h hL).symm x, ?_, ?_⟩
    · refine (s15_Three_mem_barSub_K0_iff h1217 h hL B _).2 ?_
      rw [MulEquiv.apply_symm_apply]
      exact Subgroup.mem_subgroupOf.1 hx
    · simp

private noncomputable def s15_Three_awEquivB (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h) :
    ↥(barSub V₀ V h.isElemAbelian (s15K0 h B)) ≃* ↥B :=
  (Subgroup.subgroupOfEquivOfLe
      (barSub_mono V₀ V h.isElemAbelian (s15_Three_K0_le h B))).symm.trans
    ((Subgroup.equivMapOfInjective
        ((barSub V₀ V h.isElemAbelian (s15K0 h B)).subgroupOf (barSub V₀ V h.isElemAbelian L))
        (s15AWEquiv h1217 h hL).toMonoidHom (s15AWEquiv h1217 h hL).injective).trans
      ((MulEquiv.subgroupCongr (s15_Three_awEquiv_map_K0 h1217 h hL hBA)).trans
        (Subgroup.subgroupOfEquivOfLe hBA)))

private noncomputable def s15_Three_phiB (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    ↥(s15K0 h B) →* MulAut ↥(wStar D.M V₀ V h.isElemAbelian L) :=
  (s15Phi h).comp (Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)))

private noncomputable def s15_Three_psiStarK (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    ↥(s15K0 h B) →* MulAut (vStar D.M V₀ V h.isElemAbelian L) :=
  (s15PsiStar h).comp (Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)))

private theorem s15_Three_phiB_range (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) (hBA : B ≤ s15AW h) :
    (s15_Three_phiB h B).range = B := by
  ext b
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact (s15_Three_mem_K0 h B).1 x.2 |>.2.2
  · intro hb
    have hbA : b ∈ s15AW h := hBA hb
    rw [s15_Three_AW_eq] at hbA
    obtain ⟨l, hl, hlφ⟩ := hbA
    refine ⟨⟨(l : G), (s15_Three_mem_K0 h B).2 ⟨l.2, hl, by rw [hlφ]; exact hb⟩⟩, ?_⟩
    exact (show s15Phi h (Subgroup.inclusion ((s15_Three_K0_le h B).trans
        (s15_Three_L_le_nBar h)) ⟨(l : G), _⟩) = b by
      rw [show Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h))
          ⟨(l : G), _⟩ = l from Subtype.ext rfl, hlφ])

private theorem s15_Three_psiStarK_range (h : Hyp151 D V₀ V L)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    (s15_Three_psiStarK h B).range =
      barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B) := by
  ext φ
  rw [MonoidHom.mem_range, mem_barSub]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion
        (((s15_Three_K0_le h B).trans h.le).trans (s15_Three_M_le_stabTil_star h)) x,
      x.2, rfl⟩
  · rintro ⟨g, hgX, hgφ⟩
    refine ⟨⟨(g : G), hgX⟩, ?_⟩
    rw [← hgφ]
    exact congrArg (actTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian)
      (Subtype.ext rfl)

private theorem s15_Three_phiB_ker_eq (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))) :
    (s15_Three_phiB h B).ker = (s15_Three_psiStarK h B).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxL : ((Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)) x :
        ↥(nBar D.M V₀ V h.isElemAbelian L)) : G) ∈ L := s15_Three_K0_le h B x.2
    have hpsi := s15_Three_psi_eq_one_of_phi h1217 h hL
      (Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)) x) hxL hx
    rw [← MonoidHom.mem_ker, s15_Three_ker_psi_eq h1217 h] at hpsi
    simpa only [s15_Three_psiStarK, MonoidHom.comp_apply, MonoidHom.mem_ker] using hpsi
  · intro hx
    have hx' : (s15PsiStar h).codRestrict (stabSub (wStar D.M V₀ V h.isElemAbelian L))
        (s15PsiStar_mem_stabSub h)
        (Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)) x) = 1 :=
      Subtype.ext hx
    show resHom (wStar D.M V₀ V h.isElemAbelian L)
        ((s15PsiStar h).codRestrict (stabSub (wStar D.M V₀ V h.isElemAbelian L))
          (s15PsiStar_mem_stabSub h)
          (Subgroup.inclusion ((s15_Three_K0_le h B).trans (s15_Three_L_le_nBar h)) x)) = 1
    rw [hx', map_one]

private theorem s15_Three_quotientKerEquivRange_mk {A B : Type} [Group A] [Group B]
    (f : A →* B) (a : A) :
    QuotientGroup.quotientKerEquivRange f (QuotientGroup.mk a) =
      ⟨f a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ :=
  rfl

private theorem s15_Three_quotientMulEquivOfEq_symm_mk {A : Type} [Group A]
    {M N : Subgroup A} [M.Normal] [N.Normal] (h : M = N) (a : A) :
    (QuotientGroup.quotientMulEquivOfEq h).symm (QuotientGroup.mk a) = QuotientGroup.mk a :=
  QuotientGroup.quotientMulEquivOfEq_mk h.symm a

private noncomputable def s15_Three_rho (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h) :
    ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)) ≃* ↥B :=
  ((QuotientGroup.quotientKerEquivRange (s15_Three_psiStarK h B)).trans
      (MulEquiv.subgroupCongr (s15_Three_psiStarK_range h B))).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (s15_Three_phiB_ker_eq h1217 h hL B)).symm.trans
      ((QuotientGroup.quotientKerEquivRange (s15_Three_phiB h B)).trans
        (MulEquiv.subgroupCongr (s15_Three_phiB_range h B hBA))))

private theorem s15_Three_rho_apply (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h)
    (x : ↥(s15K0 h B)) :
    s15_Three_rho h1217 h hL hBA
        ⟨s15_Three_psiStarK h B x,
          le_of_eq (s15_Three_psiStarK_range h B) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩ =
      ⟨s15_Three_phiB h B x,
        le_of_eq (s15_Three_phiB_range h B hBA) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩ := by
  rw [s15_Three_rho]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply]
  have h1 : (MulEquiv.subgroupCongr (s15_Three_psiStarK_range h B)).symm
      ⟨s15_Three_psiStarK h B x,
        le_of_eq (s15_Three_psiStarK_range h B) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩ =
      ⟨s15_Three_psiStarK h B x, MonoidHom.mem_range.2 ⟨x, rfl⟩⟩ := Subtype.ext rfl
  rw [h1, ← s15_Three_quotientKerEquivRange_mk (s15_Three_psiStarK h B) x,
    MulEquiv.symm_apply_apply,
    s15_Three_quotientMulEquivOfEq_symm_mk (s15_Three_phiB_ker_eq h1217 h hL B) x,
    s15_Three_quotientKerEquivRange_mk]
  exact Subtype.ext rfl

private theorem s15_Three_rho_compat (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h)
    (k : ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)))
    (w : ↥(wStar D.M V₀ V h.isElemAbelian L)) :
    (wStar D.M V₀ V h.isElemAbelian L).subtype
        ((s15_Three_rho h1217 h hL hBA k :
          MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) w) =
      (k : MulAut (vStar D.M V₀ V h.isElemAbelian L))
        ((wStar D.M V₀ V h.isElemAbelian L).subtype w) := by
  obtain ⟨x, hx⟩ : ∃ x : ↥(s15K0 h B), k = ⟨s15_Three_psiStarK h B x,
      le_of_eq (s15_Three_psiStarK_range h B) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩ := by
    have hk : (k : MulAut (vStar D.M V₀ V h.isElemAbelian L)) ∈
        (s15_Three_psiStarK h B).range :=
      le_of_eq (s15_Three_psiStarK_range h B).symm k.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hk
    exact ⟨x, Subtype.ext hx.symm⟩
  rw [hx, s15_Three_rho_apply]
  rfl

private theorem s15_Three_star_fix_conj (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)))
    (x : ↥(s15K0 h B)) {Z : Subgroup (vStar D.M V₀ V h.isElemAbelian L)}
    (hZ : Z ∈ wStarConj D.M V₀ V h.isElemAbelian L)
    (hZne : Z ≠ wStar D.M V₀ V h.isElemAbelian L) :
    ∀ v ∈ Z, (s15_Three_psiStarK h B x : MulAut (vStar D.M V₀ V h.isElemAbelian L)) v = v := by
  obtain ⟨m, hm, rfl⟩ := hZ
  set Z₀ : Subgroup (vStar D.M V₀ V h.isElemAbelian L) :=
    imgTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
      (conjSubgroup (wSub V₀ V h.isElemAbelian L) (m : G)) with hZ₀
  have hV := h.isElemAbelian
  have hMs1 : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h.hyp125 hV)
  have hxL : (x : G) ∈ L := s15_Three_K0_le h B x.2
  have hgs : (x : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := hMs1 (h.le hxL)
  have hk : s15_Three_psiStarK h B x =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨(x : G), hgs⟩ := rfl
  have hkL : s15_Three_psiStarK h B x ∈ lStar D.M V₀ V hV L := by
    rw [hk]
    exact actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hxL hgs
  have hkM : s15_Three_psiStarK h B x ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    barSub_mono (v1Sub D.M V₀ V hV L) V hV h.le hkL
  have hfix : ∀ w : vStar D.M V₀ V hV L,
      s15_Three_psiStarK h B x w * w⁻¹ ∈ wStar D.M V₀ V hV L := by
    intro w
    have h1 : s15_Three_psiStarK h B x w * w⁻¹ ∈ commSub ⊤ (lStar D.M V₀ V hV L) :=
      Subgroup.subset_closure ⟨_, hkL, w, Subgroup.mem_top w, rfl⟩
    rwa [s15_Three_commSub_top_lStar h hV] at h1
  obtain ⟨hind, _⟩ := fifteen_two_directSum D h1217 h hV hL
  have hZmem : Z₀ ∈ wStarConj D.M V₀ V hV L := by
    rw [hZ₀]
    exact ⟨m, hm, rfl⟩
  have hbot : Z₀ ⊓ wStar D.M V₀ V hV L = ⊥ := by
    have hWmem : wStar D.M V₀ V hV L ∈ wStarConj D.M V₀ V hV L \ {Z₀} := by
      refine ⟨⟨1, D.M.one_mem, by simp only [conjSubgroup_one, wStar]⟩, ?_⟩
      simpa using Ne.symm hZne
    exact le_bot_iff.1 ((inf_le_inf_left _ (le_sSup hWmem)).trans
      (le_of_eq (disjoint_iff.1 (hind hZmem))))
  by_cases hkZ : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom = Z₀
  · intro v hv
    have h1 : s15_Three_psiStarK h B x v ∈ Z₀ :=
      hkZ ▸ Subgroup.mem_map_of_mem _ hv
    have h3 : s15_Three_psiStarK h B x v * v⁻¹ ∈ Z₀ ⊓ wStar D.M V₀ V hV L :=
      ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hv), hfix v⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  · have hmem : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom ∈ wStarConj D.M V₀ V hV L := by
      have h1 : Z₀ =
          (wStar D.M V₀ V hV L).map
            (actTil (v1Sub D.M V₀ V hV L) V hV ⟨(m : G), hMs1 hm⟩)⁻¹.toMonoidHom := by
        rw [hZ₀]
        exact s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV (hMs1 hm)
      rw [h1, Subgroup.map_map]
      have h2 : (s15_Three_psiStarK h B x).toMonoidHom.comp
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨(m : G), hMs1 hm⟩)⁻¹.toMonoidHom =
          (s15_Three_psiStarK h B x *
            (actTil (v1Sub D.M V₀ V hV L) V hV ⟨(m : G), hMs1 hm⟩)⁻¹).toMonoidHom := rfl
      rw [h2]
      exact s15_Infra_map_wStar_mem_wStarConj h.hyp125 hV
        ((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).mul_mem hkM
          ((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).inv_mem
            (actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hm (hMs1 hm))))
    have hle : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom ≤
        Z₀ ⊔ wStar D.M V₀ V hV L := by
      rintro w ⟨v, hv, rfl⟩
      refine Subgroup.mem_sup.2 ⟨v, hv, s15_Three_psiStarK h B x v * v⁻¹, hfix v, ?_⟩
      rw [mul_comm (s15_Three_psiStarK h B x v) v⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]
      rfl
    have hZbot : Z₀ = ⊥ := by
      by_cases hW : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom = wStar D.M V₀ V hV L
      · have hleW : Z₀ ≤ wStar D.M V₀ V hV L := by
          intro u hu
          have hku : s15_Three_psiStarK h B x u ∈ wStar D.M V₀ V hV L := by
            rw [← hW]
            exact Subgroup.mem_map_of_mem _ hu
          have h1 : u = (s15_Three_psiStarK h B x u * u⁻¹)⁻¹ *
              s15_Three_psiStarK h B x u := by group
          rw [h1]
          exact (wStar D.M V₀ V hV L).mul_mem
            ((wStar D.M V₀ V hV L).inv_mem (hfix u)) hku
        exact le_bot_iff.1 ((le_inf le_rfl hleW).trans (le_of_eq hbot))
      · have hle' : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom ≤
            sSup (wStarConj D.M V₀ V hV L \
              {Z₀.map (s15_Three_psiStarK h B x).toMonoidHom}) := by
          refine hle.trans (sup_le ?_ ?_)
          · exact le_sSup ⟨hZmem, by simpa using Ne.symm hkZ⟩
          · exact le_sSup ⟨⟨1, D.M.one_mem, by simp only [conjSubgroup_one, wStar]⟩,
              by simpa using Ne.symm hW⟩
        have hbot' : Z₀.map (s15_Three_psiStarK h B x).toMonoidHom = ⊥ :=
          le_bot_iff.1 ((le_inf le_rfl hle').trans
            (le_of_eq (disjoint_iff.1 (hind hmem))))
        exact (Subgroup.map_eq_bot_iff_of_injective Z₀
          (s15_Three_psiStarK h B x).injective).1 hbot'
    intro v hv
    rw [hZbot, Subgroup.mem_bot] at hv
    rw [hv, map_one]

private theorem s15_Three_commSub_K0_star (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h) :
    commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)) =
      (commSub ⊤ B).map (wStar D.M V₀ V h.isElemAbelian L).subtype := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro c ⟨k, hk, v, -, rfl⟩
    have hk' : k ∈ (s15_Three_psiStarK h B).range :=
      le_of_eq (s15_Three_psiStarK_range h B).symm hk
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hk'
    rw [← hx]
    let k' : ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)) :=
      ⟨s15_Three_psiStarK h B x,
        le_of_eq (s15_Three_psiStarK_range h B) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩
    let S := (commSub ⊤ B).map (wStar D.M V₀ V h.isElemAbelian L).subtype
    let φ : vStar D.M V₀ V h.isElemAbelian L →* vStar D.M V₀ V h.isElemAbelian L :=
      { toFun := fun w => s15_Three_psiStarK h B x w * w⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          show s15_Three_psiStarK h B x (a * b) * (a * b)⁻¹ =
            (s15_Three_psiStarK h B x a * a⁻¹) * (s15_Three_psiStarK h B x b * b⁻¹)
          rw [map_mul, mul_inv_rev]
          ac_rfl }
    have htop : (⊤ : Subgroup (vStar D.M V₀ V h.isElemAbelian L)) ≤ S.comap φ := by
      rw [← (fifteen_two_directSum D h1217 h h.isElemAbelian hL).2]
      refine sSup_le fun Z hZ => ?_
      rintro v hv
      rw [Subgroup.mem_comap]
      by_cases hZW : Z = wStar D.M V₀ V h.isElemAbelian L
      · rw [hZW] at hv
        have hv' : v = (wStar D.M V₀ V h.isElemAbelian L).subtype ⟨v, hv⟩ := rfl
        rw [hv']
        refine Subgroup.mem_map.2 ⟨(s15_Three_rho h1217 h hL hBA k' :
            MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) ⟨v, hv⟩ * ⟨v, hv⟩⁻¹,
          Subgroup.subset_closure ⟨(s15_Three_rho h1217 h hL hBA k').1,
            (s15_Three_rho h1217 h hL hBA k').2, ⟨v, hv⟩, Subgroup.mem_top _, rfl⟩, ?_⟩
        rw [map_mul, map_inv]
        congr 1
        exact s15_Three_rho_compat h1217 h hL hBA k' ⟨v, hv⟩
      · have h1 : φ v = 1 := by
          change s15_Three_psiStarK h B x v * v⁻¹ = 1
          rw [s15_Three_star_fix_conj h1217 h hL B x hZ hZW v hv, mul_inv_cancel]
        rw [h1]
        exact S.one_mem
    exact htop (Subgroup.mem_top v)
  · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
    rintro c ⟨b, hb, w, -, rfl⟩
    have hb' : b ∈ (s15_Three_phiB h B).range :=
      le_of_eq (s15_Three_phiB_range h B hBA).symm hb
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hb'
    rw [← hx]
    let k' : ↥(barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B)) :=
      ⟨s15_Three_psiStarK h B x,
        le_of_eq (s15_Three_psiStarK_range h B) (MonoidHom.mem_range.2 ⟨x, rfl⟩)⟩
    have hcompat := s15_Three_rho_compat h1217 h hL hBA k' w
    have hrho : (s15_Three_rho h1217 h hL hBA k' :
        MulAut ↥(wStar D.M V₀ V h.isElemAbelian L)) = s15_Three_phiB h B x :=
      congrArg Subtype.val (s15_Three_rho_apply h1217 h hL hBA x)
    rw [hrho] at hcompat
    change (wStar D.M V₀ V h.isElemAbelian L).subtype
      (((s15_Three_phiB h B) x) w * w⁻¹) ∈
      commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B))
    rw [map_mul, map_inv, hcompat]
    exact Subgroup.subset_closure ⟨k'.1, k'.2, (wStar D.M V₀ V h.isElemAbelian L).subtype w,
      Subgroup.mem_top _, rfl⟩

theorem s15_Four_natural (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {B : Subgroup (MulAut ↥(wStar D.M V₀ V h.isElemAbelian L))} (hBA : B ≤ s15AW h)
    (hK : s15KNat ↥B B (commSub ⊤ B)) :
    s15KNat ↥(barSub V₀ V h.isElemAbelian (s15K0 h B))
      (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B))
      (commSub ⊤ (barSub (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian (s15K0 h B))) := by
  rw [s15_Three_commSub_K0_star h1217 h hL hBA]
  exact s15_Four_knat_transfer (s15_Three_awEquivB h1217 h hL hBA).symm
    (wStar D.M V₀ V h.isElemAbelian L).subtype
    (wStar D.M V₀ V h.isElemAbelian L).subtype_injective
    (s15_Three_rho h1217 h hL hBA) (s15_Three_rho_compat h1217 h hL hBA) hK

end Natural

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
