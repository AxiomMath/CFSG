module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s16fhKappa (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    Vtil V₀ V h.isElemAbelian →* vStar D.M V₀ V h.isElemAbelian L :=
  s15T7Kappa V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian
    (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)

theorem s16fh_wStar_eq_map (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    wStar D.M V₀ V h.isElemAbelian L = (wTil V₀ V h.isElemAbelian L).map (s16fhKappa D h) := by
  unfold wStar wSub
  exact s15_T7_imgTil_preTil_eq_map V₀ (v1Sub D.M V₀ V h.isElemAbelian L) V
    h.isElemAbelian (s15_Infra_le_v1Sub D.M V₀ V h.isElemAbelian L)
    (wTil V₀ V h.isElemAbelian L)

theorem s16fh_lbar_lstar_equiv (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) :
    ∃ ρ : ↥(lBar V₀ V h.isElemAbelian L) ≃* ↥(lStar D.M V₀ V h.isElemAbelian L),
      ∀ (a : ↥(lBar V₀ V h.isElemAbelian L)) (x : Vtil V₀ V h.isElemAbelian),
        s16fhKappa D h ((a : MulAut (Vtil V₀ V h.isElemAbelian)) x) =
          ((ρ a : ↥(lStar D.M V₀ V h.isElemAbelian L)) :
            MulAut (vStar D.M V₀ V h.isElemAbelian L)) (s16fhKappa D h x) := by
  obtain ⟨ρ, hL, hκ⟩ := s16e_two_kappa_equiv D h1217 h h.isElemAbelian
  have hLX := s16e_two_lBar_le D h h.isElemAbelian
  have hLX' := s16e_two_lStar_le D h h.isElemAbelian
  let ρL : ↥(lBar V₀ V h.isElemAbelian L) ≃* ↥(lStar D.M V₀ V h.isElemAbelian L) :=
    ((Subgroup.subgroupOfEquivOfLe hLX).symm.trans
      ((MulEquiv.subgroupMap ρ _).trans
        ((MulEquiv.subgroupCongr hL).trans (Subgroup.subgroupOfEquivOfLe hLX'))))
  refine ⟨ρL, fun a x => ?_⟩
  have hform : ((ρL a : ↥(lStar D.M V₀ V h.isElemAbelian L)) :
        MulAut (vStar D.M V₀ V h.isElemAbelian L)) =
      ((ρ ⟨(a : MulAut (Vtil V₀ V h.isElemAbelian)), hLX a.2⟩ :
        ↥(Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian)) :
        MulAut (vStar D.M V₀ V h.isElemAbelian L)) := rfl
  rw [hform]
  exact hκ ⟨(a : MulAut (Vtil V₀ V h.isElemAbelian)), hLX a.2⟩ x

theorem s16fh_wTil_stable (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    ∀ x ∈ lBar V₀ V h.isElemAbelian L, ∀ u ∈ wTil V₀ V h.isElemAbelian L,
      (x : MulAut (Vtil V₀ V h.isElemAbelian)) u ∈ wTil V₀ V h.isElemAbelian L := by
  intro x hx u hu
  exact CFSG.Quasithin.Asc81c.commSub_stable' hx (by simpa [wTil, lBar] using hu)

theorem s16fh_wTil_comm (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    commSub (wTil V₀ V h.isElemAbelian L) (lBar V₀ V h.isElemAbelian L) =
      wTil V₀ V h.isElemAbelian L := by
  simpa [wTil, lBar] using
    s15_Lin_commSub_commSub_eq_of_no_two_quotient (s15_Infra_vtil_sq_eq_one V₀ V h.isElemAbelian)
      (s15_Kbar_no_two_quotient h)

theorem s16fh_ker_wTil_le_fixV (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L) :
    wTil V₀ V h.isElemAbelian L ⊓ (s16fhKappa D h).ker ≤ fixV (lBar V₀ V h.isElemAbelian L) := by
  have hker : (s16fhKappa D h).ker ≤
      imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) := by
    intro q hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V h.isElemAbelian q
    rw [mem_imgTil]
    have h1 : mkTil (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian y = 1 := by
      simpa [s16fhKappa, s15_T7_kappa_mk] using hq
    exact ⟨y, (mem_modNull _ V h.isElemAbelian y).1
      ((QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V h.isElemAbelian L) V
        h.isElemAbelian) y).1 h1), rfl⟩
  have hfix : imgTil V₀ V h.isElemAbelian (v1Sub D.M V₀ V h.isElemAbelian L) ≤
      fixV (lBar V₀ V h.isElemAbelian L) := by
    simpa only [conjSubgroup_one, lBar] using
      s15_Core_imgTil_v1Sub_le_fixV h (m := (1 : G)) D.M.one_mem
  exact inf_le_right.trans (hker.trans hfix)

theorem s16fh_delta_le_rk_ker (D : Data G) {V L : Subgroup G} (h : Hyp151 D ⊥ V L) :
    delta15 D.M ⊥ V h.isElemAbelian L ≤
      rk ↥(wTil ⊥ V h.isElemAbelian L ⊓ (s16fhKappa D h).ker) := by
  have hV := h.isElemAbelian
  let I : Subgroup (Vtil ⊥ V hV) :=
    imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L)
  have hIleU : I ≤ wTil ⊥ V hV L := by
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤ wTil ⊥ V hV L
    have h := Subgroup.map_mono (f := (mkTil ⊥ V hV))
      (Subgroup.subgroupOf_mono V
        (inf_le_right : v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L ≤ wSub ⊥ V hV L))
    change imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ≤
      imgTil ⊥ V hV (wSub ⊥ V hV L) at h
    rw [wSub, imgTil_preTil] at h
    exact h
  have hIleker : I ≤ (s16fhKappa D h).ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    change q ∈ imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) at hq
    rw [mem_imgTil] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have h1 : mkTil (v1Sub D.M ⊥ V hV L) V hV x = 1 :=
      (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV) x).2 hx.1
    simpa [s16fhKappa, s15_T7_kappa_mk] using h1
  have hrk : rk ↥I = delta15 D.M ⊥ V hV L := by
    have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
      (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) hV
      (inf_le_right.trans (preTil_le ⊥ V hV _))
    have hzero : (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) ⊓ ⊥ = ⊥ :=
      inf_eq_right.mpr bot_le
    rw [show imgTil ⊥ V hV (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = I from rfl,
      hzero] at h
    have hzero' : mSub (⊥ : Subgroup G) = 0 := by simp [mSub, rk]
    have h' : mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) = rk ↥I := by
      simpa [hzero'] using h
    rw [show delta15 D.M ⊥ V hV L =
      mSub (v1Sub D.M ⊥ V hV L ⊓ wSub ⊥ V hV L) from rfl]
    exact h'.symm
  have hle : I ≤ wTil ⊥ V hV L ⊓ (s16fhKappa D h).ker := le_inf hIleU hIleker
  rw [← hrk]
  exact rk_mono hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
