module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_sl28_map_conj_inv_of_map_conj {X : Type} [Group X] {L : Subgroup X} {a : X}
    (h : L.map (MulAut.conj a).toMonoidHom = L) :
    L.map (MulAut.conj a⁻¹).toMonoidHom = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1
    (inv_mem (Subgroup.mem_normalizer_iff_map_conj_eq.2 h))

theorem s16h_sl28_z_sq_mem_nBar (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    x * x ∈ nBar D.M ⊥ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hx2M : x * x ∈ D.M := D.M.mul_mem hxM hxM
  have hs' : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} = 2 := by
    simpa [s15, lBar] using hs
  set a : MulAut (Vtil ⊥ V hV) := actTil ⊥ V hV ⟨x, hMs hxM⟩ with ha
  have hamem : a ∈ Mbar D.M ⊥ V hV := actTil_mem_barSub ⊥ V hV hxM (hMs hxM)
  have hne : (lBar ⊥ V hV L).map (MulAut.conj a).toMonoidHom ≠ lBar ⊥ V hV L := by
    intro hcon
    exact hxn ((s15_Infra_mem_nBar_iff h125 hV hxM).2 (by
      rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L]
      exact s16h_sl28_map_conj_inv_of_map_conj hcon))
  have hperm := ((c23a_two_conj hs').2 a hamem hne).2
  have hsq : (lBar ⊥ V hV L).map (MulAut.conj (a * a)).toMonoidHom = lBar ⊥ V hV L := by
    have h1 := hperm a hamem
    rcases h1 with ⟨hbad, -⟩ | ⟨-, hgood⟩
    · exact absurd hbad hne
    · rw [Subgroup.map_map] at hgood
      convert hgood using 2
      ext u
      simp [MulAut.conj_apply, mul_assoc]
  have hmapinv : (lBar ⊥ V hV L).map (MulAut.conj (a * a)⁻¹).toMonoidHom =
      lBar ⊥ V hV L := s16h_sl28_map_conj_inv_of_map_conj hsq
  refine (s15_Infra_mem_nBar_iff h125 hV hx2M).2 ?_
  rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hx2M) L]
  have hcast : actTil ⊥ V hV ⟨x * x, hMs hx2M⟩ = a * a := by
    rw [show (⟨x * x, hMs hx2M⟩ : ↥(stabTil ⊥ V)) =
      ⟨x, hMs hxM⟩ * ⟨x, hMs hxM⟩ from Subtype.ext rfl, map_mul]
  rw [hcast]
  exact hmapinv

theorem s16h_sl28_wSub_sq_eq (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    conjSubgroup (conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x) x =
      wSub ⊥ V h.hyp151.isElemAbelian L := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hx2M : x * x ∈ D.M := D.M.mul_mem hxM hxM
  have hbar : barSub ⊥ V hV (conjSubgroup L (x * x)) = barSub ⊥ V hV L :=
    (s15_Infra_mem_nBar_iff h125 hV hx2M).1
      (s16h_sl28_z_sq_mem_nBar D h hs hxM hxn)
  rw [conjSubgroup_conjSubgroup,
    ← s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs hx2M)]
  unfold wSub wTil
  rw [hbar]

theorem s16h_sl28_conj_z_eq (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        Subgroup.centralizer (L : Set G)) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hWx2 := s16h_sl28_wSub_sq_eq D h hs hxM hxn
  calc conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x
      = conjSubgroup (wSub ⊥ V hV L ⊓ conjSubgroup (wSub ⊥ V hV L) x) x := by rw [hZ0]
    _ = conjSubgroup (wSub ⊥ V hV L) x ⊓ conjSubgroup (conjSubgroup (wSub ⊥ V hV L) x) x := by
        rw [E3.conjSubgroup_inf]
    _ = conjSubgroup (wSub ⊥ V hV L) x ⊓ wSub ⊥ V hV L := by rw [hWx2]
    _ = wSub ⊥ V hV L ⊓ conjSubgroup (wSub ⊥ V hV L) x := inf_comm _ _
    _ = wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := hZ0

theorem s16h_sl28_v1Sub_eq_z (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) :
    v1Sub D.M ⊥ V h.hyp151.isElemAbelian L =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  obtain ⟨hv1, -⟩ := s16h_v1Sub_eq_sup_of_s_two D h hs hxM hxn
  have hZx : conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x =
      wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) :=
    s16h_sl28_conj_z_eq D h hs hxM hxn hZ0
  have hZ₂ : (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)).map
      (MulAut.conj x).toMonoidHom =
      wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
    rw [show (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)).map
        (MulAut.conj x).toMonoidHom =
        conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x⁻¹ from by
      rw [conjSubgroup, inv_inv]]
    calc conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x⁻¹
        = conjSubgroup (conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x) x⁻¹ := by
          rw [hZx]
      _ = conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) (x * x⁻¹) := by
          rw [conjSubgroup_conjSubgroup]
      _ = wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G) := by
          rw [mul_inv_cancel, conjSubgroup_one]
  rw [hv1, hZ₂, sup_idem]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
