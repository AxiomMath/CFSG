module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIOff
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalLemmaN
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalDichZ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem false_of_mixed (F : Frame L1 L2 S D X) {x y : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hx : vtype x = true) (hy : vtype y = false) (hfx : ZFaithful x) (hyx : Zv y ≤ stab x)
    (hxy : Zv x ≤ stab y) (hnot : ¬ Zv y ≤ Qv x) : False := by
  have hA := Amal.of_frame F
  obtain ⟨w, hw, hwQ⟩ : ∃ w ∈ Zv y, w ∉ Qv x := by
    by_contra h; push Not at h; exact hnot fun w hw => h w hw
  have hww : w ^ 2 = 1 := (hA.isElemAbelian_Zv y).2 w hw
  have hwx : w ∈ stab x := hyx hw
  have hfaith : ¬ stab x ≤ Subgroup.centralizer (Zv x : Set G) := by
    intro hle
    apply hwQ
    have hsq : ∀ u ∈ Subgroup.zpowers w, u ^ 2 = 1 := by
      intro u hu
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hww, one_zpow]
    exact hA.le_Qv_of_ZFaithful hfx (Subgroup.zpowers_le.mpr hwx) (isPGroup_two_of_sq hsq)
      (Subgroup.zpowers_le.mpr (hle hwx)) (Subgroup.mem_zpowers w)
  have hQC : Qv x ≤ Subgroup.centralizer (Zv x : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hv).2 q hq).symm
  have hw2 : w ^ 2 ^ 1 ∈ Qv x := by rw [pow_one, hww]; exact one_mem _
  have hN := four_le_relIndex_A F hx (hA.isElemAbelian_Zv x) (hA.stab_le_normalizer_Zv x) hQC
    hfaith hwx hwQ hw2
  have h2 := relIndex_inf_Qv_le_two F hy hxy (hA.isElemAbelian_Zv x)
  have hle : Zv x ⊓ Qv y ≤ Zv x ⊓ Subgroup.centralizer {w} := by
    refine le_inf inf_le_left fun v hv => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv y hw).2 v (Subgroup.mem_inf.mp hv).2
  have h3 := (Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite).trans h2
  omega

theorem caseI_false_of_vtype_false (F : Frame L1 L2 S D X)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hI : ¬ Zv α' ≤ Qv α)
    (hα : vtype α = false) (hα' : vtype α' = false) : False := by
  have hA := Amal.of_frame F
  obtain ⟨hbα', hfα, hfα'⟩ := hA.caseI (frame_dichotomy F) hc hI
  have hZα'α : Zv α' ≤ stab α :=
    hA.Zv_le_stab_of_dist_le (by rw [CosetGeom.dist_comm, hc.dist_eq, hbα'])
  have hZαα' : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
  rcases hA.offender_or α α' with h | h
  · exact H2 F hα hfα (hA.isElemAbelian_Zv α') hZα'α hI h
  · exact H2 F hα' hfα' (hA.isElemAbelian_Zv α) hZαα' hc.not_le h

theorem caseI_vtype (F : Frame L1 L2 S D X) {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hc : IsCritData α β α') (hI : ¬ Zv α' ≤ Qv α) : vtype α = true ∧ vtype α' = true := by
  have hA := Amal.of_frame F
  obtain ⟨hbα', hfα, hfα'⟩ := hA.caseI (frame_dichotomy F) hc hI
  have hZα'α : Zv α' ≤ stab α :=
    hA.Zv_le_stab_of_dist_le (by rw [CosetGeom.dist_comm, hc.dist_eq, hbα'])
  have hZαα' : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le (by rw [hc.dist_eq, hc.bAt_eq])
  cases h : vtype α <;> cases h' : vtype α'
  · exact (caseI_false_of_vtype_false F hc hI h h').elim
  · exact (false_of_mixed F h' h hfα' hZαα' hZα'α hc.not_le).elim
  · exact (false_of_mixed F h h' hfα hZα'α hZαα' hI).elim
  · exact ⟨rfl, rfl⟩

theorem caseI_T2_false (F : Frame L1 L2 S D X)
    (hT2 : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), ZCentral δ ↔ vtype δ = true)
    {α β α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hc : IsCritData α β α') (hI : ¬ Zv α' ≤ Qv α) :
    False :=
  (Amal.of_frame F).not_ZCentral_of_bAt hc.bAt_eq ((hT2 α).mpr (caseI_vtype F hc hI).1)

end CFSG.Quasithin.Kleidman.F204
