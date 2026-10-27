module

public import CFSG.Milestones.ASVolI.F45.F46G2dGeo
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBridge

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Range

variable {G H : Type*} [Group G] [Group H] {f : G →* H}

theorem burnsideF46_g2d_inf_map_eq_bot_iff (hf : Function.Injective f) {A : Subgroup H}
    (hA : A ≤ f.range) (Q : Subgroup G) : A ⊓ Q.map f = ⊥ ↔ A.comap f ⊓ Q = ⊥ := by
  conv_lhs => rw [← Subgroup.map_comap_eq_self hA]
  rw [← Subgroup.map_inf_eq _ _ _ hf, Subgroup.map_eq_bot_iff_of_injective _ hf]

theorem burnsideF46_g2d_relIndex_map_sup (hf : Function.Injective f) {A B : Subgroup H}
    (hA : A ≤ f.range) (hB : B ≤ f.range) (Q : Subgroup G) :
    (Q.map f ⊔ A).relIndex B = (Q ⊔ A.comap f).relIndex (B.comap f) := by
  conv_lhs => rw [← Subgroup.map_comap_eq_self hA, ← Subgroup.map_comap_eq_self hB]
  rw [← Subgroup.map_sup, Subgroup.relIndex_map_map_of_injective _ _ hf]

theorem burnsideF46_g2d_card_comap (hf : Function.Injective f) {A : Subgroup H}
    (hA : A ≤ f.range) : Nat.card (A.comap f) = Nat.card A := by
  conv_rhs => rw [← Subgroup.map_comap_eq_self hA]
  exact (Subgroup.card_map_of_injective hf).symm

end Range

variable {α : RankTwoAmalgam.{0}} {Y Yb : Type} [Group Y] [Group Yb]

section Lift

theorem burnsideF46_g2d_pathMap_zero_x (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    {ph : GPath α.graphHat n} (h0 : ph 0 = xhat) : (c.graphCovering hc).pathMap ph 0 = c.xv := by
  rw [GraphCovering.pathMap_apply, h0]
  exact Θ_xhat c hc

theorem burnsideF46_g2d_pathMap_zero_l (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    {ph : GPath α.graphHat n} (h0 : ph 0 = lhat) : (c.graphCovering hc).pathMap ph 0 = c.lv := by
  rw [GraphCovering.pathMap_apply, h0]
  exact Θ_lhat c hc

theorem burnsideF46_g2d_lift_x {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful)
    (hι : ι.IsFaithful) {n : ℕ} {p : GPath β.graph n} (hp : p ∈ GPath.nbPaths β.graph β.xv n) :
    ∃ ph : GPath α.graphHat n, ph 0 = xhat ∧ (β.graphCovering hβ).pathMap ph = p ∧
      (ι.graphCovering hι).pathMap ph ∈ GPath.nbPaths ι.graph ι.xv n := by
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := (β.graphCovering hβ).lift_path xhat n p
    (by rw [hp.1]; exact (Θ_xhat β hβ).symm)
  refine ⟨ph, hph0, hphp, burnsideF46_g2d_pathMap_zero_x ι hι hph0, ?_⟩
  rw [(ι.graphCovering hι).noBack_pathMap_iff, ← (β.graphCovering hβ).noBack_pathMap_iff, hphp]
  exact hp.2

theorem burnsideF46_g2d_corr_x {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful)
    (hι : ι.IsFaithful) {n : ℕ} (hn : 1 ≤ n) {p : GPath β.graph n}
    (hp : p ∈ GPath.nbPaths β.graph β.xv n) :
    ∃ q ∈ GPath.nbPaths ι.graph ι.xv n,
      (p.stabPath : Subgroup β.G0).comap (f1 (c := β)) =
          (q.stabPath : Subgroup ι.G0).comap (f1 (c := ι)) ∧
        (stv β β.xv ⊓ stv β (p 1)).comap (f1 (c := β)) =
          (stv ι ι.xv ⊓ stv ι (q 1)).comap (f1 (c := ι)) := by
  obtain ⟨ph, hph0, hphp, hq⟩ := burnsideF46_g2d_lift_x hβ hι hp
  refine ⟨_, hq, ?_, ?_⟩
  · rw [← hphp, comap_f1_stabPath β hβ ph hph0, comap_f1_stabPath ι hι ph hph0]
  · rw [← hphp, comap_f1_stv_inf β hβ ph hph0 hn, comap_f1_stv_inf ι hι ph hph0 hn]

end Lift

section Transfer

variable {β : α.Completion Y} {ι : α.Completion Yb} (hβ : β.IsFaithful) (hι : ι.IsFaithful)

include hβ hι

theorem burnsideF46_g2d_transfer_x_idx {n : ℕ} (hn : 1 ≤ n) (Qb : Subgroup α.G1) (k : ℕ)
    (hi : ∀ q ∈ GPath.nbPaths ι.graph ι.xv n,
      (q.stabPath : Subgroup ι.G0) ⊓ Qb.map (f1 (c := ι)) = ⊥ ∧
        (Qb.map (f1 (c := ι)) ⊔ q.stabPath).relIndex (stv ι ι.xv ⊓ stv ι (q 1)) = k)
    {p : GPath β.graph n} (hp : p ∈ GPath.nbPaths β.graph β.xv n) :
    (p.stabPath : Subgroup β.G0) ⊓ Qb.map (f1 (c := β)) = ⊥ ∧
      (Qb.map (f1 (c := β)) ⊔ p.stabPath).relIndex (stv β β.xv ⊓ stv β (p 1)) = k := by
  obtain ⟨q, hq, e1, e2⟩ := burnsideF46_g2d_corr_x hβ hι hn hp
  obtain ⟨h1, h2⟩ := hi q hq
  have rβ : (p.stabPath : Subgroup β.G0) ≤ (f1 (c := β)).range :=
    (GPath.stabPath_le_stabilizer p hp.1).trans (stv_xv_le_range_f1 β)
  have rι : (q.stabPath : Subgroup ι.G0) ≤ (f1 (c := ι)).range :=
    (GPath.stabPath_le_stabilizer q hq.1).trans (stv_xv_le_range_f1 ι)
  have sβ : stv β β.xv ⊓ stv β (p 1) ≤ (f1 (c := β)).range :=
    inf_le_left.trans (stv_xv_le_range_f1 β)
  have sι : stv ι ι.xv ⊓ stv ι (q 1) ≤ (f1 (c := ι)).range :=
    inf_le_left.trans (stv_xv_le_range_f1 ι)
  rw [burnsideF46_g2d_inf_map_eq_bot_iff (f1_injective ι hι) rι] at h1
  rw [burnsideF46_g2d_relIndex_map_sup (f1_injective ι hι) rι sι] at h2
  rw [burnsideF46_g2d_inf_map_eq_bot_iff (f1_injective β hβ) rβ,
    burnsideF46_g2d_relIndex_map_sup (f1_injective β hβ) rβ sβ, e1, e2]
  exact ⟨h1, h2⟩

theorem burnsideF46_g2d_transfer_x_card {n : ℕ} (k : ℕ) (hn : 1 ≤ n)
    (hi : ∀ q ∈ GPath.nbPaths ι.graph ι.xv n, Nat.card (q.stabPath : Subgroup ι.G0) = k)
    {p : GPath β.graph n} (hp : p ∈ GPath.nbPaths β.graph β.xv n) :
    Nat.card (p.stabPath : Subgroup β.G0) = k := by
  obtain ⟨q, hq, e1, -⟩ := burnsideF46_g2d_corr_x hβ hι hn hp
  have rβ : (p.stabPath : Subgroup β.G0) ≤ (f1 (c := β)).range :=
    (GPath.stabPath_le_stabilizer p hp.1).trans (stv_xv_le_range_f1 β)
  have rι : (q.stabPath : Subgroup ι.G0) ≤ (f1 (c := ι)).range :=
    (GPath.stabPath_le_stabilizer q hq.1).trans (stv_xv_le_range_f1 ι)
  rw [← burnsideF46_g2d_card_comap (f1_injective β hβ) rβ, e1,
    burnsideF46_g2d_card_comap (f1_injective ι hι) rι]
  exact hi q hq

end Transfer

section Orbits

theorem burnsideF46_g2d_Θ_smul_xi2 (c : α.Completion Y) (hc : c.IsFaithful) (a : α.G2)
    (v : α.Γhat) : c.Θ hc (α.xi2 a • v) = f2 (c := c) a • c.Θ hc v := by
  rw [Θ_smul c hc, theta0_xi2 c hc]

theorem burnsideF46_g2d_pathMap_smul_xi2 (c : α.Completion Y) (hc : c.IsFaithful) (a : α.G2)
    {n : ℕ} (ph : GPath α.graphHat n) :
    (c.graphCovering hc).pathMap (α.xi2 a • ph) = f2 (c := c) a • (c.graphCovering hc).pathMap ph :=
  GPath.ext' fun i _ => by
    simp only [GraphCovering.pathMap_apply, GPath.smul_apply]
    exact burnsideF46_g2d_Θ_smul_xi2 c hc a (ph i)

theorem burnsideF46_g2d_pathMap_inj_l (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    {ph ph' : GPath α.graphHat n} (h0 : ph 0 = lhat) (h0' : ph' 0 = lhat)
    (h : (c.graphCovering hc).pathMap ph = (c.graphCovering hc).pathMap ph') : ph = ph' := by
  obtain ⟨r, -, hr⟩ := (c.graphCovering hc).lift_path lhat n ((c.graphCovering hc).pathMap ph)
    (by rw [GraphCovering.pathMap_apply, h0])
  exact (hr ph ⟨h0, rfl⟩).trans (hr ph' ⟨h0', h.symm⟩).symm

theorem burnsideF46_g2d_mem_orbit_iff_l (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    {ph ph' : GPath α.graphHat n} (h0 : ph 0 = lhat) (h0' : ph' 0 = lhat) :
    (c.graphCovering hc).pathMap ph' ∈ pathOrbit (stv c c.lv) ((c.graphCovering hc).pathMap ph) ↔
      ∃ a : α.G2, α.xi2 a • ph = ph' := by
  constructor
  · rintro ⟨g, hg, hgp⟩
    obtain ⟨a, rfl⟩ := stv_lv_le_range_f2 c hg
    refine ⟨a, burnsideF46_g2d_pathMap_inj_l c hc ?_ h0' ?_⟩
    · rw [GPath.smul_apply, h0]
      exact α.xi2_smul_lhat a
    · rw [burnsideF46_g2d_pathMap_smul_xi2]
      exact hgp
  · rintro ⟨a, rfl⟩
    exact ⟨f2 (c := c) a, MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a),
      (burnsideF46_g2d_pathMap_smul_xi2 c hc a ph).symm⟩

theorem burnsideF46_g2d_stv_lv_eq_map (c : α.Completion Y) :
    stv c c.lv = (⊤ : Subgroup α.G2).map (f2 (c := c)) := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨a, rfl⟩ := stv_lv_le_range_f2 c hg
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top a)
  · rintro _ ⟨a, -, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)

theorem burnsideF46_g2d_card_orbit_l (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    {ph : GPath α.graphHat n} (h0 : ph 0 = lhat) :
    Nat.card ↥(pathOrbit (stv c c.lv) ((c.graphCovering hc).pathMap ph)) = (α.gam2 ph).index := by
  have e := burnsideF45_card_pathOrbit c (burnsideF46_g2d_pathMap_zero_l c hc h0)
  show Nat.card ↥{r | ∃ g ∈ stv c c.lv, g • (c.graphCovering hc).pathMap ph = r} = _
  rw [e, stabPath_eq_map_gam2 c hc ph h0, burnsideF46_g2d_stv_lv_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ (f2_injective c hc), Subgroup.relIndex_top_right]

theorem burnsideF46_g2d_twoOrb_transfer_l {β : α.Completion Y} {ι : α.Completion Yb}
    (hβ : β.IsFaithful) (hι : ι.IsFaithful) {n : ℕ} (h : burnsideF46_g2d_TwoOrb ι ι.lv n) :
    burnsideF46_g2d_TwoOrb β β.lv n := by
  obtain ⟨q₁, hq₁, q₂, hq₂, hcov, hdisj, hcard⟩ := h
  obtain ⟨h₁, ⟨h₁0, h₁q⟩, -⟩ := (ι.graphCovering hι).lift_path lhat n q₁
    (by rw [hq₁.1]; exact (Θ_lhat ι hι).symm)
  obtain ⟨h₂, ⟨h₂0, h₂q⟩, -⟩ := (ι.graphCovering hι).lift_path lhat n q₂
    (by rw [hq₂.1]; exact (Θ_lhat ι hι).symm)
  have hmem : ∀ {ph : GPath α.graphHat n}, ph 0 = lhat →
      (ι.graphCovering hι).pathMap ph ∈ GPath.nbPaths ι.graph ι.lv n →
      (β.graphCovering hβ).pathMap ph ∈ GPath.nbPaths β.graph β.lv n := by
    intro ph h0 hph
    refine ⟨burnsideF46_g2d_pathMap_zero_l β hβ h0, ?_⟩
    rw [(β.graphCovering hβ).noBack_pathMap_iff, ← (ι.graphCovering hι).noBack_pathMap_iff]
    exact hph.2
  have key : ∀ {ph ph' : GPath α.graphHat n}, ph 0 = lhat → ph' 0 = lhat →
      ((β.graphCovering hβ).pathMap ph' ∈
          pathOrbit (stv β β.lv) ((β.graphCovering hβ).pathMap ph) ↔
        (ι.graphCovering hι).pathMap ph' ∈
          pathOrbit (stv ι ι.lv) ((ι.graphCovering hι).pathMap ph)) := fun h0 h0' =>
    (burnsideF46_g2d_mem_orbit_iff_l β hβ h0 h0').trans
      (burnsideF46_g2d_mem_orbit_iff_l ι hι h0 h0').symm
  have hp₁ := hmem h₁0 (by rw [h₁q]; exact hq₁)
  have hp₂ := hmem h₂0 (by rw [h₂q]; exact hq₂)
  refine ⟨_, hp₁, _, hp₂, ?_, ?_, ?_⟩
  · ext r
    constructor
    · intro hr
      obtain ⟨rh, ⟨rh0, rhr⟩, -⟩ := (β.graphCovering hβ).lift_path lhat n r
        (by rw [hr.1]; exact (Θ_lhat β hβ).symm)
      have hrb : (ι.graphCovering hι).pathMap rh ∈ GPath.nbPaths ι.graph ι.lv n := by
        refine ⟨burnsideF46_g2d_pathMap_zero_l ι hι rh0, ?_⟩
        rw [(ι.graphCovering hι).noBack_pathMap_iff, ← (β.graphCovering hβ).noBack_pathMap_iff,
          rhr]
        exact hr.2
      rw [hcov] at hrb
      rw [← rhr]
      rcases hrb with h | h
      · left
        exact (key h₁0 rh0).mpr (by rw [h₁q]; exact h)
      · right
        exact (key h₂0 rh0).mpr (by rw [h₂q]; exact h)
    · rintro (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩)
      · exact smul_mem_nbPaths hp₁ (MulAction.mem_stabilizer_iff.mp hg)
      · exact smul_mem_nbPaths hp₂ (MulAction.mem_stabilizer_iff.mp hg)
  · rw [Set.disjoint_left]
    rintro r ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, hgr⟩
    have h21 : (β.graphCovering hβ).pathMap h₂ ∈
        pathOrbit (stv β β.lv) ((β.graphCovering hβ).pathMap h₁) := by
      refine ⟨g₂⁻¹ * g₁, mul_mem (inv_mem hg₂) hg₁, ?_⟩
      rw [GPath.mul_smul', ← hgr, ← GPath.mul_smul', inv_mul_cancel, GPath.one_smul']
    have h2 := (key h₁0 h₂0).mp h21
    rw [h₁q, h₂q] at h2
    exact Set.disjoint_left.mp hdisj h2 ⟨1, one_mem _, GPath.one_smul' _⟩
  · rw [burnsideF46_g2d_card_orbit_l β hβ h₁0, burnsideF46_g2d_card_orbit_l β hβ h₂0,
      ← burnsideF46_g2d_card_orbit_l ι hι h₁0, ← burnsideF46_g2d_card_orbit_l ι hι h₂0, h₁q, h₂q]
    exact hcard

end Orbits

end CFSG.ASVolI
