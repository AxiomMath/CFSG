module

public import CFSG.Quasithin.Recognition.F4Transfer
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDefs

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] {Yb : Type w'} [Group Yb]

theorem mem_stabPath_snoc {V : Type*} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V]
    {n : ℕ} (p : GPath Γ n) (w : V) (h : Γ.Adj (p n) w) (g : H) :
    g ∈ (p.snoc w h).stabPath ↔ g ∈ p.stabPath ∧ g • w = w := by
  rw [GPath.mem_stabPath_iff, GPath.mem_stabPath_iff]
  constructor
  · intro hg
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hg i (by omega)
      rwa [GPath.snoc_of_le _ _ _ hi] at this
    · have := hg (n + 1) le_rfl
      rwa [GPath.snoc_last] at this
  · rintro ⟨hg, hw⟩ i hi
    rcases Nat.lt_or_ge i (n + 1) with h1 | h1
    · rw [GPath.snoc_of_le _ _ _ (by omega)]
      exact hg i (by omega)
    · have : i = n + 1 := by omega
      subst this
      rw [GPath.snoc_last]
      exact hw

theorem stabPath_eq_map_gam1 (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    (q : GPath α.graphHat n) (hq : q 0 = xhat) :
    (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0) =
      (α.gam1 q).map (f1 (c := c)) := by
  have hle : (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0) ≤
      (f1 (c := c)).range := by
    refine (GPath.stabPath_le_stabilizer _ ?_).trans (stv_xv_le_range_f1 c)
    show c.Θ hc (q 0) = c.xv
    rw [hq]
    exact Θ_xhat c hc
  rw [← comap_f1_stabPath c hc q hq, Subgroup.map_comap_eq]
  exact (inf_eq_right.mpr hle).symm

theorem stabPath_eq_map_gam2 (c : α.Completion Y) (hc : c.IsFaithful) {n : ℕ}
    (q : GPath α.graphHat n) (hq : q 0 = lhat) :
    (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0) =
      (α.gam2 q).map (f2 (c := c)) := by
  have hle : (((c.graphCovering hc).pathMap q).stabPath : Subgroup c.G0) ≤
      (f2 (c := c)).range := by
    refine (GPath.stabPath_le_stabilizer _ ?_).trans (stv_lv_le_range_f2 c)
    show c.Θ hc (q 0) = c.lv
    rw [hq]
    exact Θ_lhat c hc
  rw [← comap_f2_stabPath c hc q hq, Subgroup.map_comap_eq]
  exact (inf_eq_right.mpr hle).symm

section Transfer

variable {c : α.Completion Y} {ι : α.Completion Yb} (hc : c.IsFaithful) (hι : ι.IsFaithful)

include hc hι

theorem noFixEnd_transfer_x {m : ℕ} (hm : 1 ≤ m) (h : NoFixEnd ι m ι.xv) :
    NoFixEnd c m c.xv := by
  intro p hp y hy hne hall
  have hcov := c.graphCovering hc
  have hcovι := ι.graphCovering hι
  have hr : p.snoc y hy ∈ GPath.nbPaths c.graph c.xv (m + 1) :=
    ⟨by rw [GPath.snoc_of_le _ _ _ (Nat.zero_le m)]; exact hp.1,
      GPath.noBack_snoc hp.2 hy (fun _ => hne)⟩
  obtain ⟨rh, ⟨hrh0, hrhp⟩, -⟩ := hcov.lift_path xhat (m + 1) (p.snoc y hy)
    (by rw [hr.1]; exact (Θ_xhat c hc).symm)
  have hrb : hcovι.pathMap rh ∈ GPath.nbPaths ι.graph ι.xv (m + 1) := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (rh 0) = ι.xv
      rw [hrh0]; exact Θ_xhat ι hι
    · rw [hcovι.noBack_pathMap_iff, ← hcov.noBack_pathMap_iff, hrhp]
      exact hr.2
  have hpb : (hcovι.pathMap rh).take m (Nat.le_succ m) ∈ GPath.nbPaths ι.graph ι.xv m :=
    ⟨by rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le m)]; exact hrb.1, hrb.2.take m _⟩
  have hadj : ι.graph.Adj (((hcovι.pathMap rh).take m (Nat.le_succ m)) m)
      (hcovι.pathMap rh (m + 1)) := by
    rw [GPath.take_apply_of_le _ _ _ le_rfl]
    exact (hcovι.pathMap rh).adj m (Nat.lt_succ_self m)
  have hne' : hcovι.pathMap rh (m + 1) ≠
      ((hcovι.pathMap rh).take m (Nat.le_succ m)) (m - 1) := by
    rw [GPath.take_apply_of_le _ _ _ (by omega)]
    intro e
    exact hrb.2 (m - 1) (by omega) (by rw [show m - 1 + 2 = m + 1 by omega]; exact e.symm)
  refine h _ hpb _ hadj hne' ?_
  intro g hg
  obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 ι (GPath.stabPath_le_stabilizer _ hpb.1 hg)
  have h1 : f1 (c := ι) a ∈ (hcovι.pathMap (rh.take m (Nat.le_succ m))).stabPath := by
    rw [hcovι.pathMap_take]
    exact hg
  have hrt0 : (rh.take m (Nat.le_succ m)) 0 = xhat := by
    rw [GPath.take_apply_of_le _ _ _ (Nat.zero_le m)]
    exact hrh0
  have h2 := (mem_stabPath_f1_iff c hc _ hrt0 a).mpr ((mem_stabPath_f1_iff ι hι _ hrt0 a).mp h1)
  rw [hcov.pathMap_take, hrhp, GPath.snoc_take_self] at h2
  have h3 := hall _ h2
  have h4 : f1 (c := c) a ∈ (hcov.pathMap rh).stabPath := by
    rw [hrhp, mem_stabPath_snoc]
    exact ⟨h2, h3⟩
  have h5 := (mem_stabPath_f1_iff ι hι rh hrh0 a).mpr ((mem_stabPath_f1_iff c hc rh hrh0 a).mp h4)
  exact h5 (m + 1) le_rfl

theorem transPair_transfer_x {m : ℕ} (hm : 1 ≤ m) (h : TransPair ι m ι.xv) :
    TransPair c m c.xv := by
  intro p hp q hq hpq y y' hy hy'
  have hcov := c.graphCovering hc
  have hcovι := ι.graphCovering hι
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := hcov.lift_path xhat m p (by rw [hp.1]; exact (Θ_xhat c hc).symm)
  obtain ⟨qh, ⟨hqh0, hqhq⟩, -⟩ := hcov.lift_path xhat m q (by rw [hq.1]; exact (Θ_xhat c hc).symm)
  have step : ∀ z : c.Γ, c.graph.Adj c.xv z →
      ∃ zh : α.Γhat, α.graphHat.Adj xhat zh ∧ c.Θ hc zh = z := fun z hz =>
    hcov.loc_surj xhat z (by rw [Θ_xhat c hc]; exact hz)
  obtain ⟨yh, hyh, hyhe⟩ := step y hy
  obtain ⟨yh', hyh', hyhe'⟩ := step y' hy'
  have hpb : (hcovι.pathMap ph) ∈ GPath.nbPaths ι.graph ι.xv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (ph 0) = ι.xv
      rw [hph0]; exact Θ_xhat ι hι
    · rw [hcovι.noBack_pathMap_iff, ← hcov.noBack_pathMap_iff, hphp]
      exact hp.2
  have hqb : (hcovι.pathMap qh) ∈ GPath.nbPaths ι.graph ι.xv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (qh 0) = ι.xv
      rw [hqh0]; exact Θ_xhat ι hι
    · rw [hcovι.noBack_pathMap_iff, ← hcov.noBack_pathMap_iff, hqhq]
      exact hq.2
  have hne : (hcovι.pathMap ph) 1 ≠ (hcovι.pathMap qh) 1 := by
    intro e
    apply hpq
    have a1 : α.graphHat.Adj xhat (ph 1) := by
      have := ph.adj 0 (by omega)
      rwa [hph0] at this
    have a2 : α.graphHat.Adj xhat (qh 1) := by
      have := qh.adj 0 (by omega)
      rwa [hqh0] at this
    have e2 : ph 1 = qh 1 := hcovι.loc_inj _ _ _ a1 a2 e
    rw [← hphp, ← hqhq]
    simp only [GraphCovering.pathMap_apply, e2]
  have hadj : ∀ zh : α.Γhat, α.graphHat.Adj xhat zh → ι.graph.Adj ι.xv (ι.Θ hι zh) := by
    intro zh hz
    have := hcovι.adj _ _ hz
    rwa [Θ_xhat ι hι] at this
  obtain ⟨g, hg, hgy⟩ := h _ hpb _ hqb hne (ι.Θ hι yh) (ι.Θ hι yh') (hadj _ hyh) (hadj _ hyh')
  have hmι : (hcovι.pathMap ph).stabPath ⊔ (hcovι.pathMap qh).stabPath =
      (α.gam1 ph ⊔ α.gam1 qh).map (f1 (c := ι)) := by
    rw [Subgroup.map_sup, ← stabPath_eq_map_gam1 ι hι ph hph0,
      ← stabPath_eq_map_gam1 ι hι qh hqh0]
  have hmc : p.stabPath ⊔ q.stabPath = (α.gam1 ph ⊔ α.gam1 qh).map (f1 (c := c)) := by
    rw [Subgroup.map_sup, ← stabPath_eq_map_gam1 c hc ph hph0,
      ← stabPath_eq_map_gam1 c hc qh hqh0, hphp, hqhq]
  rw [hmι] at hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  refine ⟨f1 (c := c) a, ?_, ?_⟩
  · rw [hmc]
    exact Subgroup.mem_map_of_mem _ ha
  · have e1 : ι.Θ hι (α.xi1 a • yh) = ι.Θ hι yh' := by
      rw [Θ_smul ι hι, theta0_xi1 ι hι]
      exact hgy
    have hsm : α.graphHat.Adj xhat (α.xi1 a • yh) := by
      have := (GraphAction.adj_smul (α.xi1 a) xhat yh).mpr hyh
      rwa [α.xi1_smul_xhat] at this
    have e2 : α.xi1 a • yh = yh' := hcovι.loc_inj _ _ _ hsm hyh' e1
    have e3 := Θ_smul c hc (α.xi1 a) yh
    rw [e2, theta0_xi1 c hc, hyhe, hyhe'] at e3
    exact e3.symm

end Transfer

end CFSG.Quasithin.TitsGeo
