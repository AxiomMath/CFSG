module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoBridge

public section

namespace CFSG.Quasithin.TitsGeo

open CFSG.Open CFSG.Quasithin.F7 CFSG.Quasithin.RankTwoAmalgam.Completion

universe u w w'

variable {α : RankTwoAmalgam.{u}} {Y : Type w} [Group Y] {Yb : Type w'} [Group Yb]

section Transfer

variable {c : α.Completion Y} {ι : α.Completion Yb} (hc : c.IsFaithful) (hι : ι.IsFaithful)

include hc hι

theorem transPair_transfer_l {m : ℕ} (hm : 1 ≤ m) (h : TransPair ι m ι.lv) :
    TransPair c m c.lv := by
  intro p hp q hq hpq y y' hy hy'
  have hcov := c.graphCovering hc
  have hcovι := ι.graphCovering hι
  obtain ⟨ph, ⟨hph0, hphp⟩, -⟩ := hcov.lift_path lhat m p (by rw [hp.1]; exact (Θ_lhat c hc).symm)
  obtain ⟨qh, ⟨hqh0, hqhq⟩, -⟩ := hcov.lift_path lhat m q (by rw [hq.1]; exact (Θ_lhat c hc).symm)
  have step : ∀ z : c.Γ, c.graph.Adj c.lv z →
      ∃ zh : α.Γhat, α.graphHat.Adj lhat zh ∧ c.Θ hc zh = z := fun z hz =>
    hcov.loc_surj lhat z (by rw [Θ_lhat c hc]; exact hz)
  obtain ⟨yh, hyh, hyhe⟩ := step y hy
  obtain ⟨yh', hyh', hyhe'⟩ := step y' hy'
  have hpb : (hcovι.pathMap ph) ∈ GPath.nbPaths ι.graph ι.lv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (ph 0) = ι.lv
      rw [hph0]; exact Θ_lhat ι hι
    · rw [hcovι.noBack_pathMap_iff, ← hcov.noBack_pathMap_iff, hphp]
      exact hp.2
  have hqb : (hcovι.pathMap qh) ∈ GPath.nbPaths ι.graph ι.lv m := by
    refine ⟨?_, ?_⟩
    · show ι.Θ hι (qh 0) = ι.lv
      rw [hqh0]; exact Θ_lhat ι hι
    · rw [hcovι.noBack_pathMap_iff, ← hcov.noBack_pathMap_iff, hqhq]
      exact hq.2
  have hne : (hcovι.pathMap ph) 1 ≠ (hcovι.pathMap qh) 1 := by
    intro e
    apply hpq
    have a1 : α.graphHat.Adj lhat (ph 1) := by
      have := ph.adj 0 (by omega)
      rwa [hph0] at this
    have a2 : α.graphHat.Adj lhat (qh 1) := by
      have := qh.adj 0 (by omega)
      rwa [hqh0] at this
    have e2 : ph 1 = qh 1 := hcovι.loc_inj _ _ _ a1 a2 e
    rw [← hphp, ← hqhq]
    simp only [GraphCovering.pathMap_apply, e2]
  have hadj : ∀ zh : α.Γhat, α.graphHat.Adj lhat zh → ι.graph.Adj ι.lv (ι.Θ hι zh) := by
    intro zh hz
    have := hcovι.adj _ _ hz
    rwa [Θ_lhat ι hι] at this
  obtain ⟨g, hg, hgy⟩ := h _ hpb _ hqb hne (ι.Θ hι yh) (ι.Θ hι yh') (hadj _ hyh) (hadj _ hyh')
  have hmι : (hcovι.pathMap ph).stabPath ⊔ (hcovι.pathMap qh).stabPath =
      (α.gam2 ph ⊔ α.gam2 qh).map (f2 (c := ι)) := by
    rw [Subgroup.map_sup, ← stabPath_eq_map_gam2 ι hι ph hph0,
      ← stabPath_eq_map_gam2 ι hι qh hqh0]
  have hmc : p.stabPath ⊔ q.stabPath = (α.gam2 ph ⊔ α.gam2 qh).map (f2 (c := c)) := by
    rw [Subgroup.map_sup, ← stabPath_eq_map_gam2 c hc ph hph0,
      ← stabPath_eq_map_gam2 c hc qh hqh0, hphp, hqhq]
  rw [hmι] at hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  refine ⟨f2 (c := c) a, ?_, ?_⟩
  · rw [hmc]
    exact Subgroup.mem_map_of_mem _ ha
  · have e1 : ι.Θ hι (α.xi2 a • yh) = ι.Θ hι yh' := by
      rw [Θ_smul ι hι, theta0_xi2 ι hι]
      exact hgy
    have hsm : α.graphHat.Adj lhat (α.xi2 a • yh) := by
      have := (GraphAction.adj_smul (α.xi2 a) lhat yh).mpr hyh
      rwa [α.xi2_smul_lhat] at this
    have e2 : α.xi2 a • yh = yh' := hcovι.loc_inj _ _ _ hsm hyh' e1
    have e3 := Θ_smul c hc (α.xi2 a) yh
    rw [e2, theta0_xi2 c hc, hyhe, hyhe'] at e3
    exact e3.symm

end Transfer

end CFSG.Quasithin.TitsGeo
