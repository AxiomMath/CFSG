module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Ind
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Tight
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3ExDih

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

@[expose] def eightArc (Q₀ Q₂ : Arc Γ 4) (h : Q₀.vert 0 = Q₂.vert 0)
    (hne : Q₀.vert 1 ≠ Q₂.vert 1) : Arc Γ 8 :=
  Arc.append (Arc.rev Q₀) Q₂ (by rw [Arc.rev_vert]; simpa using h)
    (fun _ _ => by rw [Arc.rev_vert]; exact hne)

theorem eightArc_vert_le {Q₀ Q₂ : Arc Γ 4} {h : Q₀.vert 0 = Q₂.vert 0}
    {hne : Q₀.vert 1 ≠ Q₂.vert 1} {m : ℕ} (hm : m ≤ 4) :
    (eightArc Q₀ Q₂ h hne).vert m = Q₀.vert (4 - m) := by
  rw [eightArc, Arc.append_vert_le _ _ _ _ hm, Arc.rev_vert]

theorem eightArc_vert_ge {Q₀ Q₂ : Arc Γ 4} {h : Q₀.vert 0 = Q₂.vert 0}
    {hne : Q₀.vert 1 ≠ Q₂.vert 1} {m : ℕ} (hm : 4 ≤ m) :
    (eightArc Q₀ Q₂ h hne).vert m = Q₂.vert (m - 4) := by
  rw [eightArc, Arc.append_vert_ge _ _ _ _ hm]

theorem tight_of_fan71a {F : FanTree Γ G} {L : ZLab Γ G} (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h65 : Fan65 F) (R : Arc Γ 8) (h5 : valence Γ (R.vert 4) = 5) :
    RightTransitive Γ G R.vert 3 5 ∧ RightTransitive Γ G R.vert 3 6 ∧
      RightTransitive Γ G R.vert 3 7 ∧ LeftTransitive Γ G R.vert 3 8 ∧
      LeftTransitive Γ G R.vert 2 8 ∧ LeftTransitive Γ G R.vert 1 8 := by
  have hT := F.isTree
  have hd0 : Γ.dist (R.vert 4) (R.vert 0) = 4 := by
    have := Arc.dist_vert hT R (i := 0) (j := 4) (by norm_num) (by norm_num)
    rw [SimpleGraph.dist_comm]
    omega
  have hd8 : Γ.dist (R.vert 4) (R.vert 8) = 4 := by
    have := Arc.dist_vert hT R (i := 4) (j := 8) (by norm_num) le_rfl
    omega
  have hv0 : valence Γ (R.vert 0) = 5 := valence_of_dist_even F h5 (by rw [hd0])
  have hv8 : valence Γ (R.vert 8) = 5 := valence_of_dist_even F h5 (by rw [hd8])
  obtain ⟨⟨φ⟩, hcent⟩ := h71a R hv0
  have hne : L.z (R.vert 8) ≠ L.z (R.vert 0) := fun h => by
    have h' := h71c.z_injective hv8 hv0 h
    have := Arc.vert_injOn hT R (i := 0) (j := 8) (by norm_num) (by norm_num) h'.symm
    omega
  have hr := dihedral_orderOf_rot (L.z_mul_self hv8) (L.z_mul_self hv0) (L.z_ne_one hv8)
    (L.z_ne_one hv0) hne φ
  have hx : L.z (R.vert 8) * L.z (R.vert 0) ∈ MulAction.stabilizer G (R.vert 4) :=
    Subgroup.mul_mem _ ((h71c.z_mem_stabilizer_iff hv8 _).2 (by rw [SimpleGraph.dist_comm, hd8]))
      ((h71c.z_mem_stabilizer_iff hv0 _).2 (by rw [SimpleGraph.dist_comm, hd0]))
  have hxcl : L.z (R.vert 8) * L.z (R.vert 0) ∈
      Subgroup.closure ({L.z (R.vert 0), L.z (R.vert 8)} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hceq := hcent _ hxcl hr
  have hcentx : ∀ g ∈ R.stab G, g * (L.z (R.vert 8) * L.z (R.vert 0)) =
      (L.z (R.vert 8) * L.z (R.vert 0)) * g := fun g hg => by
    rw [← hceq] at hg
    exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2) _ (by simp)).symm
  exact P71.R_tight F R h5 hcentx (h65.1 (R.vert 4) h5 _ hx hr)

theorem exists_stab_pair {F : FanTree Γ G} {L : ZLab Γ G} (h71a : Fan71a F L)
    (h71c : Fan71c F L) (h65 : Fan65 F) {α : V} (hα : valence Γ α = 5)
    (Q₀ Q₂ Q₀' Q₂' : Arc Γ 4) (h0 : Q₀.vert 0 = α) (h2 : Q₂.vert 0 = α) (h0' : Q₀'.vert 0 = α)
    (h2' : Q₂'.vert 0 = α) (hne : Q₀.vert 1 ≠ Q₂.vert 1) (hne' : Q₀'.vert 1 ≠ Q₂'.vert 1) :
    ∃ g : G, (∀ m, m ≤ 4 → g • Q₀.vert m = Q₀'.vert m) ∧
      ∀ m, m ≤ 4 → g • Q₂.vert m = Q₂'.vert m := by
  have e1 : Q₀.vert 0 = Q₂.vert 0 := h0.trans h2.symm
  have e2 : Q₀'.vert 0 = Q₂'.vert 0 := h0'.trans h2'.symm
  have hA5 : valence Γ ((eightArc Q₀ Q₂ e1 hne).vert 4) = 5 := by
    rw [eightArc_vert_le (by norm_num)]
    simpa [h0] using hα
  have hB5 : valence Γ ((eightArc Q₀' Q₂' e2 hne').vert 4) = 5 := by
    rw [eightArc_vert_le (by norm_num)]
    simpa [h0'] using hα
  obtain ⟨g, hg⟩ := P71.exists_smul_arc F _ hA5 (tight_of_fan71a h71a h71c h65 _ hA5) _ hB5
  refine ⟨g, fun m hm => ?_, fun m hm => ?_⟩
  · have := hg (4 - m) (by omega)
    rwa [eightArc_vert_le (by omega), eightArc_vert_le (by omega), show 4 - (4 - m) = m by omega]
      at this
  · have := hg (4 + m) (by omega)
    rwa [eightArc_vert_ge (by omega), eightArc_vert_ge (by omega), show 4 + m - 4 = m by omega]
      at this

end P4X

end CFSG.Quasithin.Fan86
