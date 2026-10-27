module

public import CFSG.Monster.B.GSide.EdgeData
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceFinal
public import CFSG.Monster.B.GSide.Setup

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem clabelS_mem_vStab_cv0_of_adj
    {w : CVert} (hw : cgraph.Adj cv0 w) :
    clabelS w ∈ vStab cv0 := by
  rw [mem_vStab, ← commute_clabel_iff]
  exact ((clabel_adj hw).2.1).symm

theorem clabelS_mem_vStab_cv0_of_dist_three
    {u : CVert} (hu : u ∈ sphereDistThree cv0) :
    clabelS u ∈ vStab cv0 :=
  (native_distance_three_labels_commute_and_fix_endpoints_final hu).1

@[expose] def RA :
    Set (vStab cv0) :=
  {y | ∃ w ∈ cgraph.neighborSet cv0, (y : Shat) = clabelS w}

@[expose] def RB :
    Set (vStab cv0) := {y | cV0 * y ∈ RA}

@[expose] def FA :
    Set (vStab cv0) :=
  {y | ∃ u ∈ sphereDistThree cv0, (y : Shat) = clabelS u}

@[expose] def FB :
    Set (vStab cv0) := {y | cV0 * y ∈ FA}

@[expose] def lamW0H :
    vStab cv0 := ⟨clabelS cw0, clabelS_mem_vStab_cv0_of_adj cgraph_adj_cv0_cw0⟩

theorem lamW0H_mem_RA :
    lamW0H ∈ RA := ⟨cw0, cgraph_adj_cv0_cw0, rfl⟩

theorem clabelS_cvMul
    (v : CVert) (s : Shat) : clabelS (cvMul v s) = s⁻¹ * clabelS v * s :=
  Subtype.ext (by rw [coe_clabelS, clabel_cvMul]; rfl)

theorem isConj_label_iff
    {P : CVert → Prop}
    (hP : ∀ (w : CVert) (s : Shat), s ∈ vStab cv0 → (P (cvMul w s) ↔ P w))
    (htr : ∀ w w', P w → P w' → ∃ s : Shat, s ∈ vStab cv0 ∧ cvMul w s = w')
    {w₀' : CVert} (hw₀ : P w₀') (y₀ : vStab cv0) (hy₀ : (y₀ : Shat) = clabelS w₀')
    (y : vStab cv0) :
    (∃ w, P w ∧ (y : Shat) = clabelS w) ↔ IsConj y₀ y := by
  constructor
  · rintro ⟨w, hw, hy⟩
    obtain ⟨s, hs, hsw⟩ := htr w₀' w hw₀ hw
    refine isConj_iff.2 ⟨⟨s, hs⟩⁻¹, Subtype.ext ?_⟩
    change (⟨s, hs⟩⁻¹ : vStab cv0).1 * y₀.1 * (⟨s, hs⟩⁻¹ : vStab cv0)⁻¹.1 = y.1
    rw [hy, ← hsw, clabelS_cvMul, hy₀]
    simp only [InvMemClass.coe_inv, inv_inv]
  · intro h
    obtain ⟨g, rfl⟩ := isConj_iff.1 h
    refine ⟨cvMul w₀' (g : Shat)⁻¹, (hP _ _ (inv_mem g.2)).2 hw₀, ?_⟩
    rw [clabelS_cvMul, inv_inv, ← hy₀]
    rfl

theorem mem_RA_iff_isConj
    (y : vStab cv0) : y ∈ RA ↔ IsConj lamW0H y := by
  refine isConj_label_iff (P := fun w => cgraph.Adj cv0 w) (fun w s hs => ?_)
    (fun w w' hw hw' => ?_) cgraph_adj_cv0_cw0 lamW0H rfl y
  · have := cgraph_adj_cvMul cv0 w s
    rw [mem_vStab.1 hs] at this
    exact this
  · have h := vStabOrbit_eq_neighborSet hw
    have hw'' : w' ∈ vStabOrbit cv0 w := h ▸ hw'
    obtain ⟨s, hs, rfl⟩ := hw''
    exact ⟨s, hs, rfl⟩

theorem mem_FA_iff_isConj
    {u : CVert} (hu : u ∈ sphereDistThree cv0)
    (y₀ : vStab cv0) (hy₀ : (y₀ : Shat) = clabelS u) (y : vStab cv0) :
    y ∈ FA ↔ IsConj y₀ y := by
  refine isConj_label_iff (P := fun w => w ∈ sphereDistThree cv0) (fun w s hs => ?_)
    (fun w w' hw hw' => ?_) hu y₀ hy₀ y
  · have := dist_cvMul cv0 w s
    rw [mem_vStab.1 hs] at this
    simp only [mem_sphereDistThree, this]
  · have h := (native_coset_graph_diameter_three_rank_five.2.2.2.2.1 cv0).2.2.2.2.2.2.2.2 w hw
    have hw'' : w' ∈ vStabOrbit cv0 w := h ▸ hw'
    obtain ⟨s, hs, rfl⟩ := hw''
    exact ⟨s, hs, rfl⟩

end CFSG.Monster.B.GSide
