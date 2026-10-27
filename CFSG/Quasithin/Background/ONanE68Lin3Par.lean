module

public import CFSG.Quasithin.Background.ONanE68Lin3Mat
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3Block
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic

public section

namespace CFSG.Quasithin.E6.E68Proof.Lin3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Lin2.L3Core
  CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.QuasithinUnique.Borel252

variable {F : Type} [Field F]

theorem mem_normalizer_of_comm_hei [Finite F] [CharP F 2] {c : F} (hc : c ≠ 0)
    {y : projectiveSL 3 F} (hy : y * hei 0 0 c = hei 0 0 c * y) :
    y ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, rfl⟩ := proj_surjective 3 F y
  have hB : wMat c * wMat c = 1 := by
    rw [← wMat_add, CharTwo.add_self_eq_zero, QuasithinUnique.Fin257.L3.wMat_zero]
  have hy' : proj 3 F A * proj 3 F (wMat c) = proj 3 F (wMat c) * proj 3 F A := by
    rw [hei_zero_zero] at hy
    exact hy
  have hA := QuasithinUnique.Fin257.L3.comm_of_proj_comm_of_sq hB hy'
  obtain ⟨h10, h20, h21⟩ := entries_comm_wMat hc hA
  have hAup : A ∈ upperTriangular 3 F := by
    rw [mem_upperTriangular]
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd hij (by decide) | simpa using h10 | simpa using h20 | simpa using h21
  rw [normalizer_projUnitriangular (K := F) (n := 3) 2]
  exact Subgroup.mem_map_of_mem _ hAup

theorem not_isSolvable_map_Q3 [Finite F] [CharP F 2] (hF : ∃ s : Finset F, s.card = 4)
    (j : Fin 2) : ¬ Group.IsSolvable ↥((Q3 F j).map (proj 3 F)) := by
  intro hsol
  set H : Subgroup (projectiveSL 3 F) := ((embSL (K := F) j).range).map (proj 3 F) with hH
  have hHle : H ≤ (Q3 F j).map (proj 3 F) :=
    Subgroup.map_mono (by rintro _ ⟨A, rfl⟩; exact embSL_mem_Q3 j A)
  have hsolH : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hHle)
      (Subgroup.inclusion_injective hHle)
  have hperf : ⁅H, H⁆ = H := by
    rw [hH, ← Subgroup.map_commutator, embSL_range_perfect hF j]
  let A₀ : SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hA₀ : A₀ ≠ 1 := fun h => by
    have := congrFun (congrFun (congrArg Subtype.val h) 0) 1
    simp [A₀] at this
  have hmem : embSL (K := F) j A₀ ∈ perfectCore (Q3 F j) := embSL_mem_perfectCore hF j A₀
  have hne1 : proj 3 F (embSL j A₀) ≠ 1 := by
    intro h1
    have hsc : embSL j A₀ ∈ scalars 3 F := proj_eq_one_iff.mp h1
    have h2 := blk3_scalars j ⟨embSL j A₀, hmem⟩ hsc
    have h3 := blk3_embSL hF j A₀
    rw [h2, map_one] at h3
    exact hA₀ h3.symm
  have hHne : H ≠ ⊥ := by
    intro hb
    have hm : proj 3 F (embSL j A₀) ∈ H := Subgroup.mem_map_of_mem _ ⟨A₀, rfl⟩
    rw [hb, Subgroup.mem_bot] at hm
    exact hne1 hm
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHne
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H).ne
    (Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf))

theorem not_isSolvable_of_between [Finite F] [CharP F 2] (hF : ∃ s : Finset F, s.card = 4)
    {Y : Subgroup (projectiveSL 3 F)}
    (hY : Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) < Y) (hYt : Y ≠ ⊤) : ¬ Group.IsSolvable ↥Y := by
  rcases (L3.overgroupData_L3 (F := F)).eq_of_between hY (lt_top_iff_ne_top.mpr hYt) with h | h
  · rw [h]
    exact not_isSolvable_map_Q3 hF 0
  · rw [h]
    exact not_isSolvable_map_Q3 hF 1

end CFSG.Quasithin.E6.E68Proof.Lin3
