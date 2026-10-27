module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieD

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Lattice

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem borel_proj_mem_normalizer_S {b : hypSU h 2 1} (hb : b ∈ hypBorel h 2 1) :
    hypProj h 2 1 b ∈ Subgroup.normalizer
      (((Ssub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) := by
  have := finite_hypPSU_five h
  have hbN : b ∈ Subgroup.normalizer (hypUnitriangular h 2 1 : Set (hypSU h 2 1)) := by
    rw [UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
    exact hb
  obtain ⟨u, hu, t, ht, rfl⟩ := normalizer_eq_mul h (r := 2) (ε := 1) (by norm_num)
    (by norm_num) hbN
  rw [map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨u * s * u⁻¹, conj_mem_Ssub hu hs, by simp [map_mul, map_inv]⟩
  · refine mem_normalizer_of_conj_le fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    have hs' := hs
    rw [Ssub_eq_patSub] at hs'
    refine ⟨t * s * t⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Ssub_eq_patSub]
    exact torus_conj_mem_patSub isPattern_sA₃ ht hs'

theorem u5LnP_le_normalizer_S : u5LnP h ≤ Subgroup.normalizer
    (((Ssub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) := by
  have := finite_hypPSU_five h
  set N := Subgroup.normalizer
    (((Ssub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1)) with hN
  set A : Subgroup (hypSU h 2 1) := N.comap (hypProj h 2 1) with hA
  have hBA : hypBorel h 2 1 ≤ A := fun b hb => borel_proj_mem_normalizer_S hb
  have hc : (1 : K) ∈ h.traceZero := by
    have := h.charP
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
    exact CharTwo.add_self_eq_zero (1 : K)
  obtain ⟨hI, hAI, -, -⟩ := unitary_Borel_overgroups h (r := 2) (ε := 1) (by norm_num)
    (by norm_num) hc one_ne_zero A hBA
  have hlA : lev swapM isUnit_det_swapM ∈ A := by
    show hypProj h 2 1 (lev swapM isUnit_det_swapM) ∈ N
    refine mem_normalizer_of_conj_le fun y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hy
    exact ⟨_, lev_conj_mem_Ssub swapM isUnit_det_swapM hs, by simp [map_mul, map_inv]⟩
  have hlP : lev (hK := h) swapM isUnit_det_swapM ∉ u5PtStab h := by
    rw [mem_u5PtStab_iff]
    intro hcol
    have := hcol ιe₂ (by decide)
    simp [mat_lev, oddDiag, swapM, ιe₁, ιe₂] at this
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hx
  show g ∈ A
  rw [hAI, mem_flagStabilizer]
  intro i hi
  obtain ⟨hi1, hi2⟩ := hI hi
  have hi1' : i ≠ 1 := by
    rintro rfl
    apply hlP
    exact mem_isoStabilizer.2 ((mem_flagStabilizer.1 (hAI ▸ hlA)) 1 hi)
  have hi2' : i = 2 := by omega
  subst hi2'
  exact mem_isoStabilizer.1 hg

theorem pCoreOf_u5LnP_eq : pCoreOf 2 (u5LnP h) = (Ssub h).map (hypProj h 2 1) := by
  refine le_antisymm pCoreOf_u5LnP_le_S ?_
  have hSU : (Ssub h).map (hypProj h 2 1) ≤ hypProjUnitriangular h 2 1 :=
    Subgroup.map_mono Ssub_le_Usub
  exact le_pCoreOf_of_le_normalizer 2 (hSU.trans U_le_u5LnP) u5LnP_le_normalizer_S
    ((u5_sylow h).2.1.to_le hSU)

theorem centerOf_S_eq : centerOf ((Ssub h).map (hypProj h 2 1)) = v5Y h := by
  ext x
  constructor
  · rintro ⟨⟨s₀, hs₀, rfl⟩, hc⟩
    refine ⟨s₀, (central_Ssub_iff hs₀).1 (fun s hs => ?_), rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hc (hypProj h 2 1 s) ⟨s, hs, rfl⟩
    exact hypProj_eq_of_mem_U (mul_mem (Ssub_le_Usub hs) (Ssub_le_Usub hs₀))
      (mul_mem (Ssub_le_Usub hs₀) (Ssub_le_Usub hs)) (by rw [map_mul, map_mul]; exact h1)
  · rintro ⟨v, hv, rfl⟩
    refine ⟨⟨v, Vsub_le_Ssub hv, rfl⟩, ?_⟩
    show hypProj h 2 1 v ∈ Subgroup.centralizer
      (((Ssub h).map (hypProj h 2 1) : Subgroup (hypPSU h 2 1)) : Set (hypPSU h 2 1))
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, (central_Ssub_iff (Vsub_le_Ssub hv)).2 hv s hs]

theorem v5Y_eq_centerOf_pCoreOf : v5Y h = centerOf (pCoreOf 2 (u5LnP h)) := by
  rw [pCoreOf_u5LnP_eq, centerOf_S_eq]

end Lattice

end CFSG.Quasithin.H13.F431.Un
