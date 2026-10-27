module

public import CFSG.Monster.B.TwoA.Amalgam.DeckUnitary
public import CFSG.Monster.B.TwoA.Amalgam.Chamber

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary Module
open scoped Pointwise

theorem mem_Bam_of_chamberOf_mul_inv_eq
    {h g : Eam}
    (hfix : chamberOf (h * g⁻¹) = chamberOf h) : ((h * g * h⁻¹ : Eam) : Dfull) ∈ Bam := by
  have h1 := chamberOf_eq_iff.1 hfix
  have e : h * (h * g⁻¹)⁻¹ = h * g * h⁻¹ := by group
  rwa [e] at h1

theorem not_mem_Bam_of_mem
    {h : Dfull} {i : Fin 4} (hh : h ∈ Qam i) (hB : h ∉ Bam) :
    h ∉ Pc i := fun hi => hB (Subgroup.mem_iInf.2 fun j => by
  by_cases hj : j = i
  · exact hj ▸ hi
  · exact Qam_le_Pc hj hh)

theorem sigmaAct_eq_of_conj_mem {x u : SigmaU6} (hc : x * u * x⁻¹ ∈ flagStabU)
    {S : Submodule CFSG.Fischer.F4 V6} (hS : S = Rsp ∨ S = Hsp ∨ S = Tsp) :
    sigmaAct (sigmaAct S x) u = sigmaAct S x := by
  have hSs : sigmaAct S (x * u * x⁻¹) = S := by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    rcases hS with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  calc sigmaAct (sigmaAct S x) u = sigmaAct S (x * u) := (sigmaAct_mul S x u).symm
    _ = sigmaAct (sigmaAct S (x * u * x⁻¹)) x := by
      rw [← sigmaAct_mul, inv_mul_cancel_right]
    _ = sigmaAct S x := by rw [hSs]

theorem sigmaAct_lt_of_finrank_lt {S S' : Submodule CFSG.Fischer.F4 V6} (h : S ≤ S')
    (hr : finrank CFSG.Fischer.F4 S < finrank CFSG.Fischer.F4 S') : S < S' :=
  lt_of_le_of_ne h fun e => by rw [e] at hr; exact lt_irrefl _ hr

theorem panel_mem_of_Qam
    {i : Fin 4} (hi : i ≠ 0) {h : Pc 0} (hh : (h : Dfull) ∈ Qam i)
    (hB : (h : Dfull) ∉ Bam) :
    ∃ S : Submodule CFSG.Fischer.F4 V6, (S = Rsp ∨ S = Hsp ∨ S = Tsp) ∧
      ((finrank CFSG.Fischer.F4 (sigmaAct S (rhoP1 h)) = 1 ∧ sigmaAct S (rhoP1 h) < Hsp ∧
          sigmaAct S (rhoP1 h) ≠ Rsp) ∨
        (Rsp < sigmaAct S (rhoP1 h) ∧ sigmaAct S (rhoP1 h) < Tsp ∧
          finrank CFSG.Fischer.F4 (sigmaAct S (rhoP1 h)) = 2 ∧ sigmaAct S (rhoP1 h) ≠ Hsp) ∨
        (Hsp < sigmaAct S (rhoP1 h) ∧ UIso 3 (sigmaAct S (rhoP1 h)) ∧
          sigmaAct S (rhoP1 h) ≠ Tsp)) := by
  have hnot := not_mem_Bam_of_mem hh hB
  have hT : (h : Dfull) ∈ Pc 1 → sigmaAct Tsp (rhoP1 h) = Tsp := fun h1 => by
    have := Subgroup.ext_iff.1 Pc_one_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1 h1
  have hH : (h : Dfull) ∈ Pc 2 → sigmaAct Hsp (rhoP1 h) = Hsp := fun h2 => by
    have := Subgroup.ext_iff.1 Pc_two_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1 h2
  have hR : (h : Dfull) ∈ Pc 3 → sigmaAct Rsp (rhoP1 h) = Rsp := fun h3 => by
    have := Subgroup.ext_iff.1 Pc_three_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.1 h3
  have hT' : sigmaAct Tsp (rhoP1 h) = Tsp → (h : Dfull) ∈ Pc 1 := fun e => by
    have := Subgroup.ext_iff.1 Pc_one_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.2 e
  have hH' : sigmaAct Hsp (rhoP1 h) = Hsp → (h : Dfull) ∈ Pc 2 := fun e => by
    have := Subgroup.ext_iff.1 Pc_two_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.2 e
  have hR' : sigmaAct Rsp (rhoP1 h) = Rsp → (h : Dfull) ∈ Pc 3 := fun e => by
    have := Subgroup.ext_iff.1 Pc_three_subgroupOf h
    rw [Subgroup.mem_subgroupOf] at this
    exact this.2 e
  fin_cases i
  · exact absurd rfl hi
  ·
    have h2 := hH (Qam_le_Pc (by decide) hh)
    refine ⟨Tsp, Or.inr (Or.inr rfl), Or.inr (Or.inr ⟨?_, uIso_Tsp.sigmaAct _,
      fun e => hnot (hT' e)⟩)⟩
    refine sigmaAct_lt_of_finrank_lt ?_ ?_
    · rw [← h2]
      exact sigmaAct_mono Hsp_le_Tsp _
    · rw [finrank_sigmaAct, finrank_Hsp, uIso_Tsp.1]
      norm_num
  ·
    have h1 := hT (Qam_le_Pc (by decide) hh)
    have h3 := hR (Qam_le_Pc (by decide) hh)
    refine ⟨Hsp, Or.inr (Or.inl rfl), Or.inr (Or.inl ⟨?_, ?_, ?_, fun e => hnot (hH' e)⟩)⟩
    · refine sigmaAct_lt_of_finrank_lt ?_ ?_
      · rw [← h3]
        exact sigmaAct_mono Rsp_le_Hsp _
      · rw [finrank_sigmaAct, finrank_Hsp, finrank_Rsp]
        norm_num
    · refine sigmaAct_lt_of_finrank_lt ?_ ?_
      · rw [← h1]
        exact sigmaAct_mono Hsp_le_Tsp _
      · rw [finrank_sigmaAct, finrank_Hsp, uIso_Tsp.1]
        norm_num
    · rw [finrank_sigmaAct, finrank_Hsp]
  ·
    have h2 := hH (Qam_le_Pc (by decide) hh)
    refine ⟨Rsp, Or.inl rfl, Or.inl ⟨by rw [finrank_sigmaAct, finrank_Rsp], ?_,
      fun e => hnot (hR' e)⟩⟩
    refine sigmaAct_lt_of_finrank_lt ?_ ?_
    · rw [← h2]
      exact sigmaAct_mono Rsp_le_Hsp _
    · rw [finrank_sigmaAct, finrank_Hsp, finrank_Rsp]
      norm_num

theorem map_p4Proj_inv_map
    (a : P4) (W : Submodule (ZMod 2) V8) :
    (W.map (p4Proj a : V8 →ₗ[ZMod 2] V8)).map (p4Proj a⁻¹ : V8 →ₗ[ZMod 2] V8) = W := by
  rw [← map_p4Proj_mul, inv_mul_cancel, map_one]
  exact Submodule.map_id W

theorem map_p4Proj_map_inv
    (a : P4) (W : Submodule (ZMod 2) V8) :
    (W.map (p4Proj a⁻¹ : V8 →ₗ[ZMod 2] V8)).map (p4Proj a : V8 →ₗ[ZMod 2] V8) = W := by
  rw [← map_p4Proj_mul, mul_inv_cancel, map_one]
  exact Submodule.map_id W

theorem map_flag4W_eq_iff
    (a : P4) (j : Fin 3) :
    (flag4W j).map (p4Proj a : V8 →ₗ[ZMod 2] V8) = flag4W j ↔ (a : Dfull) ∈ Pc j.castSucc := by
  rw [← mem_flag4H_iff, flag4H, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩

theorem orth_panel_mem_of_Qam
    {h : P4} (hh : (h : Dfull) ∈ Qam 0) (hB : (h : Dfull) ∉ Bam) :
    finrank (ZMod 2) ((flag4W 0).map (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8)) = 1 ∧
      (flag4W 0).map (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8) ≤ flag4W 1 ∧
      (flag4W 0).map (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8) ≠ flag4W 0 := by
  have hnot := not_mem_Bam_of_mem hh hB
  have h1 : (flag4W 1).map (p4Proj h : V8 →ₗ[ZMod 2] V8) = flag4W 1 :=
    (map_flag4W_eq_iff h 1).2 (Qam_le_Pc (by decide) hh)
  refine ⟨?_, ?_, fun e => hnot ((map_flag4W_eq_iff h 0).1 ?_)⟩
  · rw [show (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8) =
      ((p4Proj h⁻¹ : V8 ≃ₗ[ZMod 2] V8) : V8 →ₗ[ZMod 2] V8) from rfl,
      LinearEquiv.finrank_map_eq]
    exact (flag4W_mem 0).1
  · calc (flag4W 0).map (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8)
        ≤ (flag4W 1).map (p4Proj h⁻¹ : V8 →ₗ[ZMod 2] V8) :=
          Submodule.map_mono (flag4W_mono (by decide))
      _ = flag4W 1 := by
          conv_lhs => rw [← h1]
          exact map_p4Proj_inv_map h (flag4W 1)
  · conv_lhs => rw [← e]
    exact map_p4Proj_map_inv h (flag4W 0)

section Panels

variable {G Δ : Type*} [Group G] [MulAction G Δ] {π : Δ → Chamber} {p : G → Equiv.Perm Chamber}

theorem exists_smul_ne_of_unitary_panel
    (hπ : ∀ (z : G) (y : Δ), π (z • y) = p z (π y))
    {P₁ : Subgroup G} {φ₁ : Pc 0 →* P₁} (hφ₁ : Function.Surjective φ₁)
    (hφ₁p : ∀ (g : Pc 0) (c : Chamber),
      p (φ₁ g : G) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 0) g)⁻¹)
    {α₁ : P₁ →* SigmaU6} (hα₁ : ∀ g, α₁ (φ₁ g) = rhoP1 g) {T : Set G}
    (hTU : ∀ u ∈ psuSub ⊓ flagStabU, ∃ z : P₁, (z : G) ∈ T ∧ α₁ z = u)
    {i : Fin 4} (hi : i ≠ 0) {y : Δ} {h : Eam} (hy : π y = chamberOf h)
    (hhQ : (h : Dfull) ∈ Qam i) (hhB : (h : Dfull) ∉ Bam) : ∃ t ∈ T, t • y ≠ y := by
  have hh0 : (h : Dfull) ∈ Pc 0 := Qam_le_Pc (Ne.symm hi) hhQ
  set h' : Pc 0 := ⟨h, hh0⟩ with hh'
  obtain ⟨S, hS, hX⟩ := panel_mem_of_Qam hi (h := h') hhQ hhB
  obtain ⟨u, hu, hmove⟩ := exists_psu_flag_moves hX
  obtain ⟨z, hzT, hzu⟩ := hTU u hu
  obtain ⟨g, rfl⟩ := hφ₁ z
  refine ⟨φ₁ g, hzT, fun hfix => hmove ?_⟩
  have hc : chamberOf (h * (Subgroup.inclusion (Pc_le_Eam 0) g)⁻¹) = chamberOf h := by
    have := congrArg π hfix
    rw [hπ, hy, hφ₁p, chamberMul_chamberOf] at this
    exact this
  have hB := mem_Bam_of_chamberOf_mul_inv_eq hc
  have hBP : h' * g * h'⁻¹ ∈ Bam.subgroupOf (Pc 0) := hB
  rw [Bam_subgroupOf_Pc0, Subgroup.mem_comap, map_mul, map_mul, map_inv] at hBP
  rw [← hzu, hα₁]
  exact sigmaAct_eq_of_conj_mem hBP hS

theorem exists_smul_ne_of_orth_panel
    (hπ : ∀ (z : G) (y : Δ), π (z • y) = p z (π y))
    {P₄ : Subgroup G} {φ₄ : P4 →* P₄} (hφ₄ : Function.Surjective φ₄)
    (hφ₄p : ∀ (g : P4) (c : Chamber),
      p (φ₄ g : G) c = chamberMul c (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g)⁻¹)
    {α₄ : P₄ →* OA8} (hα₄ : ∀ g, α₄ (φ₄ g) = p4Proj g) {T : Set G}
    (hTO : ∀ d ∈ orthD ⊓ flagStabO, ∃ z : P₄, (z : G) ∈ T ∧ α₄ z = d)
    {y : Δ} {h : Eam} (hy : π y = chamberOf h) (hhQ : (h : Dfull) ∈ Qam 0)
    (hhB : (h : Dfull) ∉ Bam) : ∃ t ∈ T, t • y ≠ y := by
  have hh3 : (h : Dfull) ∈ P4 := Qam_le_Pc (j := 3) (by decide) hhQ
  set h' : P4 := ⟨h, hh3⟩ with hh'
  obtain ⟨hM1, hM2, hMne⟩ := orth_panel_mem_of_Qam (h := h') hhQ hhB
  obtain ⟨d, hdD, hd0, hd1, hd2, hmove⟩ := exists_orthD_flag_moves hM1 hM2 hMne
  obtain ⟨z, hzT, hzd⟩ := hTO d ⟨hdD, ⟨⟨hd0, hd1⟩, hd2⟩⟩
  obtain ⟨g, rfl⟩ := hφ₄ z
  refine ⟨φ₄ g, hzT, fun hfix => hmove ?_⟩
  have hc : chamberOf (h * (Subgroup.inclusion (Pc_le_Eam 3 : P4 ≤ Eam) g)⁻¹) = chamberOf h := by
    have := congrArg π hfix
    rw [hπ, hy, hφ₄p, chamberMul_chamberOf] at this
    exact this
  have hB := mem_Bam_of_chamberOf_mul_inv_eq hc
  have hBP : h' * g * h'⁻¹ ∈ Bam.subgroupOf P4 := hB
  rw [Bam_subgroupOf_P4, Subgroup.mem_comap] at hBP
  have h0 : (flag4W 0).map (p4Proj (h' * g * h'⁻¹) : V8 →ₗ[ZMod 2] V8) = flag4W 0 := hBP.1.1
  rw [map_p4Proj_mul, map_p4Proj_mul] at h0
  have key := congrArg (fun W : Submodule (ZMod 2) V8 =>
    W.map (p4Proj h'⁻¹ : V8 →ₗ[ZMod 2] V8)) h0
  simp only [map_p4Proj_inv_map] at key
  rw [← hzd, hα₄]
  exact key

end Panels

end CFSG.Monster.B.TwoA.Amalgam
