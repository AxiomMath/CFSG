module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYModule
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryRootGen
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryCommutator
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitGeometryWeyl

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open scoped commutatorElement

section RootGeneration

theorem d4SmulMemRoots {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {α : Fin 4 → ℤ} (hα : α ∈ roots 4) :
    ε • α ∈ roots 4 := by
  rcases hε with rfl | rfl
  · rwa [one_smul]
  · rw [neg_one_smul]
    exact neg_mem_roots hα

theorem d4SubEpsMemRoots {i j : Fin 4} (h : i < j) :
    OrthogonalSplit.eps 4 i - OrthogonalSplit.eps 4 j ∈ roots 4 :=
  ⟨i, j, h, Or.inl rfl⟩

theorem d4AddEpsMemRoots {i j : Fin 4} (h : i < j) :
    OrthogonalSplit.eps 4 i + OrthogonalSplit.eps 4 j ∈ roots 4 :=
  ⟨i, j, h, Or.inr (Or.inr (Or.inl rfl))⟩

variable {K : Type} [Field K]

theorem d4RootSubgroup_add_le {H : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))}
    {α β : Fin 4 → ℤ} (hα : α ∈ roots 4) (hβ : β ∈ roots 4) (hαβ : α + β ∈ roots 4)
    (h1 : rootSubgroup 4 K α ≤ H) (h2 : rootSubgroup 4 K β ≤ H) :
    rootSubgroup 4 K (α + β) ≤ H := by
  obtain ⟨c, hc, hcomm⟩ :=
    (orthogonal_geometry_split_root_commutators (K := K) (r := 4)).2.2 α hα β hβ hαβ
  rintro _ ⟨s, rfl⟩
  have hs : (c : K) * ((c : K) * s) * 1 = s := by
    rcases hc with rfl | rfl <;> simp
  rw [← hs, ← hcomm ((c : K) * s) 1, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (h1 ⟨_, rfl⟩) (h2 ⟨_, rfl⟩)) (inv_mem (h1 ⟨_, rfl⟩)))
    (inv_mem (h2 ⟨_, rfl⟩))

theorem d4RootSubgroup_smul_posRoots_le
    {H : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))} {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) (hX : ∀ k, rootSubgroup 4 K (ε • OrthogonalSplit.simpleRoot 4 k) ≤ H)
    {β : Fin 4 → ℤ} (hβ : β ∈ posRoots 4) : rootSubgroup 4 K (ε • β) ≤ H := by
  have step : ∀ {a b c : Fin 4 → ℤ}, a ∈ roots 4 → b ∈ roots 4 → c ∈ roots 4 → a + b = c →
      rootSubgroup 4 K (ε • a) ≤ H → rootSubgroup 4 K (ε • b) ≤ H →
        rootSubgroup 4 K (ε • c) ≤ H := by
    intro a b c ha hb hc e h1 h2
    have := d4RootSubgroup_add_le (d4SmulMemRoots hε ha) (d4SmulMemRoots hε hb)
      (by rw [← smul_add, e]; exact d4SmulMemRoots hε hc) h1 h2
    rwa [← smul_add, e] at this
  have s0 := hX 0
  have s1 := hX 1
  have s2 := hX 2
  have s3 := hX 3
  rw [simpleRoot_zero] at s0
  rw [simpleRoot_one] at s1
  rw [simpleRoot_two] at s2
  rw [simpleRoot_three] at s3
  have m02 := step (d4SubEpsMemRoots (i := 0) (j := 1) (by decide))
    (d4SubEpsMemRoots (i := 1) (j := 2) (by decide)) (d4SubEpsMemRoots (i := 0) (j := 2)
      (by decide)) (by abel) s0 s1
  have m13 := step (d4SubEpsMemRoots (i := 1) (j := 2) (by decide))
    (d4SubEpsMemRoots (i := 2) (j := 3) (by decide)) (d4SubEpsMemRoots (i := 1) (j := 3)
      (by decide)) (by abel) s1 s2
  have m03 := step (d4SubEpsMemRoots (i := 0) (j := 2) (by decide))
    (d4SubEpsMemRoots (i := 2) (j := 3) (by decide)) (d4SubEpsMemRoots (i := 0) (j := 3)
      (by decide)) (by abel) m02 s2
  have p13 := step (d4SubEpsMemRoots (i := 1) (j := 2) (by decide))
    (d4AddEpsMemRoots (i := 2) (j := 3) (by decide)) (d4AddEpsMemRoots (i := 1) (j := 3)
      (by decide)) (by abel) s1 s3
  have p03 := step (d4SubEpsMemRoots (i := 0) (j := 2) (by decide))
    (d4AddEpsMemRoots (i := 2) (j := 3) (by decide)) (d4AddEpsMemRoots (i := 0) (j := 3)
      (by decide)) (by abel) m02 s3
  have p12 := step (d4SubEpsMemRoots (i := 1) (j := 3) (by decide))
    (d4AddEpsMemRoots (i := 2) (j := 3) (by decide)) (d4AddEpsMemRoots (i := 1) (j := 2)
      (by decide)) (by abel) m13 s3
  have p02 := step (d4SubEpsMemRoots (i := 0) (j := 3) (by decide))
    (d4AddEpsMemRoots (i := 2) (j := 3) (by decide)) (d4AddEpsMemRoots (i := 0) (j := 2)
      (by decide)) (by abel) m03 s3
  have p01 := step (d4SubEpsMemRoots (i := 0) (j := 2) (by decide))
    (d4AddEpsMemRoots (i := 1) (j := 2) (by decide)) (d4AddEpsMemRoots (i := 0) (j := 1)
      (by decide)) (by abel) m02 p12
  obtain ⟨i, j, hij, rfl | rfl⟩ := hβ
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem d4RootSupr_le_of {H : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))}
    (hX : ∀ k c, rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c ∈ H)
    (hY : ∀ k c, rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c ∈ H) : rootSupr 4 K ≤ H := by
  refine iSup₂_le fun α hα => ?_
  rcases (mem_posRoots_or_neg_mem_posRoots hα).1 with h | h
  · have := d4RootSubgroup_smul_posRoots_le (ε := 1) (Or.inl rfl) (fun k => by
      rw [one_smul]
      rintro _ ⟨c, rfl⟩
      exact hX k c) h
    rwa [one_smul] at this
  · have := d4RootSubgroup_smul_posRoots_le (ε := -1) (Or.inr rfl) (fun k => by
      rw [neg_one_smul]
      rintro _ ⟨c, rfl⟩
      exact hY k c) h
    rwa [neg_one_smul, neg_neg] at this

theorem d4Unipotent_le_of {H : Subgroup ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))}
    (hX : ∀ k c, rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c ∈ H) : unipotent 4 K ≤ H := by
  refine iSup₂_le fun β hβ => ?_
  have := d4RootSubgroup_smul_posRoots_le (ε := 1) (Or.inl rfl) (fun k => by
    rw [one_smul]
    rintro _ ⟨c, rfl⟩
    exact hX k c) hβ
  rwa [one_smul] at this

end RootGeneration

section Psi


variable (K : Type) [Field K]

noncomputable abbrev d4Levi : Subgroup (ModGL Tag.E6 K) := subsystemGroup Tag.E6 K setD

@[expose] noncomputable def d4RestrictEnd : d4Levi K →* Module.End K (d4Module K) where
  toFun g := ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)).restrict
    (mem_d4Module_of_mem_subsystemGroup g.2)
  map_one' := LinearMap.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => rfl

@[expose] noncomputable def d4Psi : d4Levi K →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 4 ⊕ Fin 4 → K)).toMonoidHom.comp
    ((Units.map (d4Phi K).conjRingEquiv.toMonoidHom).comp (d4RestrictEnd K).toHomUnits)

variable {K}

theorem d4RestrictEnd_apply (g : d4Levi K) (v : d4Module K) :
    ((d4RestrictEnd K g v : d4Module K) : RootModule Tag.E6 K) =
      ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v :=
  rfl

theorem d4Psi_apply (g : d4Levi K) (x : Fin 4 ⊕ Fin 4 → K) :
    d4Psi K g x = d4Phi K (d4RestrictEnd K g ((d4Phi K).symm x)) :=
  rfl

theorem d4Psi_phi (g : d4Levi K) {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4Psi K g (d4Phi K ⟨v, hv⟩) =
      d4Phi K ⟨((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v,
        mem_d4Module_of_mem_subsystemGroup g.2 v hv⟩ := by
  rw [d4Psi_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem d4Psi_eq_one_iff (g : d4Levi K) :
    d4Psi K g = 1 ↔
      ∀ v ∈ d4Module K, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v = v := by
  constructor
  · intro h v hv
    have h1 := LinearEquiv.congr_fun h (d4Phi K ⟨v, hv⟩)
    rw [d4Psi_phi] at h1
    exact congrArg Subtype.val ((d4Phi K).injective h1)
  · intro h
    refine LinearEquiv.ext fun x => ?_
    rw [d4Psi_apply]
    have : d4RestrictEnd K g ((d4Phi K).symm x) = (d4Phi K).symm x :=
      Subtype.ext (h _ ((d4Phi K).symm x).2)
    rw [this, LinearEquiv.apply_symm_apply]
    rfl

theorem d4_jD_mem_setD (k : Fin 4) : jD k ∈ setD := by
  fin_cases k
  exacts [Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inl rfl),
    Or.inr (Or.inr (Or.inr rfl))]

theorem xUnit_mem_d4Levi (k : Fin 4) (c : K) : xUnit Tag.E6 K (jD k) c ∈ d4Levi K :=
  Subgroup.subset_closure ⟨jD k, d4_jD_mem_setD k, c, Or.inl rfl⟩

theorem yUnit_mem_d4Levi (k : Fin 4) (c : K) : yUnit Tag.E6 K (jD k) c ∈ d4Levi K :=
  Subgroup.subset_closure ⟨jD k, d4_jD_mem_setD k, c, Or.inr rfl⟩

theorem d4Psi_xUnit [CharP K 2] (k : Fin 4) (c : K) :
    d4Psi K ⟨xUnit Tag.E6 K (jD k) c, xUnit_mem_d4Levi k c⟩ =
      rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c := by
  refine LinearEquiv.ext fun x => ?_
  rw [d4Psi_apply]
  have h := d4Phi_xOp k c ((d4Phi K).symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem d4Psi_yUnit [CharP K 2] (k : Fin 4) (c : K) :
    d4Psi K ⟨yUnit Tag.E6 K (jD k) c, yUnit_mem_d4Levi k c⟩ =
      rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c := by
  refine LinearEquiv.ext fun x => ?_
  rw [d4Psi_apply]
  have h := d4Phi_yOp k c ((d4Phi K).symm x).2
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem closure_d4Gens_eq_top :
    Subgroup.closure (((↑) : d4Levi K → ModGL Tag.E6 K) ⁻¹'
      {g | ∃ i ∈ setD, ∃ c : K, g = xUnit Tag.E6 K i c ∨ g = yUnit Tag.E6 K i c}) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

variable [CharP K 2]

theorem d4Psi_range_le : (d4Psi K).range ≤ orthElementaryGroup (quadPlus 4 K) := by
  rw [MonoidHom.range_eq_map, ← closure_d4Gens_eq_top, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨i, hi, c, hg | hg⟩, rfl⟩
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    have e : g = ⟨xUnit Tag.E6 K (jD k) c, xUnit_mem_d4Levi k c⟩ := Subtype.ext hg
    rw [e, d4Psi_xUnit]
    exact rootElt_mem _ _
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    have e : g = ⟨yUnit Tag.E6 K (jD k) c, yUnit_mem_d4Levi k c⟩ := Subtype.ext hg
    rw [e, d4Psi_yUnit]
    exact rootElt_mem _ _

theorem range_d4Psi : (d4Psi K).range = orthElementaryGroup (quadPlus 4 K) := by
  refine le_antisymm d4Psi_range_le ?_
  rw [(orthogonal_geometry_split_root_generation (K := K) (r := 4) (by norm_num)).1]
  exact d4RootSupr_le_of (fun k c => ⟨_, d4Psi_xUnit k c⟩) (fun k c => ⟨_, d4Psi_yUnit k c⟩)

end Psi

end CFSG.SeitzReduction.TwistedE6Pilot
