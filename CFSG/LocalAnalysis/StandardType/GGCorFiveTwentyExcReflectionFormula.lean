module

public import CFSG.LieType.Chevalley.LangWeylChamberStabilizers
public import CFSG.LieType.Chevalley.LangWeylInvolutionReflections
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots
public import Mathlib.Algebra.Module.Submodule.Union
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootSpace
  CFSG.LieType.Steinberg.Adjoint Module

variable {τ : Tag}

theorem exists_reflection_formula_of_finrank_ker_add_one {w : WeylGroup τ} (hw : w * w = 1)
    (hdim : finrank ℝ (LinearMap.ker (weylLinear τ w + 1)) = 1) :
    ∃ x : RootSpace τ, x ≠ 0 ∧ ∀ v : RootSpace τ,
      weylAct τ w v = v - (2 * inner ℝ x v / inner ℝ x x) • x := by
  set f : Module.End ℝ (RootSpace τ) := weylLinear τ w with hf
  have hff : f * f = 1 := by
    rw [hf, ← map_mul, hw, map_one]
  have hff_apply : ∀ v : RootSpace τ, f (f v) = v := fun v => by
    have h := congrArg (fun g : Module.End ℝ (RootSpace τ) => g v) hff
    simpa only [Module.End.mul_apply, Module.End.one_apply] using h
  have hmem : ∀ v : RootSpace τ, v - f v ∈ LinearMap.ker (f + 1) := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply]
    simp only [map_sub, hff_apply]
    abel
  have hKdim : finrank ℝ (LinearMap.ker (f + 1)) = 1 := by rw [hf]; exact hdim
  obtain ⟨x, hx0, hxspan⟩ :=
    (finrank_eq_one_iff' (K := ℝ) (V := LinearMap.ker (f + 1))).mp hKdim
  have hxne : (x : RootSpace τ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hxneg : f (x : RootSpace τ) = -(x : RootSpace τ) := by
    have hker : (f + 1) (x : RootSpace τ) = 0 := x.2
    rw [LinearMap.add_apply, Module.End.one_apply] at hker
    exact eq_neg_of_add_eq_zero_left hker
  have hiso : ∀ v : RootSpace τ,
      inner ℝ (f v) (f (x : RootSpace τ)) = inner ℝ v (x : RootSpace τ) :=
    fun v => inner_weylLinear w v (x : RootSpace τ)
  refine ⟨(x : RootSpace τ), hxne, fun v => ?_⟩
  obtain ⟨c, hc⟩ := hxspan ⟨v - f v, hmem v⟩
  have hcval : c • (x : RootSpace τ) = v - f v := by
    simpa using congrArg Subtype.val hc
  have hfv : f v = v - c • (x : RootSpace τ) := by
    rw [hcval]
    abel
  have hc_eq : c = 2 * inner ℝ (x : RootSpace τ) v /
      inner ℝ (x : RootSpace τ) (x : RootSpace τ) := by
    have h := hiso v
    rw [hfv, hxneg, inner_neg_right, inner_sub_left, real_inner_smul_left,
      ← real_inner_comm v (x : RootSpace τ)] at h
    have hmain : c * inner ℝ (x : RootSpace τ) (x : RootSpace τ) =
        2 * inner ℝ (x : RootSpace τ) v := by linarith
    rw [eq_div_iff (inner_self_ne_zero.mpr hxne)]
    exact hmain
  rw [weylAct_apply, hfv, hc_eq]

theorem rootReflection_eq_of_forall_inner_ne_zero (hτ : ∀ i, τ.symmetrizer i i = 1)
    {x : RootSpace τ} (hx : x ≠ 0) {v₀ : RootSpace τ}
    (hv₀ : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∃ v ∈ (ℝ ∙ x : Submodule ℝ (RootSpace τ))ᗮ, inner ℝ (ofLattice α) v ≠ 0) →
        inner ℝ (ofLattice α) v₀ ≠ 0)
    {α α' : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hα' : IsRoot τ α')
    (hαv : inner ℝ (ofLattice α) v₀ = 0) (hα'v : inner ℝ (ofLattice α') v₀ = 0) :
    rootReflection α' = rootReflection α := by
  have horth : ((ℝ ∙ x : Submodule ℝ (RootSpace τ))ᗮ)ᗮ = ℝ ∙ x := by
    rw [Submodule.orthogonal_orthogonal_eq_closure]
    exact Submodule.topologicalClosure_eq_self _
  have hmem : ∀ {β : Fin τ.rank → ℤ}, IsRoot τ β → inner ℝ (ofLattice β) v₀ = 0 →
      ofLattice β ∈ ((ℝ ∙ x : Submodule ℝ (RootSpace τ))ᗮ)ᗮ := by
    intro β hβ hβv
    rw [Submodule.mem_orthogonal']
    intro u hu
    by_contra hne
    exact absurd hβv (hv₀ β hβ ⟨u, hu, hne⟩)
  have hαx : ofLattice α ∈ (ℝ ∙ x : Submodule ℝ (RootSpace τ)) := by
    rw [← horth]
    exact hmem hα hαv
  have hα'x : ofLattice α' ∈ (ℝ ∙ x : Submodule ℝ (RootSpace τ)) := by
    rw [← horth]
    exact hmem hα' hα'v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hαx
  obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.1 hα'x
  obtain ⟨c₀, -, hinner⟩ := exists_inner_ofLattice_eq_iform τ
  have hα2 : (iform α α : ℝ) = 2 := by
    rw [CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hα]
    norm_num
  have hα'2 : (iform α' α' : ℝ) = 2 := by
    rw [CFSG.LieType.Chevalley.SimplyLacedCover.iform_self_eq_two hτ hα']
    norm_num
  have hcx : inner ℝ (ofLattice α) (ofLattice α) = c ^ 2 * inner ℝ x x := by
    rw [← hc, real_inner_smul_left, real_inner_smul_right]
    ring
  have hcx' : inner ℝ (ofLattice α') (ofLattice α') = c' ^ 2 * inner ℝ x x := by
    rw [← hc', real_inner_smul_left, real_inner_smul_right]
    ring
  have h1 : c ^ 2 * inner ℝ x x = c₀ * 2 := by
    rw [← hcx, hinner α α, hα2]
  have h2 : c' ^ 2 * inner ℝ x x = c₀ * 2 := by
    rw [← hcx', hinner α' α', hα'2]
  have hsq : c ^ 2 = c' ^ 2 :=
    mul_right_cancel₀ (inner_self_ne_zero.mpr hx) (by rw [h1, h2])
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hcc | hcc
  · have heq : α' = α := ofLattice_injective (by rw [← hc', ← hc, hcc])
    rw [heq]
  · have hc'x : c' • x = ofLattice (-α) := by
      rw [ofLattice_neg, ← hc, ← neg_smul]
      congr 1
      linarith
    have heq : α' = -α := ofLattice_injective (by rw [← hc', hc'x])
    rw [heq, rootReflection_neg hα]

theorem exists_rootReflection_of_reflection_formula (hτ : ∀ i, τ.symmetrizer i i = 1)
    {w : WeylGroup τ} (hw1 : w ≠ 1) {x : RootSpace τ} (hx : x ≠ 0)
    (hform : ∀ v : RootSpace τ, weylAct τ w v = v - (2 * inner ℝ x v / inner ℝ x x) • x) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ w = rootReflection β := by
  classical
  let H : Submodule ℝ (RootSpace τ) := (ℝ ∙ x)ᗮ
  let ι := {γ : Fin τ.rank → ℤ // IsRoot τ γ ∧ ∃ v ∈ H, inner ℝ (ofLattice γ) v ≠ 0}
  haveI : Finite ι := (finite_setOf_isRoot τ).subset (fun _ h => h.1)
  obtain ⟨v₀, hv₀H, hv₀⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists (K := ℝ) H
    (fun γ : ι => innerₗ (RootSpace τ) (ofLattice γ.1))
    (fun γ => by
      obtain ⟨v, hv, hvne⟩ := γ.2.2
      exact ⟨v, hv, by simpa only [innerₗ_apply_apply] using hvne⟩)
  have hv₀' : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∃ v ∈ H, inner ℝ (ofLattice α) v ≠ 0) → inner ℝ (ofLattice α) v₀ ≠ 0 := by
    intro α hα hex
    have h := hv₀ ⟨α, hα, hex⟩
    simpa only [innerₗ_apply_apply] using h
  have hxv : inner ℝ x v₀ = 0 :=
    (Submodule.mem_orthogonal (K := ℝ ∙ x) v₀).1 hv₀H x (Submodule.mem_span_singleton_self x)
  have hfix : weylAct τ w v₀ = v₀ := by
    rw [hform v₀]
    simp [hxv]
  have hwstab : w ∈ weylStabilizer τ v₀ := by
    rw [mem_weylStabilizer]
    exact hfix
  have hstab := (exceptional_Lang_Weyl_chamber_point_stabilizers τ).2.2.2.2.2 v₀
  rw [hstab] at hwstab
  rcases Set.eq_empty_or_nonempty
      {s : WeylGroup τ | ∃ α, IsRoot τ α ∧ inner ℝ (ofLattice α) v₀ = 0 ∧ s = rootReflection α}
      with hS | ⟨r₀, hr₀⟩
  · rw [hS, Subgroup.closure_empty] at hwstab
    exact absurd (Subgroup.mem_bot.1 hwstab) hw1
  · obtain ⟨α, hα, hαv, hr₀eq⟩ := hr₀
    have hr₀sq : r₀ * r₀ = 1 := by
      rw [hr₀eq]
      exact rootReflection_mul_self hα
    have hle : Subgroup.closure
        {s : WeylGroup τ | ∃ α, IsRoot τ α ∧ inner ℝ (ofLattice α) v₀ = 0 ∧ s = rootReflection α}
        ≤ Subgroup.zpowers r₀ := by
      rw [Subgroup.closure_le]
      rintro s ⟨α', hα', hα'v, rfl⟩
      have heq : rootReflection α' = r₀ := by
        rw [rootReflection_eq_of_forall_inner_ne_zero hτ hx hv₀' hα hα' hαv hα'v, ← hr₀eq]
      rw [heq]
      exact Subgroup.mem_zpowers r₀
    have hwz : w ∈ Subgroup.zpowers r₀ := hle hwstab
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hwz
    have h2 : r₀ ^ (2 : ℤ) = 1 := by rw [zpow_two, hr₀sq]
    have hw_eq : w = r₀ := by
      have hmod : r₀ ^ n = r₀ ^ (n % 2) := zpow_eq_zpow_emod n h2
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · rw [h0, zpow_zero] at hmod
        exact absurd (hn.symm.trans hmod) hw1
      · rw [h1, zpow_one] at hmod
        exact hn.symm.trans hmod
    exact ⟨α, hα, by rw [hw_eq, hr₀eq]⟩

end CFSG.StandardType

end
