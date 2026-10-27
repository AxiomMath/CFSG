module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem innAutOf_normal (L₀ : Type) [Group L₀] : (innAutOf L₀).Normal where
  conj_mem := by
    rintro _ ⟨x, rfl⟩ φ
    refine ⟨φ x, MulEquiv.ext fun y => ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

theorem eq_one_of_forall_commute_conj {L₀ : Type} [Group L₀] (hZ : center L₀ = ⊥)
    {φ : MulAut L₀} (h : ∀ s : L₀, φ * MulAut.conj s = MulAut.conj s * φ) : φ = 1 := by
  refine MulEquiv.ext fun s => ?_
  have hc : ∀ y : L₀, φ s * y * (φ s)⁻¹ = s * y * s⁻¹ := by
    intro y
    have h1 := congrArg (fun f : MulAut L₀ => f (φ.symm y)) (h s)
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv] at h1
    exact h1
  have hcen : s⁻¹ * φ s ∈ center L₀ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := hc y
    calc y * (s⁻¹ * φ s) = s⁻¹ * (s * y * s⁻¹) * φ s := by group
      _ = s⁻¹ * (φ s * y * (φ s)⁻¹) * φ s := by rw [this]
      _ = s⁻¹ * φ s * y := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  rw [MulAut.one_apply]
  calc φ s = s * (s⁻¹ * φ s) := by group
    _ = s := by rw [hcen, mul_one]

theorem centralizer_innAutOf_subgroupOf_eq_bot {L₀ : Type} [Group L₀] (hZ : center L₀ = ⊥)
    {A : Subgroup (MulAut L₀)} (hA : innAutOf L₀ ≤ A) :
    centralizer (((innAutOf L₀).subgroupOf A : Subgroup ↥A) : Set ↥A) = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine eq_one_of_forall_commute_conj hZ fun s => ?_
  have hs : MulAut.conj s ∈ A := hA ⟨s, rfl⟩
  have h1 := ha ⟨MulAut.conj s, hs⟩ (Subgroup.mem_subgroupOf.mpr ⟨s, rfl⟩)
  exact (congrArg Subtype.val h1).symm

theorem solvableRadical_eq_bot_of_simple_normal {Q : Type} [Group Q] [Finite Q]
    {L : Subgroup Q} [L.Normal] (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : centralizer (L : Set Q) = ⊥) : CFSG.solvableRadical Q = ⊥ := by
  haveI := hLs
  have hL : CFSG.IsComponent L :=
    ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1,
      Subgroup.Normal.isSubnormal inferInstance⟩
  have hRs : Group.IsSolvable ↥(CFSG.solvableRadical Q) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  have h := (CFSG.LocalCores.component_solvable_centralizer hRs
    (Subgroup.Normal.isSubnormal inferInstance)).1 L hL
  rw [eq_bot_iff, ← hC]
  rw [Subgroup.commutator_comm] at h
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp h

theorem perfectCore_top_le_of_isSolvable_quot {Q : Type} [Group Q] [Finite Q] (N : Subgroup Q)
    [N.Normal] (hq : Group.IsSolvable (Q ⧸ N)) : perfectCore (⊤ : Subgroup Q) ≤ N := by
  haveI := hq
  have h1 : perfectCore (⊤ : Subgroup (Q ⧸ N)) = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
  have h2 := map_perfectCore (QuotientGroup.mk' N) (⊤ : Subgroup Q)
  rw [Subgroup.map_top, MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective N),
    h1] at h2
  exact (QuotientGroup.ker_mk' N) ▸ (Subgroup.map_eq_bot_iff _).mp h2

end CFSG.LocalAnalysis.WeakClosure81

end
