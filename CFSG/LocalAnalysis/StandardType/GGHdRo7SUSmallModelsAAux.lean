module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_isRefl_iff_linRefl {p : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] (r : W ≃ₗ[ZMod p] W) :
    ZS.IsRefl p r ↔ GGLinRefl r := Iff.rfl

theorem hdRo7SmAAux_isRefl_of_smRefl {m : ℕ} {r : SMGL m} {u : SMV m}
    {φ : Module.Dual (ZMod 3) (SMV m)} (h : SMRefl r u φ) : GGLinRefl r := by
  obtain ⟨hφu, hr⟩ := h
  have hu_ne : u ≠ 0 := by
    intro h0
    have h1 : φ u = 0 := by rw [h0, map_zero]
    rw [hφu] at h1
    exact (by decide : (2 : ZMod 3) ≠ 0) h1
  have hφr : ∀ v, φ (r v) = - φ v := by
    intro v
    rw [hr, map_sub, map_smul, hφu, smul_eq_mul]
    ring
  have hsq : r * r = 1 := by
    apply LinearEquiv.ext
    intro v
    change r (r v) = v
    calc r (r v) = r v - φ (r v) • u := hr (r v)
      _ = (v - φ v • u) - φ (r v) • u := by rw [hr v]
      _ = (v - φ v • u) - (-φ v) • u := by rw [hφr v]
      _ = v := by module
  refine ⟨hsq, ?_⟩
  have hsub : ∀ v, (r.toLinearMap - LinearMap.id : SMV m →ₗ[ZMod 3] SMV m) v
      = -(φ v) • u := by
    intro v
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    change r v - v = -(φ v) • u
    rw [hr]
    module
  have hrange : ggLinMove r = Submodule.span (ZMod 3) {u} := by
    rw [ggLinMove]
    apply le_antisymm
    · rintro w ⟨v, hv⟩
      rw [← hv, hsub v]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨u, ?_⟩
      rw [hsub u, hφu, show -(2 : ZMod 3) = 1 by decide, one_smul]
  rw [hrange]
  exact finrank_span_singleton hu_ne

theorem hdRo7SmAAux_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M.reindex (Equiv.refl ι) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

theorem hdRo7SmAAux_groupEquiv_of_eq {B : Type} {M M' : CoxeterMatrix B} (h : M = M') :
    ∃ φ : M.Group ≃* M'.Group, ∀ i, φ (M.simple i) = M'.simple i := by
  subst h
  exact ⟨MulEquiv.refl _, fun _ => rfl⟩

theorem hdRo7SmAAux_linWeyl_of_perm {W : Type} [AddCommGroup W] [Module (ZMod 3) W]
    (R : Subgroup (W ≃ₗ[ZMod 3] W)) (n : ℕ) (hn : 1 ≤ n)
    (e : Equiv.Perm (Fin (n + 1)) ≃* R)
    (hrefl : ∀ k : Fin n, GGLinRefl ((e (Equiv.swap k.castSucc k.succ) : R) : W ≃ₗ[ZMod 3] W)) :
    ZS.LinWeyl 3 R := by
  obtain ⟨φ, hφ⟩ := hdRo7SmAAux_groupEquiv_of_eq (coxeterMatrix_isFiniteType_A_eq n).symm
  let ee : (CoxeterMatrix.A n).Group ≃* Equiv.Perm (Fin (n + 1)) :=
    φ.trans (typeAWeylEquiv n).symm
  have hee : ∀ k : Fin n,
      ee ((CoxeterMatrix.A n).simple k) = Equiv.swap k.castSucc k.succ := by
    intro k
    change (typeAWeylEquiv n).symm (φ ((CoxeterMatrix.A n).simple k)) =
      Equiv.swap k.castSucc k.succ
    rw [hφ k, ← typeAWeylEquiv_swap n k, MulEquiv.symm_apply_apply]
  refine ⟨Fin n, CoxeterMatrix.A n, ?_, ?_⟩
  · refine Or.inl ⟨n, Equiv.refl _, hn, Or.inl ?_⟩
    exact (hdRo7SmAAux_reindex_refl _).symm
  · refine ⟨ee.trans e, ?_⟩
    intro k
    have hf : (ee.trans e) ((CoxeterMatrix.A n).simple k) =
        e (Equiv.swap k.castSucc k.succ) := by
      change e (ee ((CoxeterMatrix.A n).simple k)) = e (Equiv.swap k.castSucc k.succ)
      rw [hee k]
    change ZS.IsRefl 3
      (((ee.trans e) ((CoxeterMatrix.A n).simple k) : R) : W ≃ₗ[ZMod 3] W)
    rw [hf]
    exact (hdRo7SmAAux_isRefl_iff_linRefl _).mpr (hrefl k)

end CFSG.StandardType.HdRo7SU.Small
