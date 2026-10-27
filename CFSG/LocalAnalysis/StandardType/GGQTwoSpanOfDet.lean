module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeWeyl

public section

namespace CFSG.StandardType

open Module

private theorem ggQ2sp_parab_fixes {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {u : D.V}
    (hu : ∀ i : {k // k ≠ D.b}, D.root (i : D.ι) u = 0) :
    ∀ g ∈ D.parab {k | k ≠ D.b}, g u = u := by
  intro g hg
  refine Subgroup.closure_induction (p := fun x _ => x u = u) ?_ ?_ ?_ ?_ hg
  · rintro t ⟨k, hk, rfl⟩
    have hk' : D.root k u = 0 := hu ⟨k, hk⟩
    have happ : D.simpleRefl k u = u - D.root k u • D.coroot k := by
      rw [show D.simpleRefl k = Module.reflection (D.root_coroot_self k) from rfl]
      exact Module.reflection_apply (h := D.root_coroot_self k) u
    rw [happ, hk', zero_smul, sub_zero]
  · rfl
  · intro a b _ _ ha hb
    rw [LinearEquiv.mul_apply, hb, ha]
  · intro a _ ha
    apply a.injective
    rw [ha]
    exact a.apply_symm_apply u

theorem ggQ2_span_of_det {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (hdet : ((M.cartan.submatrix (fun i : {k // k ≠ M.b} => (i : M.ι))
      (fun i : {k // k ≠ M.b} => (i : M.ι))).det : ZMod p) ≠ 0) :
    Submodule.span (ZMod p) (insert M.yV (Set.range fun i : {k // k ≠ M.b} => M.coroot i)) = ⊤ := by
  classical
  let Λ := {k // k ≠ M.b}
  let C : Matrix Λ Λ (ZMod p) := fun i j => (M.cartan (i : M.ι) (j : M.ι) : ZMod p)
  have hC_apply : ∀ i j : Λ, C i j = (M.cartan (i : M.ι) (j : M.ι) : ZMod p) :=
    fun i j => rfl
  have hCeq : C = (Int.castRingHom (ZMod p)).mapMatrix
      (M.cartan.submatrix (fun i : Λ => (i : M.ι)) (fun i : Λ => (i : M.ι))) := by
    rw [RingHom.mapMatrix_apply]
    ext i j
    rfl
  have hCdet : IsUnit C.det := by
    rw [isUnit_iff_ne_zero]
    have hM : C.det = ((M.cartan.submatrix (fun i : Λ => (i : M.ι))
        (fun i : Λ => (i : M.ι))).det : ZMod p) := by
      rw [hCeq, ← RingHom.map_det]
      rfl
    rw [hM]
    exact hdet
  have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hCdet
  rw [eq_top_iff]
  intro v _
  let c : Λ → ZMod p := C⁻¹.mulVec (fun i : Λ => M.root (i : M.ι) v)
  have hCc : C.mulVec c = fun i : Λ => M.root (i : M.ι) v := by
    show C.mulVec (C⁻¹.mulVec (fun i : Λ => M.root (i : M.ι) v)) = _
    rw [Matrix.mulVec_mulVec, hCinv, Matrix.one_mulVec]
  let u : M.V := v - ∑ j : Λ, c j • M.coroot (j : M.ι)
  have hu : ∀ i : Λ, M.root (i : M.ι) u = 0 := by
    intro i
    have h1 : M.root (i : M.ι) u = M.root (i : M.ι) v - (C.mulVec c) i := by
      have hu_eq : u = v - ∑ j : Λ, c j • M.coroot (j : M.ι) := rfl
      rw [hu_eq, map_sub, map_sum, Matrix.mulVec_apply_eq_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, M.pairing, hC_apply, smul_eq_mul, mul_comm]
    rw [h1, hCc]
    exact sub_self _
  have hfix : ∀ g ∈ M.parabL {k | k ≠ M.b}, g u = u := ggQ2sp_parab_fixes M.toLin hu
  have hu_mem : u ∈ Submodule.span (ZMod p) {M.yV} := ((ggQ2_fixed_lin M).2 u).mp hfix
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hu_mem
  have hv_eq : v = s • M.yV + ∑ j : Λ, c j • M.coroot (j : M.ι) := by
    have h2 : v = u + ∑ j : Λ, c j • M.coroot (j : M.ι) := by
      have hu_eq : u = v - ∑ j : Λ, c j • M.coroot (j : M.ι) := rfl
      rw [hu_eq, sub_add_cancel]
    rw [← hs] at h2
    exact h2
  rw [hv_eq]
  refine Submodule.add_mem _ ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert M.yV _))
  · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_insert_of_mem M.yV ⟨j, rfl⟩)

end CFSG.StandardType

end
