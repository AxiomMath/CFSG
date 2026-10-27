module

public import CFSG.Monster.Griess.DyadicCoords
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster Matrix Module

@[expose] noncomputable def parityMap : SpaceB →ₗ[ℚ] SpaceB :=
  LinearMap.prodMap LinearMap.id (LinearMap.prodMap LinearMap.id (-LinearMap.id))

theorem parityMap_apply (u : SpaceB) : parityMap u = (u.1, u.2.1, -u.2.2) := rfl

@[expose] noncomputable def xB : SpaceB ≃ₗ[ℚ] SpaceB :=
  LinearEquiv.ofInvolutive parityMap fun u => by simp [parityMap_apply]

theorem xB_apply (u : SpaceB) : xB u = (u.1, u.2.1, -u.2.2) := rfl

theorem xB_xB (u : SpaceB) : xB (xB u) = u := by simp [xB_apply]

theorem xB_mul_self : xB * xB = 1 := LinearEquiv.ext xB_xB

theorem xB_ne_one : xB ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : SpaceB ≃ₗ[ℚ] SpaceB =>
    (f ((0, 0, Matrix.of fun _ _ => (1 : ℚ)) : SpaceB)).2.2 (0, 0) 0) h
  simp only [xB_apply, LinearEquiv.coe_one, id_eq, Matrix.neg_apply, Matrix.of_apply] at h1
  norm_num at h1

theorem bform_xB (u v : SpaceB) : bform (xB u) (xB v) = bform u v := by
  simp only [bform_apply, xB_apply, Matrix.neg_apply, neg_mul_neg]

theorem isDyadicVec_xB {u : SpaceB} (hu : IsDyadicVec u) : IsDyadicVec (xB u) :=
  ⟨hu.1, hu.2.1, fun j i => by
    change -(u.2.2 j i) ∈ dyadic
    exact neg_mem (hu.2.2 j i)⟩

theorem xB_mem_BR_iff {u : SpaceB} : xB u ∈ BR ↔ u ∈ BR := by
  refine ⟨fun h => ?_, fun h => mem_BR_iff.2 (isDyadicVec_xB (mem_BR_iff.1 h))⟩
  rw [← xB_xB u]
  exact mem_BR_iff.2 (isDyadicVec_xB (mem_BR_iff.1 h))

theorem map_xB_BR : BR.map ((xB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨xB u, xB_mem_BR_iff.2 h, xB_xB u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact xB_mem_BR_iff.2 hv

theorem mem_eigenspace_xB_one {u : SpaceB} :
    u ∈ End.eigenspace (xB : End ℚ SpaceB) 1 ↔ u.2.2 = 0 := by
  rw [End.mem_eigenspace_iff, one_smul]
  change xB u = u ↔ _
  rw [xB_apply]
  constructor
  · intro h
    have h' := congrArg (fun v : SpaceB => v.2.2) h
    simp only at h'
    have : (2 : ℚ) • u.2.2 = 0 := by rw [two_smul]; nth_rw 1 [← h']; exact neg_add_cancel _
    exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · intro h
    ext <;> simp [h]

theorem mem_eigenspace_xB_neg_one {u : SpaceB} :
    u ∈ End.eigenspace (xB : End ℚ SpaceB) (-1) ↔ u.1 = 0 ∧ u.2.1 = 0 := by
  rw [End.mem_eigenspace_iff, neg_one_smul]
  change xB u = -u ↔ _
  rw [xB_apply]
  constructor
  · intro h
    have h1 := congrArg (fun v : SpaceB => v.1) h
    have h2 := congrArg (fun v : SpaceB => v.2.1) h
    simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
    refine ⟨?_, ?_⟩
    · have : (2 : ℚ) • u.1 = 0 := by rw [two_smul]; nth_rw 1 [h1]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    · have : (2 : ℚ) • u.2.1 = 0 := by rw [two_smul]; nth_rw 1 [h2]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  · rintro ⟨h1, h2⟩
    ext <;> simp [h1, h2]

@[expose] noncomputable def projW : SpaceB →ₗ[ℚ] SpaceW :=
  LinearMap.snd ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW)

@[expose] noncomputable def projAX : SpaceB →ₗ[ℚ] symMat × SpaceX :=
  LinearMap.prod (LinearMap.fst ℚ symMat (SpaceX × SpaceW))
    (LinearMap.fst ℚ SpaceX SpaceW ∘ₗ LinearMap.snd ℚ symMat (SpaceX × SpaceW))

theorem eigenspace_xB_one : End.eigenspace (xB : End ℚ SpaceB) 1 = LinearMap.ker projW := by
  ext u
  rw [mem_eigenspace_xB_one, LinearMap.mem_ker]
  rfl

theorem eigenspace_xB_neg_one :
    End.eigenspace (xB : End ℚ SpaceB) (-1) = LinearMap.ker projAX := by
  ext u
  rw [mem_eigenspace_xB_neg_one, LinearMap.mem_ker, Prod.ext_iff]
  rfl

theorem finrank_eigenspace_xB_one : finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) 1) = 98580 := by
  rw [eigenspace_xB_one]
  have hsurj : LinearMap.range projW = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro N
    exact ⟨(0, 0, N), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker projW
  rw [hsurj, finrank_top, finrank_W, finrank_B] at h
  omega

theorem finrank_eigenspace_xB_neg_one :
    finrank ℚ (End.eigenspace (xB : End ℚ SpaceB) (-1)) = 98304 := by
  rw [eigenspace_xB_neg_one]
  have hsurj : LinearMap.range projAX = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨A, x⟩
    exact ⟨(A, x, 0), rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker projAX
  rw [hsurj, finrank_top, finrank_prod, finrank_A, finrank_X, finrank_B] at h
  omega

end CFSG.Monster.Griess
