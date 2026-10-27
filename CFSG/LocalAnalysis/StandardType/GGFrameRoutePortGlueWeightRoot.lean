module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Refl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
import all CFSG.LocalAnalysis.StandardType.GGFrameE78Refl
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ClassicalInvolution

namespace E7WeightRoot

open CFSG.OddStandard.SmallF3.Omega.E7RootSet

@[expose] def index (i : Fin 7) : Fin Tag.E7.rank := Fin.cast (by rfl) i

@[expose] def cartan : FEMat 7 := (CartanMatrix.E 7).map (Int.castRingHom (ZMod 3))

theorem det_cartan : cartan.det = 2 := by
  have h := (Int.castRingHom (ZMod 3)).map_det (CartanMatrix.E 7)
  rw [CartanMatrix.E₇_det] at h
  simpa [cartan, RingHom.mapMatrix_apply] using h.symm

theorem isUnit_det_cartan : IsUnit cartan.det := by
  rw [det_cartan]
  exact isUnit_iff_ne_zero.mpr (by decide)

@[expose] noncomputable def rootToWeight : FEVec 7 ≃ₗ[ZMod 3] FEVec 7 :=
  LinearEquiv.ofLinear (Matrix.toLin' cartan) (Matrix.toLin' cartan⁻¹)
    (by rw [← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ isUnit_det_cartan,
      Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ isUnit_det_cartan,
      Matrix.toLin'_one])

theorem rootToWeight_apply (v : FEVec 7) : rootToWeight v = cartan.mulVec v := by
  change Matrix.toLin' cartan v = _
  rw [Matrix.toLin'_apply]

theorem rootToWeight_single (i : Fin 7) :
    rootToWeight (Pi.single i 1) = feCol 7 i := by
  ext j
  simp [rootToWeight_apply, cartan, Matrix.mulVec, dotProduct, feCol, Pi.single_apply]

theorem polarV_single (i : Fin 7) (v : FEVec 7) :
    Certificates.OmegaSevenMax.polarV (Pi.single i 1) v = (rootToWeight v) i := by
  fin_cases i <;>
    simp [Certificates.OmegaSevenMax.polarV, rootToWeight_apply, cartan,
      CartanMatrix.E, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      show (2 : ZMod 3) = -1 from by decide] <;> ring

theorem rhoEquiv_apply_eq_coe
    (w : WeylGroup Tag.E7) (v : FEVec 7) :
    rhoEquiv w v = (rho w).val v := by
  obtain ⟨u, rfl⟩ := redV_surj v
  rw [rhoEquiv_redV, rho_apply_redV]

@[expose] noncomputable def rhoLinear :
    WeylGroup Tag.E7 →*
    (FEVec 7 ≃ₗ[ZMod 3] FEVec 7) where
  toFun := rhoEquiv
  map_one' := by
    ext v
    rw [rhoEquiv_apply_eq_coe, map_one]
    rfl
  map_mul' := by
    intro w w'
    ext v
    simp only [LinearEquiv.mul_apply, rhoEquiv_apply_eq_coe, map_mul]
    rfl

theorem rhoLinear_injective :
    Function.Injective rhoLinear := by
  intro w w' h
  apply rho_injective
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv := congrArg (fun f : FEVec 7 ≃ₗ[ZMod 3] FEVec 7 => f v) h
  change rhoEquiv w v = rhoEquiv w' v at hv
  exact (rhoEquiv_apply_eq_coe w v).symm.trans
    (hv.trans (rhoEquiv_apply_eq_coe w' v))

theorem redV_single (i : Fin 7) :
    redV (Pi.single (index i) 1 : Fin Tag.E7.rank → ℤ) =
      (Pi.single i 1 : FEVec 7) := by
  ext j
  change ((Pi.single i (1 : ℤ) : Fin 7 → ℤ) j : ZMod 3) =
    (Pi.single i (1 : ZMod 3) : FEVec 7) j
  simp [Pi.single_apply]

theorem rootToWeight_simple
    (i : Fin 7) (v : FEVec 7) :
    rootToWeight (rhoEquiv (simple Tag.E7 (index i)) v) =
      (feS 7 i).mulVec (rootToWeight v) := by
  rw [rhoEquiv_apply_eq_coe, rho_simple, reflEl_apply]
  change rootToWeight
    (v - Certificates.OmegaSevenMax.polarV
      (redV (Pi.single (index i) 1 : Fin Tag.E7.rank → ℤ)) v •
        redV (Pi.single (index i) 1 : Fin Tag.E7.rank → ℤ)) = _
  rw [redV_single, map_sub, map_smul, rootToWeight_single, polarV_single, feS_mulVec]

theorem exists_weyl_of_mem_closure
    {t : FEMat 7}
    (ht : t ∈ Submonoid.closure (Set.range (feS 7))) :
    ∃ w : WeylGroup Tag.E7, ∀ v : FEVec 7,
      t.mulVec (rootToWeight v) = rootToWeight (rhoLinear w v) := by
  obtain ⟨l, hl, hprod⟩ := Submonoid.exists_list_of_mem_closure ht
  subst t
  clear ht
  revert hl
  induction l with
  | nil =>
      intro _
      refine ⟨1, ?_⟩
      intro v
      simp
  | cons s l ih =>
      intro hl
      obtain ⟨i, rfl⟩ := hl s (List.mem_cons_self ..)
      obtain ⟨w, hw⟩ := ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))
      refine ⟨simple Tag.E7 (index i) * w, ?_⟩
      intro v
      rw [List.prod_cons, ← Matrix.mulVec_mulVec, hw, map_mul,
        LinearEquiv.mul_apply]
      exact (rootToWeight_simple i (rhoLinear w v)).symm

theorem rhoLinear_mem_rootSet
    (w : WeylGroup Tag.E7) {v : FEVec 7} (hv : v ∈ rootSet) :
    rhoLinear w v ∈ rootSet := by
  change rhoEquiv w v ∈ rootSet
  have h : rhoEquiv w v ∈ rootSet.image (rhoEquiv w) :=
    Finset.mem_image.mpr ⟨v, hv, rfl⟩
  rwa [rho_image_rootSet] at h

theorem negative_eigen_mem_rootSet
    {t : FEMat 7} {v : FEVec 7}
    (ht : t ∈ feT 7) (hv : v ≠ 0) (htv : t.mulVec v = -v) :
    rootToWeight.symm v ∈ rootSet := by
  change FEConjDer 7 t at ht
  induction ht generalizing v with
  | base i =>
      let c : ZMod 3 := 2 * v i
      have hline : v = c • feCol 7 i := feS_neg_line 7 i v htv
      have hc : c ≠ 0 := by
        intro h
        apply hv
        simpa [h] using hline
      have hvec : rootToWeight.symm v = c • (Pi.single i 1 : FEVec 7) := by
        apply rootToWeight.injective
        rw [rootToWeight.apply_symm_apply, map_smul, rootToWeight_single]
        exact hline
      have hroot : (Pi.single i 1 : FEVec 7) ∈ rootSet :=
        mem_rootSet_iff.mpr ⟨Pi.single (index i) 1, IsRoot.basis (index i), redV_single i⟩
      have hneg : -(Pi.single i 1 : FEVec 7) ∈ rootSet := by
        refine mem_rootSet_iff.mpr
          ⟨-Pi.single (index i) 1, IsRoot.neg (IsRoot.basis (index i)), ?_⟩
        rw [show -(Pi.single (index i) 1 : Fin Tag.E7.rank → ℤ) =
          (-1 : ℤ) • Pi.single (index i) 1 by simp, redV_zsmul, redV_single]
        simp
      have hsign : ∀ a : ZMod 3, a ≠ 0 → a = 1 ∨ a = -1 := by decide +kernel
      rcases hsign c hc with hc1 | hc1
      · simpa [hvec, hc1] using hroot
      · simpa [hvec, hc1] using hneg
  | conj i ht ih =>
      rename_i r
      let s := feS 7 i
      have hs : s * s = 1 := feS_mul_self 7 i
      have hinvol (u : FEVec 7) : s.mulVec (s.mulVec u) = u := by
        rw [Matrix.mulVec_mulVec, hs, Matrix.one_mulVec]
      have hy : s.mulVec v ≠ 0 := by
        intro h
        apply hv
        have h' := congrArg s.mulVec h
        rwa [hinvol, Matrix.mulVec_zero] at h'
      have hrv : r.mulVec (s.mulVec v) = -(s.mulVec v) := by
        have h' := congrArg s.mulVec htv
        have hm : s * (s * r * s) = r * s := by
          simp only [← mul_assoc, hs, one_mul]
        change s.mulVec ((s * r * s).mulVec v) = s.mulVec (-v) at h'
        rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, Matrix.mulVec_neg] at h'
        exact h'
      have hroot := ih hy hrv
      have heq : rootToWeight.symm v =
          rhoLinear (simple Tag.E7 (index i)) (rootToWeight.symm (s.mulVec v)) := by
        apply rootToWeight.injective
        rw [rootToWeight.apply_symm_apply]
        change v = rootToWeight
          (rhoEquiv (simple Tag.E7 (index i)) (rootToWeight.symm (s.mulVec v)))
        rw [rootToWeight_simple, rootToWeight.apply_symm_apply]
        exact (hinvol v).symm
      rw [heq]
      exact rhoLinear_mem_rootSet _ hroot

end E7WeightRoot

end CFSG.StandardType.FrameRoute

end
