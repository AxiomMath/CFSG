module

public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Generation

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinB

open TauCeti TauCeti.TypeBSpinCarrier TauCeti.UniversalEnvelopingAlgebra WithConv
open CFSG.TauCetiBridge CFSG.TauCetiBridge.BigCell

variable (n : ℕ)

@[expose] def ratRootGroup : Subgroup (Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) :=
  Subgroup.closure {g | ∃ (k : Fin (n + 1) ⊕ Fin (n + 1)) (t : ℚ), g =
    (rootSubgroupPoints n k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ)}

theorem rootPoint_mem_ratRootGroup (k : Fin (n + 1) ⊕ Fin (n + 1)) (t : ℚ) :
    (rootSubgroupPoints n k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) ∈ ratRootGroup n :=
  Subgroup.subset_closure ⟨k, t, rfl⟩

@[expose] def ratRootPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) →ₐ[ℤ] ℚ)) :=
  (ratRootGroup n).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (dimension n)).symm.toMonoidHom

@[expose] def ratVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) (ratRootPoints n)

theorem ratVanishingIdeal_le_definingIdeal : ratVanishingIdeal n ≤ definingIdeal n := by
  rw [definingIdeal_eq_kostantGeneratedDefiningIdeal, le_kostantGeneratedDefiningIdeal_iff]
  intro k x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (dimension n)).symm
      (rootSubgroupPoints n k ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) ∈ ratRootPoints n :=
    ⟨_, rootPoint_mem_ratRootGroup n k c, rfl⟩
  have hv := (mem_fracVanishingIdeal _ x).mp hx ⟨_, hmem⟩
  simp only [coe_rootSubgroupPoints] at hv
  have hpt := pointsMulEquiv_kostantRootSubgroupCoordinateMap
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)) (TauCeti.typeBSimpleCorootGenerator (K := ℚ))
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) k
    (isNilpotent_rep_rootGenerator n k) (latticeBasis n) ℚ
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

theorem evalMat_eq_aeval {A : Type*} [CommRing A]
    (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A)
    (P : MvPolynomial (Fin (dimension n) × Fin (dimension n)) ℤ) :
    evalMat M P = MvPolynomial.aeval (fun ij : Fin (dimension n) × Fin (dimension n) =>
      M ij.1 ij.2) P := by
  rw [evalMat, MvPolynomial.aeval_def, algebraMap_int_eq]
  rfl

theorem evalMat_eq_zero_of_mem_points (P : MvPolynomial (Fin (dimension n) × Fin (dimension n)) ℤ)
    (hP : ∀ s ∈ ratRootGroup n,
      evalMat (s : Matrix (Fin (dimension n)) (Fin (dimension n)) ℚ) P = 0)
    {A : Type} [CommRing A] {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A}
    (hg : g ∈ points n A) :
    evalMat (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A) P = 0 := by
  have hy : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (dimension n)
      (GeneralLinear.coordinateRingMap ℤ (dimension n) P) ∈ ratVanishingIdeal n := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm s).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, ← evalMat_eq_aeval]
    exact hP s hs
  have h0 := (mem_points_iff n A g).1 hg _ (ratVanishingIdeal_le_definingIdeal n hy)
  rw [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap] at h0
  rw [evalMat_eq_aeval]
  exact h0

end CFSG.RankThree.PartTwo.Census.Carrier.SpinB
