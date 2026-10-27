module

public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure
public import CFSG.Adapters.TauCetiExceptional.BigCellCore
public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generation

public noncomputable section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open TauCeti TauCeti.TypeDSpinCarrier TauCeti.UniversalEnvelopingAlgebra WithConv
open CFSG.TauCetiBridge CFSG.TauCetiBridge.BigCell

variable (n : ℕ) (hn : 4 ≤ n)

@[expose] def ratRootGroup : Subgroup (Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) :=
  Subgroup.closure {g | ∃ (k : Fin n ⊕ Fin n) (t : ℚ), g =
    (rootSubgroupPoints n hn k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ)}

theorem rootPoint_mem_ratRootGroup (k : Fin n ⊕ Fin n) (t : ℚ) :
    (rootSubgroupPoints n hn k ℚ (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) ∈ ratRootGroup n hn :=
  Subgroup.subset_closure ⟨k, t, rfl⟩

@[expose] def ratRootPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n) →ₐ[ℤ] ℚ)) :=
  (ratRootGroup n hn).map
    (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (dimension n)).symm.toMonoidHom

@[expose] def ratVanishingIdeal :
    HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) (ratRootPoints n hn)

theorem ratVanishingIdeal_le_definingIdeal : ratVanishingIdeal n hn ≤ definingIdeal n hn := by
  rw [definingIdeal_eq_kostantGeneratedDefiningIdeal, le_kostantGeneratedDefiningIdeal_iff]
  intro k x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) (dimension n)).symm
      (rootSubgroupPoints n hn k ℚ (Multiplicative.ofAdd c) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) ℚ) ∈ ratRootPoints n hn :=
    ⟨_, rootPoint_mem_ratRootGroup n hn k c, rfl⟩
  have hv := (mem_fracVanishingIdeal _ x).mp hx ⟨_, hmem⟩
  simp only [coe_rootSubgroupPoints] at hv
  have hpt := pointsMulEquiv_kostantRootSubgroupCoordinateMap
    (TauCeti.serreRootGenerator (CartanMatrix.D n)) (TauCeti.serreH ℚ (CartanMatrix.D n))
    (rep n hn) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn) k
    (isNilpotent_rep_rootGenerator n hn k) (latticeBasis n) ℚ
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

omit hn in
theorem evalMat_eq_aeval {A : Type*} [CommRing A]
    (M : Matrix (Fin (dimension n)) (Fin (dimension n)) A)
    (P : MvPolynomial (Fin (dimension n) × Fin (dimension n)) ℤ) :
    evalMat M P = MvPolynomial.aeval (fun ij : Fin (dimension n) × Fin (dimension n) =>
      M ij.1 ij.2) P := by
  rw [evalMat, MvPolynomial.aeval_def, algebraMap_int_eq]
  rfl

theorem evalMat_eq_zero_of_mem_points (P : MvPolynomial (Fin (dimension n) × Fin (dimension n)) ℤ)
    (hP : ∀ s ∈ ratRootGroup n hn,
      evalMat (s : Matrix (Fin (dimension n)) (Fin (dimension n)) ℚ) P = 0)
    {A : Type} [CommRing A] {g : Matrix.GeneralLinearGroup (Fin (dimension n)) A}
    (hg : g ∈ points n hn A) :
    evalMat (g : Matrix (Fin (dimension n)) (Fin (dimension n)) A) P = 0 := by
  have hy : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ (dimension n)
      (GeneralLinear.coordinateRingMap ℤ (dimension n) P) ∈ ratVanishingIdeal n hn := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm s).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, ← evalMat_eq_aeval]
    exact hP s hs
  have h0 := (mem_points_iff n hn A g).1 hg _ (ratVanishingIdeal_le_definingIdeal n hn hy)
  rw [GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap] at h0
  rw [evalMat_eq_aeval]
  exact h0

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
