module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Adjoint
public import CFSG.Adapters.TauCetiExceptional.FrameworkClosure
public import CFSG.Adapters.TauCetiExceptional.BigCellPoints
public import CFSG.Blueprint.ChevalleyWeyl
public import TauCeti.Algebra.Lie.F4.ShortRoot.Generation
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate70
public import Certificates.Certificate71

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge.BigCell TauCeti
  TauCeti.F4ShortRoot TauCeti.UniversalEnvelopingAlgebra TauCeti.DynkinType WithConv MvPolynomial
open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

local notation "CM" => CartanMatrix.F₄ᵀ
local notation "rootGen" => TauCeti.serreRootGenerator CM
local notation "cartanGen" => TauCeti.serreH ℚ CM

abbrev PolyRing : Type :=
  MvPolynomial (Fin 26 × Fin 26) ℤ

abbrev genMat : Matrix (Fin 26) (Fin 26) PolyRing :=
  coordMatrix 26

variable {A : Type*} [CommRing A]

theorem mapMatrix_bMatR {B : Type*} [CommRing B] (f : A →+* B) (p : ℕ) :
    f.mapMatrix (bMatR A p) = bMatR B p := by
  ext r c
  simp [bMatR]

theorem mapMatrix_conj_adjugate (M : Matrix (Fin 26) (Fin 26) A)
    (Y : Matrix (Fin 26) (Fin 26) ℤ) :
    (evalMat M).mapMatrix (genMat * Y.map (Int.cast : ℤ → PolyRing) * genMat.adjugate) =
      M * Y.map (Int.cast : ℤ → A) * M.adjugate := by
  rw [map_mul, map_mul, RingHom.map_adjugate, mapMatrix_evalMat_coordMatrix]
  congr 2
  ext r c
  simp

@[expose] def detPoly : PolyRing :=
  genMat.det - 1

theorem evalMat_detPoly (M : Matrix (Fin 26) (Fin 26) A) : evalMat M detPoly = M.det - 1 := by
  rw [detPoly, map_sub, map_one, RingHom.map_det, mapMatrix_evalMat_coordMatrix]

@[expose] def normPoly (t : Fin 52) (r c : Fin 26) : PolyRing :=
  (genMat * bMatR PolyRing t * genMat.adjugate -
    ∑ u : Fin 52, coord u (genMat * bMatR PolyRing t * genMat.adjugate) • bMatR PolyRing u) r c

theorem evalMat_normPoly (M : Matrix (Fin 26) (Fin 26) A) (t : Fin 52) (r c : Fin 26) :
    evalMat M (normPoly t r c) = (M * bMatR A t * M.adjugate -
      ∑ u : Fin 52, coord u (M * bMatR A t * M.adjugate) • bMatR A u) r c := by
  have key : evalMat M (normPoly t r c) = ((evalMat M).mapMatrix
      (genMat * bMatR PolyRing t * genMat.adjugate -
        ∑ u : Fin 52, coord u (genMat * bMatR PolyRing t * genMat.adjugate) •
          bMatR PolyRing u)) r c := rfl
  have hsum : ∀ u : Fin 52, (evalMat M).mapMatrix
      (coord u (genMat * bMatR PolyRing t * genMat.adjugate) • bMatR PolyRing u) =
        coord u (M * bMatR A t * M.adjugate) • bMatR A u := fun u => by
    rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _),
      ← RingHom.mapMatrix_apply, mapMatrix_bMatR, map_coord, ← RingHom.mapMatrix_apply,
      mapMatrix_conj_adjugate]
  rw [key, map_sub, mapMatrix_conj_adjugate, map_sum]
  simp only [hsum]

theorem adOp_single_apply (g h : Matrix (Fin 26) (Fin 26) A) (b x : Label .F4) :
    adOp g h (Finsupp.single b 1) x =
      coord (labEquiv.symm x) (g * bMatR A (labEquiv.symm b) * h) := by
  rw [adOp, Finsupp.linearCombination_single, one_smul, Finsupp.finsetSum_apply,
    Finset.sum_eq_single (labEquiv.symm x)]
  · rw [Finsupp.smul_apply, posVec_eq_single_lab, Equiv.apply_symm_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  · intro u _ hu
    rw [Finsupp.smul_apply, posVec_eq_single_lab, Finsupp.single_eq_of_ne, smul_zero]
    intro h
    exact hu (by rw [h, Equiv.symm_apply_apply])
  · exact fun h => absurd (Finset.mem_univ _) h

@[expose] def adPoly (P : MvPolynomial (Fin (nLab .F4) × Fin (nLab .F4)) ℤ) : PolyRing :=
  evalMat (natMat .F4 PolyRing (adOp genMat genMat.adjugate)) P

theorem mapMatrix_natMat_adOp (M : Matrix (Fin 26) (Fin 26) A) :
    (evalMat M).mapMatrix (natMat .F4 PolyRing (adOp genMat genMat.adjugate)) =
      natMat .F4 A (adOp M M.adjugate) := by
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, natMat_apply, natMat_apply, adOp_single_apply,
    adOp_single_apply, map_coord, ← RingHom.mapMatrix_apply, bMatR, bMatR,
    mapMatrix_conj_adjugate]

theorem evalMat_adPoly (M : Matrix (Fin 26) (Fin 26) A)
    (P : MvPolynomial (Fin (nLab .F4) × Fin (nLab .F4)) ℤ) :
    evalMat M (adPoly P) = evalMat (natMat .F4 A (adOp M M.adjugate)) P := by
  rw [adPoly, ← RingHom.comp_apply, ← evalMat_mapMatrix, mapMatrix_natMat_adOp]

theorem adjugate_eq_inv_of_det_eq_one (g : Matrix.GeneralLinearGroup (Fin 26) A)
    (h : (g : Matrix (Fin 26) (Fin 26) A).det = 1) :
    (g : Matrix (Fin 26) (Fin 26) A).adjugate =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) := by
  rw [Matrix.coe_units_inv]
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [Matrix.mul_adjugate, h, one_smul]

theorem tcE_triangular : ∀ (i : Fin 4) (a b : Fin 26),
    (b ≤ a → tcE (.inl i) a b = 0 ∧ tcE2 (.inl i) a b = 0) ∧
      (a ≤ b → tcE (.inr i) a b = 0 ∧ tcE2 (.inr i) a b = 0) := by
  intro i a b
  simp only [← smat_spE, ← smat_spE2, smat, Matrix.of_apply]
  revert i a b
  decide +kernel

theorem det_rootPointMat (k : Fin 4 ⊕ Fin 4) (t : A) : (rootPointMat k t).det = 1 := by
  rw [rootPointMat_eq]
  rcases k with i | i
  · rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [((tcE_triangular i a a).1 le_rfl).1, ((tcE_triangular i a a).1 le_rfl).2]
    · intro a b hba
      have hba' : b < a := hba
      simp [Matrix.one_apply_ne (ne_of_lt hba').symm, ((tcE_triangular i a b).1 hba'.le).1,
        ((tcE_triangular i a b).1 hba'.le).2]
  · rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun a _ => ?_
      simp [((tcE_triangular i a a).2 le_rfl).1, ((tcE_triangular i a a).2 le_rfl).2]
    · intro a b hba
      have hab : a < b := hba
      simp [Matrix.one_apply_ne (ne_of_lt hab), ((tcE_triangular i a b).2 hab.le).1,
        ((tcE_triangular i a b).2 hab.le).2]

@[expose] def ratRootGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 26) ℚ) :=
  Subgroup.closure {g | ∃ (k : Fin 4 ⊕ Fin 4) (t : ℚ), g = rootPoint k t}

theorem rootPoint_mem_ratRootGroup (k : Fin 4 ⊕ Fin 4) (t : ℚ) :
    rootPoint k t ∈ ratRootGroup :=
  Subgroup.subset_closure ⟨k, t, rfl⟩

theorem det_eq_one_of_mem_ratRootGroup {s : Matrix.GeneralLinearGroup (Fin 26) ℚ}
    (hs : s ∈ ratRootGroup) : (s : Matrix (Fin 26) (Fin 26) ℚ).det = 1 := by
  have hle : ratRootGroup ≤ (Matrix.GeneralLinearGroup.det :
      Matrix.GeneralLinearGroup (Fin 26) ℚ →* ℚˣ).ker := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    exact det_rootPointMat k t
  have h := MonoidHom.mem_ker.1 (hle hs)
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem ratRootGroup_le_normGroup : ratRootGroup ≤ normGroup ℚ := by
  rw [ratRootGroup, Subgroup.closure_le]
  rintro _ ⟨k, t, rfl⟩
  exact rootPoint_mem_normGroup k t

theorem adUnits_mem_adjointGroup {s : Matrix.GeneralLinearGroup (Fin 26) ℚ}
    (hs : s ∈ ratRootGroup) :
    adUnits ℚ ⟨s, ratRootGroup_le_normGroup hs⟩ ∈ adjointGroup .F4 ℚ := by
  have hle : ratRootGroup ≤ ((adjointGroup .F4 ℚ).comap (adUnits ℚ)).map
      (normGroup ℚ).subtype := by
    rw [ratRootGroup, Subgroup.closure_le]
    rintro _ ⟨k, t, rfl⟩
    refine ⟨⟨rootPoint k t, rootPoint_mem_normGroup k t⟩, ?_, rfl⟩
    change adUnits ℚ ⟨rootPoint k t, rootPoint_mem_normGroup k t⟩ ∈ adjointGroup .F4 ℚ
    rcases k with i | i
    · have e : adUnits ℚ ⟨rootPoint (.inl i) t, rootPoint_mem_normGroup _ t⟩ =
          xUnit .F4 ℚ (nodeF i) t :=
        Units.ext (by rw [coe_adUnits, adConj_rootPoint_inl]; rfl)
      rw [e]
      exact xUnit_mem_adjointGroup _ _
    · have e : adUnits ℚ ⟨rootPoint (.inr i) t, rootPoint_mem_normGroup _ t⟩ =
          yUnit .F4 ℚ (nodeF i) t :=
        Units.ext (by rw [coe_adUnits, adConj_rootPoint_inr]; rfl)
      rw [e]
      exact yUnit_mem_adjointGroup _ _
  obtain ⟨n, hn, hns⟩ := hle hs
  have e : n = ⟨s, ratRootGroup_le_normGroup hs⟩ := Subtype.ext hns
  rw [← e]
  exact hn

theorem evalMat_detPoly_ratRootGroup (s : Matrix.GeneralLinearGroup (Fin 26) ℚ)
    (hs : s ∈ ratRootGroup) : evalMat (s : Matrix (Fin 26) (Fin 26) ℚ) detPoly = 0 := by
  rw [evalMat_detPoly, det_eq_one_of_mem_ratRootGroup hs, sub_self]

theorem evalMat_normPoly_ratRootGroup (t : Fin 52) (r c : Fin 26)
    (s : Matrix.GeneralLinearGroup (Fin 26) ℚ) (hs : s ∈ ratRootGroup) :
    evalMat (s : Matrix (Fin 26) (Fin 26) ℚ) (normPoly t r c) = 0 := by
  rw [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one s (det_eq_one_of_mem_ratRootGroup hs),
    ← ((ratRootGroup_le_normGroup hs t).1).eq_sum, sub_self, Matrix.zero_apply]

theorem evalMat_adPoly_ratRootGroup (P : MvPolynomial (Fin (nLab .F4) × Fin (nLab .F4)) ℤ)
    (hP : VanishesOnRat .F4 P) (s : Matrix.GeneralLinearGroup (Fin 26) ℚ)
    (hs : s ∈ ratRootGroup) : evalMat (s : Matrix (Fin 26) (Fin 26) ℚ) (adPoly P) = 0 := by
  rw [evalMat_adPoly, adjugate_eq_inv_of_det_eq_one s (det_eq_one_of_mem_ratRootGroup hs)]
  have h := hP _ (adUnits_mem_adjointGroup hs)
  rwa [coe_adUnits] at h

@[expose] def ratRootPoints :
    Subgroup (WithConv (GeneralLinear.coordinateHopfAlgebra ℤ 26 →ₐ[ℤ] ℚ)) :=
  ratRootGroup.map (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 26).symm.toMonoidHom

@[expose] def ratVanishingIdeal : HopfIdeal ℤ (GeneralLinear.coordinateHopfAlgebra ℤ 26) :=
  fracVanishingIdeal (R := ℤ) (K := ℚ) ratRootPoints

theorem ratVanishingIdeal_le_definingIdeal :
    ratVanishingIdeal ≤ TauCeti.F4ShortRoot.definingIdeal := by
  rw [TauCeti.F4ShortRoot.definingIdeal_eq_kostantGeneratedDefiningIdeal,
    le_kostantGeneratedDefiningIdeal_iff]
  intro k x hx
  rw [RingHom.mem_ker]
  apply symmetricAlgebra_eq_zero_of_forall_rat
  intro c
  have hmem : (GeneralLinear.pointsMulEquiv (R := ℤ) (A := ℚ) 26).symm
      (rootPoint k c) ∈ ratRootPoints :=
    ⟨_, rootPoint_mem_ratRootGroup k c, rfl⟩
  have hv := (mem_fracVanishingIdeal _ x).mp hx ⟨_, hmem⟩
  simp only [rootPoint] at hv
  rw [TauCeti.F4ShortRoot.coe_rootSubgroupPoints] at hv
  have hpt := pointsMulEquiv_kostantRootSubgroupCoordinateMap rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice k (isNilpotent_rep_serreRootGenerator k)
    latticeBasis ℚ ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ℚ)).symm
      (Multiplicative.ofAdd c))
  rw [← hpt, GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_pointToGeneralLinear] at hv
  exact hv

theorem evalMat_eq_aeval {A : Type*} [CommRing A] (M : Matrix (Fin 26) (Fin 26) A)
    (P : MvPolynomial (Fin 26 × Fin 26) ℤ) :
    evalMat M P = MvPolynomial.aeval (fun ij : Fin 26 × Fin 26 => M ij.1 ij.2) P := by
  rw [evalMat, MvPolynomial.aeval_def, algebraMap_int_eq]
  rfl

theorem evalMat_eq_zero_of_mem_points (P : MvPolynomial (Fin 26 × Fin 26) ℤ)
    (hP : ∀ s ∈ ratRootGroup, evalMat (s : Matrix (Fin 26) (Fin 26) ℚ) P = 0)
    {A : Type} [CommRing A] [Algebra (ZMod 2) A] {g : Matrix.GeneralLinearGroup (Fin 26) A}
    (hg : g ∈ PrimeField.points A) : evalMat (g : Matrix (Fin 26) (Fin 26) A) P = 0 := by
  have hy : GeneralLinear.coordinateHopfAlgebraAlgEquiv ℤ 26
      (GeneralLinear.coordinateRingMap ℤ 26 P) ∈ ratVanishingIdeal := by
    refine (mem_fracVanishingIdeal _ _).mpr ?_
    rintro ⟨_, ⟨s, hs, rfl⟩⟩
    change ((GeneralLinear.pointsMulEquiv (R := ℤ) 26).symm s).ofConv _ = 0
    rw [GeneralLinear.pointsMulEquiv_symm_apply,
      GeneralLinear.generalLinearToPoint_coordinateRingMap, ← evalMat_eq_aeval]
    exact hP s hs
  have hy' := ratVanishingIdeal_le_definingIdeal hy
  rw [TauCeti.F4ShortRoot.definingIdeal_def] at hy'
  have hz := map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem rootGen cartanGen rep
    lattice.toAddSubgroup rep_kostantForm_mem_lattice isNilpotent_rep_serreRootGenerator
    latticeBasis f4ShortRootWeight (ZMod 2) (1 : ZMod 2) hy'
  have hgp := PrimeField.points_le_baseChangePresentationPoints A hg
  rw [GeneralLinear.mem_hopfIdealPointsSubgroup_iff] at hgp
  have h0 := hgp _ hz
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeIso_hom_apply, one_smul,
    GeneralLinear.pointsMulEquiv_symm_apply,
    GeneralLinear.generalLinearToPoint_coordinateRingMap,
    MvPolynomial.aeval_map_algebraMap] at h0
  rw [evalMat_eq_aeval]
  exact h0

section Points

variable {A : Type} [CommRing A] [Algebra (ZMod 2) A]

theorem det_eq_one_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 26) A}
    (hg : g ∈ PrimeField.points A) : (g : Matrix (Fin 26) (Fin 26) A).det = 1 := by
  have h := evalMat_eq_zero_of_mem_points detPoly evalMat_detPoly_ratRootGroup hg
  rwa [evalMat_detPoly, sub_eq_zero] at h

theorem inSpan_conj_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 26) A}
    (hg : g ∈ PrimeField.points A) (t : Fin 52) :
    InSpan ((g : Matrix (Fin 26) (Fin 26) A) * bMatR A t *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)) := by
  have h : ∀ r c, evalMat (g : Matrix (Fin 26) (Fin 26) A) (normPoly t r c) = 0 := fun r c =>
    evalMat_eq_zero_of_mem_points _ (evalMat_normPoly_ratRootGroup t r c) hg
  simp only [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points hg)] at h
  rw [inSpan_iff]
  exact sub_eq_zero.1 (Matrix.ext h)

theorem points_le_normGroup : PrimeField.points A ≤ normGroup A := fun g hg t => by
  refine ⟨inSpan_conj_of_mem_points hg t, ?_⟩
  have h := inSpan_conj_of_mem_points (inv_mem hg) t
  rwa [inv_inv] at h

end Points

theorem evalMat_natMat_adConj_of_mem_points {L : Type} [Field L] [Algebra (ZMod 2) L]
    {g : Matrix.GeneralLinearGroup (Fin 26) L} (hg : g ∈ PrimeField.points L)
    (P : MvPolynomial (Fin (nLab .F4) × Fin (nLab .F4)) ℤ) (hP : VanishesOnRat .F4 P) :
    evalMat (natMat .F4 L (adConj g)) P = 0 := by
  have h := evalMat_eq_zero_of_mem_points (adPoly P) (evalMat_adPoly_ratRootGroup P hP) hg
  rwa [evalMat_adPoly, adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points hg)] at h

@[expose] def adPoints (L : Type) [Field L] [Algebra (ZMod 2) L] :
    PrimeField.points L →* ModGL .F4 L :=
  (adUnits L).comp (Subgroup.inclusion points_le_normGroup)

theorem coe_adPoints {L : Type} [Field L] [Algebra (ZMod 2) L] (g : PrimeField.points L) :
    ((adPoints L g : ModGL .F4 L) : Module.End L (RootModule .F4 L)) =
      adConj (g : Matrix.GeneralLinearGroup (Fin 26) L) :=
  rfl

theorem coe_primeFieldRootPoint {A : Type} [CommRing A] [Algebra (ZMod 2) A]
    (k : Fin 4 ⊕ Fin 4) (t : A) :
    ((PrimeField.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 26) A)) = rootPoint k t :=
  PrimeField.coe_rootSubgroupPoints k A _

theorem adPoints_rootSubgroupPoints_inl {L : Type} [Field L] [Algebra (ZMod 2) L] (i : Fin 4)
    (t : L) : adPoints L (PrimeField.rootSubgroupPoints (.inl i) L (Multiplicative.ofAdd t)) =
      xUnit .F4 L (nodeF i) t :=
  Units.ext (by rw [coe_adPoints, coe_primeFieldRootPoint, adConj_rootPoint_inl]; rfl)

theorem adPoints_rootSubgroupPoints_inr {L : Type} [Field L] [Algebra (ZMod 2) L] (i : Fin 4)
    (t : L) : adPoints L (PrimeField.rootSubgroupPoints (.inr i) L (Multiplicative.ofAdd t)) =
      yUnit .F4 L (nodeF i) t :=
  Units.ext (by rw [coe_adPoints, coe_primeFieldRootPoint, adConj_rootPoint_inr]; rfl)

end CFSG.TauCetiBridge.ReeF4
