module

public import CFSG.StronglyEmbedded.Catalog.Basic
public import CFSG.StronglyEmbedded.MatrixGroups.PSU3Model
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Agreement
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU

public section

namespace CFSG.BenderSuzuki.Catalog

open TauCeti Matrix

abbrev antidiag (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem typeAGraphConjugator_eq_antidiag (R : Type*) [CommRing R] [CharP R 2] :
    (typeAGraphConjugator 2 R : Matrix (Fin 3) (Fin 3) R) = antidiag R := by
  have h : (-1 : R) = 1 := CharTwo.neg_eq 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [typeAGraphConjugator, typeAGraphSign, h]

variable (n : ℕ) (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2]

noncomputable def unitarySteinberg :
    Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) K :=
  (Matrix.SpecialLinearGroup.typeAGraphAutomorphism 2 K).toMonoidHom.comp
    (slFrobenius (p := 2) K n)

variable {n K}

local notation "Fr" => iterateFrobenius K 2 n

omit [IsAlgClosed K] in
theorem toGL_slFrobenius (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    Matrix.SpecialLinearGroup.toGL (slFrobenius (p := 2) K n g) =
      GeneralLinearGroup.map Fr (Matrix.SpecialLinearGroup.toGL g) := by
  ext i j
  rfl

omit [IsAlgClosed K] in
theorem mem_fixedSubgroup_unitarySteinberg_iff_GL (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    g ∈ fixedSubgroup (unitarySteinberg n K) ↔
      typeAGraphAutomorphism 2 K (GeneralLinearGroup.map Fr (Matrix.SpecialLinearGroup.toGL g)) =
        Matrix.SpecialLinearGroup.toGL g := by
  rw [mem_fixedSubgroup, ← Matrix.SpecialLinearGroup.toGL_injective.eq_iff, unitarySteinberg,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism, toGL_slFrobenius]

omit [IsAlgClosed K] in
theorem mem_fixedSubgroup_unitarySteinberg_iff (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    g ∈ fixedSubgroup (unitarySteinberg n K) ↔
      ((g : Matrix (Fin 3) (Fin 3) K).map (· ^ 2 ^ n))ᵀ * antidiag K *
          (g : Matrix (Fin 3) (Fin 3) K) = antidiag K := by
  rw [mem_fixedSubgroup_unitarySteinberg_iff_GL,
    typeAGraphAutomorphism_eq_iff_transpose_mul_conjugator_mul_eq,
    typeAGraphConjugator_eq_antidiag]
  rfl

omit [IsAlgClosed K] in
theorem entry_pow_eq_self {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ fixedSubgroup (unitarySteinberg n K)) (i j : Fin 3) :
    (g : Matrix (Fin 3) (Fin 3) K) i j ^ 2 ^ (2 * n) = (g : Matrix (Fin 3) (Fin 3) K) i j := by
  set G := Matrix.SpecialLinearGroup.toGL g
  have hG : typeAGraphAutomorphism 2 K (GeneralLinearGroup.map Fr G) = G :=
    (mem_fixedSubgroup_unitarySteinberg_iff_GL g).mp hg
  have h1 : GeneralLinearGroup.map Fr G =
      typeAGraphAutomorphism 2 K (GeneralLinearGroup.map Fr (GeneralLinearGroup.map Fr G)) := by
    conv_lhs => rw [← hG]
    exact map_typeAGraphAutomorphism Fr 2 _
  have h2 : G = GeneralLinearGroup.map Fr (GeneralLinearGroup.map Fr G) :=
    hG.symm.trans ((congrArg _ h1).trans (typeAGraphAutomorphism_typeAGraphAutomorphism 2 _))
  have h3 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i j) h2
  simp only [GeneralLinearGroup.map_apply, iterateFrobenius_def] at h3
  have h4 : (g : Matrix (Fin 3) (Fin 3) K) i j =
      ((g : Matrix (Fin 3) (Fin 3) K) i j ^ 2 ^ n) ^ 2 ^ n := h3
  rw [two_mul, pow_add, pow_mul]
  exact h4.symm

local notation "F" => GaloisField 2 (2 * n)

variable (n K) in
noncomputable abbrev glMap : GL (Fin 3) F →* GL (Fin 3) K :=
  GeneralLinearGroup.map (galoisEmbedding 2 K (2 * n))

theorem glMap_injective : Function.Injective (glMap n K) := fun A B h => by
  ext i j
  exact (galoisEmbedding 2 K (2 * n)).injective
    (congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) i j) h)

noncomputable abbrev hermitianAdjoint (A : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.of fun i j => A j i ^ (2 ^ n)

theorem unitary_map_iff (A : Matrix (Fin 3) (Fin 3) F) :
    ((A.map (galoisEmbedding 2 K (2 * n))).map (· ^ 2 ^ n))ᵀ * antidiag K *
        A.map (galoisEmbedding 2 K (2 * n)) = antidiag K ↔
      hermitianAdjoint A * antidiag F * A = antidiag F := by
  let ι := galoisEmbedding 2 K (2 * n)
  have hJ : antidiag K = (antidiag F).map ι := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hadj : ((A.map ι).map (· ^ 2 ^ n))ᵀ = (hermitianAdjoint A).map ι := by
    ext i j
    simp [ι]
  rw [hJ, hadj, ← Matrix.map_mul, ← Matrix.map_mul]
  exact (Matrix.map_injective ι.injective).eq_iff

variable (n K) in
noncomputable def specialUnitary : Subgroup (GL (Fin 3) F) :=
  ((fixedSubgroup (unitarySteinberg n K)).map Matrix.SpecialLinearGroup.toGL).comap (glMap n K)

theorem mem_specialUnitary_iff (A : GL (Fin 3) F) :
    A ∈ specialUnitary n K ↔
      hermitianAdjoint (A : Matrix (Fin 3) (Fin 3) F) * antidiag F *
          (A : Matrix (Fin 3) (Fin 3) F) = antidiag F ∧ GeneralLinearGroup.det A = 1 := by
  let ι := galoisEmbedding 2 K (2 * n)
  rw [specialUnitary, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, hgA⟩
    have hmat : (g : Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 3) (Fin 3) F).map ι :=
      congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hgA
    refine ⟨(unitary_map_iff _).mp (hmat ▸ (mem_fixedSubgroup_unitarySteinberg_iff g).mp hg), ?_⟩
    apply Units.ext
    apply ι.injective
    have := congrArg Matrix.det hmat
    rw [g.2, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
    simpa using this.symm
  · rintro ⟨hU, hdet⟩
    have hdet' : ((A : Matrix (Fin 3) (Fin 3) F).map ι).det = 1 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have := congrArg Units.val hdet
      simp only [GeneralLinearGroup.val_det_apply, Units.val_one] at this
      rw [this, map_one]
    refine ⟨⟨_, hdet'⟩, ?_, ?_⟩
    · exact (mem_fixedSubgroup_unitarySteinberg_iff _).mpr ((unitary_map_iff _).mpr hU)
    · ext i j
      rfl

theorem map_toGL_le_range (hn : n ≠ 0) :
    (fixedSubgroup (unitarySteinberg n K)).map Matrix.SpecialLinearGroup.toGL ≤
      (glMap n K).range := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨A, hA⟩ := exists_map_galoisEmbedding_eq (p := 2) (k := 2 * n) (by omega)
    (g : Matrix (Fin 3) (Fin 3) K) (entry_pow_eq_self hg)
  have hdet : A.det = 1 := by
    apply (galoisEmbedding 2 K (2 * n)).injective
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, g.2, map_one]
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨A, hdet⟩, ?_⟩
  ext i j
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j) hA

variable (K) in
noncomputable def fixedEquivSpecialUnitary (hn : n ≠ 0) :
    ↥(fixedSubgroup (unitarySteinberg n K)) ≃* ↥(specialUnitary n K) :=
  ((fixedSubgroup (unitarySteinberg n K)).equivMapOfInjective _
      Matrix.SpecialLinearGroup.toGL_injective).trans
    ((MulEquiv.subgroupCongr (by
        rw [specialUnitary, Subgroup.map_comap_eq, inf_eq_right.mpr (map_toGL_le_range hn)])).trans
      ((specialUnitary n K).equivMapOfInjective _ glMap_injective).symm)

theorem psu3Model_eq_map_specialUnitary :
    Theory.Comparator.PSU3Model n = (specialUnitary n K).map ProjGenLinGroup.mk := by
  rw [Theory.Comparator.PSU3Model]
  congr 1
  rw [← Subgroup.closure_eq (specialUnitary n K)]
  congr 1
  ext A
  exact (mem_specialUnitary_iff A).symm

variable (n K) in
noncomputable def fixedPointCandidateEquivPSU3Model (hn : n ≠ 0)
    [IsSimpleGroup (Theory.Comparator.PSU3Model n)] (hP : ¬ IsMulCommutative (Theory.Comparator.PSU3Model n)) :
    FixedPointCandidate (unitarySteinberg n K) ≃* Theory.Comparator.PSU3Model n :=
  let e := fixedEquivSpecialUnitary K hn
  let c := MulEquiv.subgroupCongr (psu3Model_eq_map_specialUnitary (n := n) (K := K))
  derivedCentralQuotientEquiv hP
    (c.symm.toMonoidHom.comp ((ProjGenLinGroup.mk.subgroupMap _).comp e.toMonoidHom))
    (c.symm.surjective.comp ((ProjGenLinGroup.mk.subgroupMap_surjective _).comp e.surjective))
    fun h hh => by
      have h1 : ProjGenLinGroup.mk.subgroupMap _ (e h) = 1 := by
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
          MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
          map_eq_one_iff _ c.symm.injective] at hh
        exact hh
      have h2 : ((e h : GL (Fin 3) F)) ∈ Subgroup.center (GL (Fin 3) F) := by
        rw [← ProjGenLinGroup.mk_eq_one]
        simpa using congrArg Subtype.val h1
      have h3 : e h ∈ Subgroup.center ↥(specialUnitary n K) :=
        Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_center_iff.mp h2 y)
      simpa using GorensteinWalter.preambleCenter_mem_map e.symm h3

section Index

variable {n : ℕ} (hn : 0 < n)
  (hv : (LieTypeIndex.twistedA 2 ⟨2, n, Nat.prime_two, hn⟩).Valid)

instance charP_closure_twistedA : CharP (ValidLieTypeIndex.Closure ⟨_, hv⟩) 2 := by
  have h := (inferInstance : CharP (ValidLieTypeIndex.Closure ⟨_, hv⟩)
    (ValidLieTypeIndex.characteristic ⟨_, hv⟩))
  simpa only [ValidLieTypeIndex.characteristic, LieTypeIndex.characteristic_twistedA] using h

noncomputable def carrierEquivTwistedA :
    ValidLieTypeIndex.AmbientGroup ⟨_, hv⟩ ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ValidLieTypeIndex.Closure ⟨_, hv⟩) :=
  (TypeALieIndex.ofTwistedA 2 _ hv).carrierEquivSpecialLinear

private theorem carrierEquivTwistedA_comp_steinberg :
    (carrierEquivTwistedA hn hv).toMonoidHom.comp (ValidLieTypeIndex.steinberg ⟨_, hv⟩) =
      (unitarySteinberg n _).comp (carrierEquivTwistedA hn hv).toMonoidHom := by
  have hF : (TypeALieIndex.ofTwistedA 2 _ hv).specialLinearFrobenius =
      slFrobenius (p := 2) (ValidLieTypeIndex.Closure ⟨_, hv⟩) n := by
    ext g i j
    simp [TypeALieIndex.specialLinearFrobenius, iterateFrobenius_def,
      ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent]
  refine MonoidHom.ext fun g => ?_
  have key := (TypeALieIndex.ofTwistedA 2 _ hv).carrierEquivSpecialLinear_steinberg g
  rw [TypeALieIndex.specialLinearSteinberg, TypeALieIndex.specialLinearGraphAut_ofTwistedA,
    hF] at key
  exact key

noncomputable def groupEquivPSU3Model [IsSimpleGroup (Theory.Comparator.PSU3Model n)]
    (hP : ¬ IsMulCommutative (Theory.Comparator.PSU3Model n)) :
    ValidLieTypeIndex.Group ⟨_, hv⟩ ≃* Theory.Comparator.PSU3Model n :=
  (FixedPointCandidate.congr _ (carrierEquivTwistedA_comp_steinberg hn hv)).trans
    (fixedPointCandidateEquivPSU3Model n _ hn.ne' hP)

end Index

end CFSG.BenderSuzuki.Catalog
