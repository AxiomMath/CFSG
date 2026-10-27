module

public import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgUnitaryBlock
import CFSG.LocalAnalysis.StandardType.GGLieInnerDiagSLPack
import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.LinUnitUnitaryBlocks
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSpecial
import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie CFSG.HardMathSupport.Solomon.Coordinator.LieComp

section MatrixKernel

variable {E W : Type} [Field E] [AddCommGroup W] [Module E W]

private noncomputable def ltunipair_matrixKernelHom {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) E →*
      (Units.map (LinearMap.det : Module.End E W →* E)).ker :=
  MonoidHom.codRestrict
    ((SpecialLinearGroup.toGeneralLinearGroup (R := E) (V := W)).comp
      (Matrix.SpecialLinearGroup.toLin_equiv b).toMonoidHom)
    (Units.map (LinearMap.det : Module.End E W →* E)).ker (fun u => by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Units.val_one]
      change LinearMap.det ((Matrix.SpecialLinearGroup.toLin_equiv b u :
        SpecialLinearGroup E W) : W →ₗ[E] W) = 1
      exact SpecialLinearGroup.det_eq_one _)

private theorem ltunipair_matrixKernelHom_injective {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W) :
    Function.Injective (ltunipair_matrixKernelHom (E := E) (W := W) b) := by
  intro u v huv
  have h' : SpecialLinearGroup.toGeneralLinearGroup
        (Matrix.SpecialLinearGroup.toLin_equiv b u) =
      SpecialLinearGroup.toGeneralLinearGroup
        (Matrix.SpecialLinearGroup.toLin_equiv b v) := Subtype.ext_iff.mp huv
  exact (Matrix.SpecialLinearGroup.toLin_equiv b).injective
    (SpecialLinearGroup.toGeneralLinearGroup_injective h')

private theorem ltunipair_matrixKernelHom_surjective {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W) :
    Function.Surjective (ltunipair_matrixKernelHom (E := E) (W := W) b) := by
  intro γ
  have hγ : (γ.1 : (Module.End E W)ˣ) ∈
      Set.range (SpecialLinearGroup.toGeneralLinearGroup (R := E) (V := W)) := by
    rw [SpecialLinearGroup.mem_range_toGeneralLinearGroup_iff]
    apply Units.ext
    rw [LinearEquiv.coe_det, Units.val_one]
    change LinearMap.det ((γ.1 : (Module.End E W)ˣ) : Module.End E W) = 1
    simpa using congrArg Units.val γ.2
  obtain ⟨u, hu⟩ := hγ
  refine ⟨(Matrix.SpecialLinearGroup.toLin_equiv b).symm u, ?_⟩
  apply Subtype.ext
  show SpecialLinearGroup.toGeneralLinearGroup
      (Matrix.SpecialLinearGroup.toLin_equiv b
        ((Matrix.SpecialLinearGroup.toLin_equiv b).symm u)) = γ.1
  rw [MulEquiv.apply_symm_apply, hu]

private theorem ltunipair_toLinAlgEquiv_conj {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W)
    (A : GL (Fin (m + 1)) E) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) E) :
    (Matrix.SpecialLinearGroup.toLin_equiv b (InnerDiagA.conjSL A u) : W →ₗ[E] W) =
      Matrix.toLinAlgEquiv b (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) *
        (Matrix.SpecialLinearGroup.toLin_equiv b u : W →ₗ[E] W) *
        Matrix.toLinAlgEquiv b ((A⁻¹ : GL (Fin (m + 1)) E) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) E) := by
  have h1 : (Matrix.SpecialLinearGroup.toLin_equiv b (InnerDiagA.conjSL A u) : W →ₗ[E] W) =
      Matrix.toLinAlgEquiv b (↑(InnerDiagA.conjSL A u) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) E) := by
    rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
    rfl
  have h2 : (Matrix.SpecialLinearGroup.toLin_equiv b u : W →ₗ[E] W) =
      Matrix.toLinAlgEquiv b (↑u : Matrix (Fin (m + 1)) (Fin (m + 1)) E) := by
    rw [Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq]
    rfl
  rw [h1, h2, InnerDiagA.coe_conjSL]
  simp only [map_mul]

private theorem ltunipair_matrixKernelHom_conj_end {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W)
    (γ : (Module.End E W)ˣ) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) E) :
    ((ltunipair_matrixKernelHom (E := E) (W := W) b
        (InnerDiagA.conjSL (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ) u) :
        (Module.End E W)ˣ) : Module.End E W) =
      (γ : Module.End E W) *
        ((ltunipair_matrixKernelHom (E := E) (W := W) b u : (Module.End E W)ˣ) :
          Module.End E W) * (↑(γ⁻¹) : Module.End E W) := by
  show (Matrix.SpecialLinearGroup.toLin_equiv b
      (InnerDiagA.conjSL (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ) u) :
        W →ₗ[E] W) =
    (γ : Module.End E W) *
      (Matrix.SpecialLinearGroup.toLin_equiv b u : W →ₗ[E] W) * (↑(γ⁻¹) : Module.End E W)
  rw [ltunipair_toLinAlgEquiv_conj b
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ) u]
  have hAval : ((Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ :
      Matrix.GeneralLinearGroup (Fin (m + 1)) E) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) E) =
      LinearMap.toMatrixAlgEquiv b (γ : Module.End E W) := rfl
  have hAinv : (((Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ)⁻¹ :
      Matrix.GeneralLinearGroup (Fin (m + 1)) E) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) E) =
      LinearMap.toMatrixAlgEquiv b (↑(γ⁻¹) : Module.End E W) := by
    rw [← map_inv, Units.coe_mapEquiv]
    rfl
  simp only [hAval, hAinv, Matrix.toLinAlgEquiv_toMatrixAlgEquiv]

private theorem ltunipair_matrixKernelHom_conj {m : ℕ} (b : Module.Basis (Fin (m + 1)) E W)
    (γ : (Module.End E W)ˣ) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) E) :
    (ltunipair_matrixKernelHom (E := E) (W := W) b
        (InnerDiagA.conjSL (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv γ) u) :
        (Module.End E W)ˣ) =
      γ * (ltunipair_matrixKernelHom (E := E) (W := W) b u : (Module.End E W)ˣ) * γ⁻¹ := by
  apply Units.ext
  exact ltunipair_matrixKernelHom_conj_end b γ u

end MatrixKernel

section Restrict

variable {ℓ f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
  {x : LinearMap.GeneralLinearGroup K (Fin n → K)}

private noncomputable def ltunipair_restrictHom
    (a : primaryFactors (x : Module.End K (Fin n → K))) :
    ↥(specialBlock (idForm h n) x (a : K[X])) →*
      blockGL (x : Module.End K (Fin n → K)) (a : K[X]) :=
  (blockRestrict x (a : K[X])).comp
    (Subgroup.inclusion (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer))

private theorem ltunipair_restrictHom_apply
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (g : ↥(specialBlock (idForm h n) x (a : K[X]))) :
    (ltunipair_restrictHom (h := h) (x := x) a g :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) =
      blockRestrict x (a : K[X]) ⟨g.1,
        (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer) g.2⟩ := rfl

private noncomputable def ltunipair_restrictToKer
    (a : primaryFactors (x : Module.End K (Fin n → K))) :
    ↥(specialBlock (idForm h n) x (a : K[X])) →*
      (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker :=
  (ltunipair_restrictHom (h := h) (x := x) a).codRestrict
    (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker (fun g => by
      show blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])
        (blockRestrict x (a : K[X])
          ⟨g.1, (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer) g.2⟩) = 1
      obtain ⟨-, hg, hdet⟩ := mem_specialBlock.mp g.2
      have hsub : (⟨g.1, (specialBlock_le_orbitFactor.trans
          orbitFactor_le_gl_centralizer) g.2⟩ : gl_centralizer x) = ⟨g.1, hg⟩ :=
        Subtype.ext rfl
      rw [hsub]
      exact hdet)

private theorem ltunipair_restrictToKer_apply
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (g : ↥(specialBlock (idForm h n) x (a : K[X]))) :
    ((ltunipair_restrictToKer (h := h) (x := x) a g :
        (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker) :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) =
      blockRestrict x (a : K[X]) ⟨g.1,
        (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer) g.2⟩ := rfl

private theorem ltunipair_restrictToKer_injective
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (hP : PairedPrimaryBlock h (idForm h n) x a) :
    ∀ g g' : ↥(specialBlock (idForm h n) x (a : K[X])),
      ltunipair_restrictToKer (h := h) (x := x) a g =
        ltunipair_restrictToKer (h := h) (x := x) a g' → g = g' := by
  have hinj : Function.Injective (ltunipair_restrictHom (h := h) (x := x) a) := by
    intro g g' hgg
    obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
    have hcompat : ∀ s : orbitFactor (idForm h n) x (a : K[X]),
        φ s = blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
      fun s => blockGL_ext fun v hv => hφ s v hv
    have h1 : φ ⟨g.1, specialBlock_le_orbitFactor g.2⟩ =
        φ ⟨g'.1, specialBlock_le_orbitFactor g'.2⟩ := by
      rw [hcompat ⟨g.1, specialBlock_le_orbitFactor g.2⟩,
        hcompat ⟨g'.1, specialBlock_le_orbitFactor g'.2⟩]
      simpa only [ltunipair_restrictHom_apply] using hgg
    exact Subtype.ext (congrArg (fun z : orbitFactor (idForm h n) x (a : K[X]) =>
      (z : LinearMap.GeneralLinearGroup K (Fin n → K))) (φ.injective h1))
  intro g g' hgg
  exact hinj (congrArg (fun z : ↥(blockGLDet (x : Module.End K (Fin n → K))
    (a : K[X])).ker => (z : blockGL (x : Module.End K (Fin n → K)) (a : K[X]))) hgg)

private theorem ltunipair_restrictToKer_surjective
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (hP : PairedPrimaryBlock h (idForm h n) x a) :
    Function.Surjective (ltunipair_restrictToKer (h := h) (x := x) a) := by
  obtain ⟨φ, hφ, -⟩ := exists_pairedFactor hP
  have hcompat : ∀ s : orbitFactor (idForm h n) x (a : K[X]),
      φ s = blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩ :=
    fun s => blockGL_ext fun v hv => hφ s v hv
  intro γ
  let s : orbitFactor (idForm h n) x (a : K[X]) := φ.symm γ.1
  have hφs : φ s = γ.1 := φ.apply_symm_apply γ.1
  have hsB : s.1 ∈ specialBlock (idForm h n) x (a : K[X]) := by
    rw [mem_specialBlock]
    refine ⟨s.2, orbitFactor_le_gl_centralizer s.2, ?_⟩
    change blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])
      (blockRestrict x (a : K[X]) ⟨s.1, orbitFactor_le_gl_centralizer s.2⟩) = 1
    rw [← hcompat s, hφs]
    exact γ.2
  refine ⟨⟨s.1, hsB⟩, ?_⟩
  apply Subtype.ext
  rw [ltunipair_restrictToKer_apply]
  exact (hcompat s).symm.trans hφs

private noncomputable def ltunipair_blockKerEquiv
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (hP : PairedPrimaryBlock h (idForm h n) x a) :
    ↥(specialBlock (idForm h n) x (a : K[X])) ≃*
      (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker :=
  MulEquiv.ofBijective (ltunipair_restrictToKer (h := h) (x := x) a)
    ⟨ltunipair_restrictToKer_injective a hP, ltunipair_restrictToKer_surjective a hP⟩

private theorem ltunipair_blockKerEquiv_apply
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (hP : PairedPrimaryBlock h (idForm h n) x a)
    (g : ↥(specialBlock (idForm h n) x (a : K[X]))) :
    ((ltunipair_blockKerEquiv a hP g :
        (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker) :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) =
      blockRestrict x (a : K[X]) ⟨g.1,
        (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer) g.2⟩ := rfl

private theorem ltunipair_blockKerEquiv_conj
    (a : primaryFactors (x : Module.End K (Fin n → K)))
    (hP : PairedPrimaryBlock h (idForm h n) x a)
    (γ : LinearMap.GeneralLinearGroup K (Fin n → K))
    (hγ : γ ∈ unitaryCentralizer (idForm h n) x)
    (g : ↥(specialBlock (idForm h n) x (a : K[X]))) :
    ((ltunipair_blockKerEquiv a hP
        ⟨γ * (g : LinearMap.GeneralLinearGroup K (Fin n → K)) * γ⁻¹,
          conj_mem_specialBlock hγ g.2⟩ :
        (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker) :
        blockGL (x : Module.End K (Fin n → K)) (a : K[X])) =
      blockRestrict x (a : K[X]) ⟨γ,
          mem_gl_centralizer.mpr (mem_unitaryCentralizer.mp hγ).2⟩ *
        ((ltunipair_blockKerEquiv a hP g :
          (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker) :
          blockGL (x : Module.End K (Fin n → K)) (a : K[X])) *
        (blockRestrict x (a : K[X]) ⟨γ,
          mem_gl_centralizer.mpr (mem_unitaryCentralizer.mp hγ).2⟩)⁻¹ := by
  rw [ltunipair_blockKerEquiv_apply, ltunipair_blockKerEquiv_apply]
  rw [show (⟨γ * (g : LinearMap.GeneralLinearGroup K (Fin n → K)) * γ⁻¹,
        (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer)
          (conj_mem_specialBlock hγ g.2)⟩ : gl_centralizer x) =
      ⟨γ, mem_gl_centralizer.mpr (mem_unitaryCentralizer.mp hγ).2⟩ *
        (⟨g.1, (specialBlock_le_orbitFactor.trans orbitFactor_le_gl_centralizer) g.2⟩ :
          gl_centralizer x) *
        (⟨γ, mem_gl_centralizer.mpr (mem_unitaryCentralizer.mp hγ).2⟩ :
          gl_centralizer x)⁻¹ from Subtype.ext rfl]
  rw [map_mul, map_mul, map_inv]

end Restrict

theorem ggLinearOn_unitaryBlock_paired {f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (A B : primeFormUnitary h (idGram K n)) {c : Kˣ}
    (hA3 : (A : GL (Fin n) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (hAB : (A : GL (Fin n) K) * (B : GL (Fin n) K) = (B : GL (Fin n) K) * (A : GL (Fin n) K))
    (a : primaryFactors
      (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) : Module.End K (Fin n → K)))
    (ha : IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) a)
    (hpair : ¬ dualPoly h.bar (a : K[X]) = a)
    (hTq : CFSG.Open.IsQuasisimple ↥(unitaryBlockComponent h
      (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X])))
    (hstab : primeFormConjHom h (idGram K n) B ∈ CFSG.GroupActions.subgroupStabAut
      (unitaryBlockComponent h (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K))
        (a : K[X]))) :
    GGLinearOn (unitaryBlockComponent h
        (x := Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)) (a : K[X]))
      (primeFormConjHom h (idGram K n) B) := by
  classical
  have hne : (a : K[X]) ≠ dualPoly h.bar (a : K[X]) := fun hh => hpair hh.symm
  let x : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)
  let Y : LinearMap.GeneralLinearGroup K (Fin n → K) :=
    Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K)
  haveI : CharP K 2 := h.charP
  have H : UnitaryPrimaryData h.bar (idForm h n) x :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.UnitaryBlocks.primaryData_toLin'
      h A.2 Nat.prime_three (by norm_num) hA3
  have hP : PairedPrimaryBlock h (idForm h n) x a :=
    pairedPrimaryBlock (hK := h) (B := idForm h n) (x := x) H a hne
  have hAB' : x * Y = Y * x := by
    show Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K) *
        Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) *
        Matrix.GeneralLinearGroup.toLin (A : GL (Fin n) K)
    rw [← map_mul, ← map_mul, hAB]
  have hcomm : Commute (Y : Module.End K (Fin n → K)) (x : Module.End K (Fin n → K)) :=
    congrArg Units.val hAB'.symm
  have hYuni : Y ∈ sesqUnitaryGroup (idForm h n) :=
    (toLin_mem_sesqUnitaryGroup_iff (h := h) (n := n) (B : GL (Fin n) K)).mpr B.2
  have hYgl : Y ∈ gl_centralizer x := mem_gl_centralizer.mpr hcomm
  have hYmem : Y ∈ unitaryCentralizer (idForm h n) x :=
    mem_unitaryCentralizer.mpr ⟨hYuni, hcomm⟩
  let E := AdjoinRoot (a : K[X])
  let W := primaryComponent (x : Module.End K (Fin n → K)) (a : K[X])
  let m0 := primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) - 1
  haveI : Module.Finite K E := (monic_of_mem_primaryFactors a.2).finite_adjoinRoot
  haveI : Finite K := h.finite
  haveI : Finite E := Module.finite_of_finite K
  haveI : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap K E).injective 2
  have hcardE : Nat.card E = 2 ^ (2 * (f * (a : K[X]).natDegree)) :=
    natCard_adjoinRoot h
  have h4E : 4 ≤ Nat.card E := by
    rw [hcardE]
    have hd : 1 ≤ (a : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
    have h2 : 2 ≤ 2 * (f * (a : K[X]).natDegree) := by
      have hf1 : 1 ≤ f := h.one_le
      nlinarith
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * (f * (a : K[X]).natDegree)) := Nat.pow_le_pow_right (by norm_num) h2
  have hb : Module.finrank E W = m0 + 1 := by
    have h1 : 1 ≤ primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) :=
      le_trans (by norm_num) ha.1
    have h2 : m0 + 1 = primaryMultiplicity (x : Module.End K (Fin n → K)) (a : K[X]) :=
      Nat.sub_add_cancel h1
    rw [h2]
  let b : Module.Basis (Fin (m0 + 1)) E W := Module.finBasisOfFinrankEq E W hb
  let θmat : (Module.End E W)ˣ ≃* Matrix.GeneralLinearGroup (Fin (m0 + 1)) E :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let γ₀ : (Module.End E W)ˣ := blockRestrict x (a : K[X]) ⟨Y, hYgl⟩
  let Amat : GL (Fin (m0 + 1)) E := θmat γ₀
  let e2 : Matrix.SpecialLinearGroup (Fin (m0 + 1)) E →*
      (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker :=
    ltunipair_matrixKernelHom b
  let eB : ↥(specialBlock (idForm h n) x (a : K[X])) ≃*
      (blockGLDet (x : Module.End K (Fin n → K)) (a : K[X])).ker :=
    ltunipair_blockKerEquiv a hP
  let πF : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) →*
      ↥(unitaryBlockComponent h (x := x) (a : K[X])) :=
    MonoidHom.subgroupMap (QuotientGroup.mk' (unitaryNormOneScalars h n))
      (unitaryPreimageBlock h (x := x) (a : K[X]))
  have hq2 : 2 ≤ 2 ^ f :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.one_le
  let ε : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) ≃*
      ↥(specialBlock (idForm h n) x (a : K[X])) :=
    specialBlockEquiv h H a hq2 ha
  let φ : Matrix.SpecialLinearGroup (Fin (m0 + 1)) E →*
      ↥(unitaryBlockComponent h (x := x) (a : K[X])) :=
    πF.comp (ε.symm.toMonoidHom.comp (eB.symm.toMonoidHom.comp e2))
  have hπF : Function.Surjective πF ∧ πF.ker ≤
      Subgroup.center ↥(unitaryPreimageBlock h (x := x) (a : K[X])) :=
    subgroupMap_mk'_surjective_ker_le_center (h := h) (x := x) a
  have hφ : Function.Surjective φ :=
    hπF.1.comp (ε.symm.surjective.comp (eB.symm.surjective.comp
      (ltunipair_matrixKernelHom_surjective b)))
  have hker : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m0 + 1)) E) := by
    rw [← MonoidHom.comap_ker]
    refine (Subgroup.comap_mono hπF.2).trans ?_
    have hinj : Function.Injective
        ⇑(ε.symm.toMonoidHom.comp (eB.symm.toMonoidHom.comp e2)) :=
      ε.symm.injective.comp (eB.symm.injective.comp
        (ltunipair_matrixKernelHom_injective b))
    exact Subgroup.comap_center_le_center hinj
  have hA : ∀ u : Matrix.SpecialLinearGroup (Fin (m0 + 1)) E,
      (primeFormConjHom h (idGram K n) B) (φ u) =
        ((φ (InnerDiagA.conjSL Amat u) :
          ↥(unitaryBlockComponent h (x := x) (a : K[X]))) :
          primeFormP h (idGram K n)) := by
    intro u
    let s : ↥(specialBlock (idForm h n) x (a : K[X])) := eB.symm (e2 u)
    let f : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := ε.symm s
    have hs' : Y * (s : LinearMap.GeneralLinearGroup K (Fin n → K)) * Y⁻¹ ∈
        specialBlock (idForm h n) x (a : K[X]) := conj_mem_specialBlock hYmem s.2
    let s' : ↥(specialBlock (idForm h n) x (a : K[X])) :=
      ⟨Y * (s : LinearMap.GeneralLinearGroup K (Fin n → K)) * Y⁻¹, hs'⟩
    let f' : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) := ε.symm s'
    have hss : eB s' = e2 (InnerDiagA.conjSL Amat u) := by
      apply Subtype.ext
      rw [ltunipair_blockKerEquiv_conj a hP Y hYmem s]
      rw [show eB s = e2 u from eB.apply_symm_apply (e2 u)]
      exact (ltunipair_matrixKernelHom_conj b γ₀ u).symm
    have hmem : primeFormConjSU h (idGram K n) B (f : ↥(gramSU h (idGram K n))) ∈
        unitaryPreimageBlock h (x := x) (a : K[X]) := by
      change toLinSU h n (primeFormConjSU h (idGram K n) B
        (f : ↥(gramSU h (idGram K n)))) ∈ specialBlock (idForm h n) x (a : K[X])
      rw [toLinSU_primeFormConjSU]
      have hf : toLinSU h n (f : ↥(gramSU h (idGram K n))) =
          (s : LinearMap.GeneralLinearGroup K (Fin n → K)) := by
        have h1 := specialBlockEquiv_apply_coe (h := h) H a hq2 ha (ε.symm s)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm
      rw [hf]
      exact hs'
    have hff' : (primeFormConjSU h (idGram K n) B (f : ↥(gramSU h (idGram K n))) :
        ↥(gramSU h (idGram K n))) = (f' : ↥(gramSU h (idGram K n))) := by
      have hε : ε ⟨primeFormConjSU h (idGram K n) B
          (f : ↥(gramSU h (idGram K n))), hmem⟩ = s' := by
        apply Subtype.ext
        rw [specialBlockEquiv_apply_coe, toLinSU_primeFormConjSU]
        have hf : toLinSU h n (f : ↥(gramSU h (idGram K n))) =
            (s : LinearMap.GeneralLinearGroup K (Fin n → K)) := by
          have h1 := specialBlockEquiv_apply_coe (h := h) H a hq2 ha (ε.symm s)
          rw [MulEquiv.apply_symm_apply] at h1
          exact h1.symm
        rw [hf]
      have h2 : (⟨primeFormConjSU h (idGram K n) B
          (f : ↥(gramSU h (idGram K n))), hmem⟩ :
          ↥(unitaryPreimageBlock h (x := x) (a : K[X]))) = f' := by
        have h3 := congrArg (fun z => ε.symm z) hε
        simpa using h3
      exact congrArg (fun z : ↥(unitaryPreimageBlock h (x := x) (a : K[X])) =>
        (z : ↥(gramSU h (idGram K n)))) h2
    have hφconj : φ (InnerDiagA.conjSL Amat u) = πF f' := by
      have hsymm : eB.symm (e2 (InnerDiagA.conjSL Amat u)) = s' := by
        rw [← hss, eB.symm_apply_apply]
      change πF (ε.symm (eB.symm (e2 (InnerDiagA.conjSL Amat u)))) = πF f'
      rw [hsymm]
    rw [hφconj]
    change primeFormConjHom h (idGram K n) B
      ((f : ↥(gramSU h (idGram K n))) : primeFormP h (idGram K n)) =
      ((f' : ↥(gramSU h (idGram K n))) : primeFormP h (idGram K n))
    rw [primeFormConjHom_mk]
    congr 1
  exact ggLinearOn_of_slConj hTq h4E φ hφ hker Amat hA

end CFSG.StandardType.SCFourCover

end
