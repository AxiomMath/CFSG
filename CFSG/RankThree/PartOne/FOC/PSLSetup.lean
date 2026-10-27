module

public import CFSG.RankThree.PartOne.FOC.PSLLift
public import CFSG.RankThree.PartOne.KC.LinearPlaneCore
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.PerfectCentral
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import Certificates.Certificate116
public import Certificates.Certificate119
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.RankThree.PartOne.FOC

open Polynomial Matrix Subgroup CFSG
open CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCLinPlane
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Setup

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def slEnd (A : Matrix.SpecialLinearGroup (Fin n) K) :
    Module.End K (Fin n → K) :=
  Matrix.toLin' ((Matrix.SpecialLinearGroup.toGL A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem slEnd_mul (A B : Matrix.SpecialLinearGroup (Fin n) K) :
    slEnd (A * B) = slEnd A * slEnd B := by
  unfold slEnd
  rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
  rfl

theorem slEnd_one : slEnd (1 : Matrix.SpecialLinearGroup (Fin n) K) = 1 := by
  unfold slEnd
  rw [map_one, Units.val_one, Matrix.toLin'_one]
  rfl

theorem slEnd_pow (A : Matrix.SpecialLinearGroup (Fin n) K) (k : ℕ) :
    slEnd (A ^ k) = slEnd A ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, slEnd_one]
  | succ k ih => rw [pow_succ, slEnd_mul, ih, pow_succ]

theorem squarefree_slEnd {p : ℕ} (hpK : (p : K) ≠ 0) {A : Matrix.SpecialLinearGroup (Fin n) K}
    (hAp : A ^ p = 1) : Squarefree (minpoly K (slEnd A)) :=
  squarefree_minpoly_of_pow_eq_one hpK (by rw [← slEnd_pow, hAp, slEnd_one])

variable {A : Matrix.SpecialLinearGroup (Fin n) K}

@[expose] noncomputable def blkSL (hsq : Squarefree (minpoly K (slEnd A)))
    (b : primaryFactors (slEnd A)) : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
  (blockImage hsq b).comap Matrix.SpecialLinearGroup.toGL

theorem mem_blkSL {hsq : Squarefree (minpoly K (slEnd A))} {b : primaryFactors (slEnd A)}
    {g : Matrix.SpecialLinearGroup (Fin n) K} :
    g ∈ blkSL hsq b ↔ Matrix.SpecialLinearGroup.toGL g ∈ blockImage hsq b := Iff.rfl

theorem blkSL_map [Finite K] {hsq : Squarefree (minpoly K (slEnd A))}
    {b : primaryFactors (slEnd A)} (hb : GoodBlock b) :
    (blkSL hsq b).map Matrix.SpecialLinearGroup.toGL = blockImage hsq b :=
  Subgroup.map_comap_eq_self (blockImage_le_range_toGL_of_good hsq b hb)

theorem blkSL_quasisimple [Finite K] {hsq : Squarefree (minpoly K (slEnd A))}
    {b : primaryFactors (slEnd A)} (hb : GoodBlock b) : CFSG.IsQuasisimple ↥(blkSL hsq b) := by
  have e : ↥(blkSL hsq b) ≃* ↥(blockImage hsq b) :=
    (Subgroup.equivMapOfInjective (blkSL hsq b) Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr (blkSL_map hb))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (isQuasisimple_blockImage_of_good hsq b hb)

theorem toGL_mem_centralizer {G : Matrix.SpecialLinearGroup (Fin n) K}
    (hG : G ∈ Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) K))) :
    Matrix.SpecialLinearGroup.toGL G ∈
      Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)) := by
  have hG' : G * A = A * G := Subgroup.mem_centralizer_singleton_iff.mp hG
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hG']

theorem blockImage_le_centralizer {hsq : Squarefree (minpoly K (slEnd A))}
    (b : primaryFactors (slEnd A)) :
    blockImage hsq b ≤
      Subgroup.centralizer ({Matrix.SpecialLinearGroup.toGL A} : Set (GL (Fin n) K)) := by
  rw [← range_commutantUnitsToGL_eq_centralizer (x := slEnd A)
    (Matrix.SpecialLinearGroup.toGL A) rfl]
  exact blockImage_le_range hsq b

theorem blkSL_le_centralizer {hsq : Squarefree (minpoly K (slEnd A))}
    (b : primaryFactors (slEnd A)) :
    blkSL hsq b ≤ Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
  intro g hg
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have h1 := blockImage_le_centralizer b hg
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul] at h1
  exact Matrix.SpecialLinearGroup.toGL_injective h1

theorem blkSL_norm {hsq : Squarefree (minpoly K (slEnd A))} (b : primaryFactors (slEnd A))
    {g : Matrix.SpecialLinearGroup (Fin n) K}
    (hg : g ∈ Subgroup.centralizer ({A} : Set (Matrix.SpecialLinearGroup (Fin n) K)))
    {f : Matrix.SpecialLinearGroup (Fin n) K} (hf : f ∈ blkSL hsq b) :
    g * f * g⁻¹ ∈ blkSL hsq b := by
  have h1 := toGL_mem_centralizer hg
  rw [← range_commutantUnitsToGL_eq_centralizer (x := slEnd A)
    (Matrix.SpecialLinearGroup.toGL A) rfl] at h1
  rw [mem_blkSL, map_mul, map_mul, map_inv]
  exact conj_mem_blockImage hsq b h1 hf

@[expose] noncomputable def Qb (hsq : Squarefree (minpoly K (slEnd A)))
    (b : primaryFactors (slEnd A)) : Subgroup (projectiveSL n K) :=
  (blkSL hsq b).map (proj n K)

theorem isComponentOf_Qb [Finite K] {hsq : Squarefree (minpoly K (slEnd A))}
    {b : primaryFactors (slEnd A)} (hb : GoodBlock b) :
    IsComponentOf (Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) (Qb hsq b) :=
  isComponentOf_map_block (proj n K) (proj_surjective n K)
    (by rw [ker_proj]; exact (scalars_eq_center n K).le) A (blkSL hsq b) (blkSL_quasisimple hb)
    (blkSL_le_centralizer b) fun _ hg _ hf => blkSL_norm b hg hf

theorem exists_lift_centralizer {p : ℕ} (hp : p.Prime) (hZ : ¬ p ∣ Nat.card (scalars n K))
    (hAp : A ^ p = 1) {u : projectiveSL n K}
    (hu : u ∈ Subgroup.centralizer ({proj n K A} : Set (projectiveSL n K))) :
    ∃ G : Matrix.SpecialLinearGroup (Fin n) K, proj n K G = u ∧ A * G = G * A := by
  obtain ⟨G, rfl⟩ := proj_surjective n K u
  refine ⟨G, rfl, commute_of_proj_commute hp hZ hAp ?_⟩
  exact (Subgroup.mem_centralizer_singleton_iff.mp hu).symm

end Setup

end CFSG.RankThree.PartOne.FOC
