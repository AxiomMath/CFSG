module

public import CFSG.HardMathSupport.Foote.Coordinator.LangTorus.Monomial
public import CFSG.RankThree.PartOne.KE6.E8T3E6
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.CTCasesCycloGlue
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate1952

public section

namespace CFSG.StandardType

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Foote.Coordinator (blockP)
open CFSG.HardMathSupport.Foote.Coordinator
  (extJ' extJ'_apply_mem extJ'_apply_notMem sum_fin_eq_sum_J' smul_single_apply_eq_zero
   weylMatrix_mulVec_extJ' weylMatrix_pow_mulVec_extJ' iform_eq_sum_single')

@[expose] def cartanBlock (τ : Tag) (J : Set (Fin τ.rank)) : Matrix J J ℤ :=
  Matrix.of fun j m => τ.cartan j m

section Block

variable
  {τ : Tag} {w : WeylGroup τ} {J : Set (Fin τ.rank)} [Fintype J] [DecidableEq J]

private lemma iform_extJ'_cartan (hsym : τ.symmetrizer = 1) (a b : J → ℤ) :
    iform (extJ' J a) (extJ' J b) = ∑ m : J, ∑ l : J, a m * τ.cartan m l * b l := by
  rw [iform_eq_sum_single']
  rw [sum_fin_eq_sum_J' J (fun i => extJ' J a i * iform (Pi.single i 1) (extJ' J b))
    (fun i hi => by rw [extJ'_apply_notMem a hi, zero_mul])]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [extJ'_apply_mem a m.2, iform_single_left]
  have hsymm : τ.symmetrizer (m : Fin τ.rank) (m : Fin τ.rank) = 1 := by
    rw [hsym]; simp
  have hinner : (∑ j, τ.cartan (m : Fin τ.rank) j * extJ' J b j) =
      ∑ l : J, τ.cartan (m : Fin τ.rank) l * b l := by
    rw [sum_fin_eq_sum_J' J (fun j => τ.cartan (m : Fin τ.rank) j * extJ' J b j)
      (fun j hj => by rw [extJ'_apply_notMem b hj, mul_zero])]
    exact Finset.sum_congr rfl fun l _ => by rw [extJ'_apply_mem b l.2]
  rw [hsymm, hinner, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

theorem blockP_sq_add_self_add_one
    (hJ : ∀ β ∈ parabolicRoots τ J, w • β ∈ parabolicRoots τ J)
    (hrel : ∀ x : Fin τ.rank → ℤ, w • w • x + w • x + x = 0) :
    blockP w J * blockP w J + blockP w J + 1 = 0 := by
  classical
  refine Matrix.ext_of_mulVec_single fun c => ?_
  set u : J → ℤ := Pi.single c 1
  have h2 := weylMatrix_pow_mulVec_extJ' (J := J) hJ 2 u
  have h1 := weylMatrix_mulVec_extJ' (J := J) hJ u
  have hrelx : weylMatrix w ^ 2 *ᵥ extJ' J u + weylMatrix w *ᵥ extJ' J u + extJ' J u = 0 := by
    have h := hrel (extJ' J u)
    simp only [← weylMatrix_mulVec, Matrix.mulVec_mulVec, ← pow_two] at h
    exact h
  rw [h2, h1] at hrelx
  have key : ∀ j : J, (blockP w J ^ 2 *ᵥ u) j + (blockP w J *ᵥ u) j + u j = 0 := by
    intro j
    have hj := congrFun hrelx j
    rw [Pi.add_apply, Pi.add_apply, extJ'_apply_mem (blockP w J ^ 2 *ᵥ u) j.2,
      extJ'_apply_mem (blockP w J *ᵥ u) j.2, extJ'_apply_mem u j.2] at hj
    exact hj
  funext j
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec, Pi.add_apply,
    Pi.add_apply]
  simpa [pow_two] using key j

theorem blockP_transpose_mul_cartanBlock_mul_self (hsym : τ.symmetrizer = 1)
    (hJ : ∀ β ∈ parabolicRoots τ J, w • β ∈ parabolicRoots τ J) :
    (blockP w J)ᵀ * cartanBlock τ J * blockP w J = cartanBlock τ J := by
  classical
  ext j k
  change ((blockP w J)ᵀ * cartanBlock τ J * blockP w J) j k
      = τ.cartan (j : Fin τ.rank) (k : Fin τ.rank)
  have hL : ((blockP w J)ᵀ * cartanBlock τ J * blockP w J) j k
      = ∑ m : J, ∑ l : J, blockP w J m j * blockP w J l k * τ.cartan m l := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, cartanBlock, Matrix.of_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  have hcol : ∀ i : J, w • (Pi.single (i : Fin τ.rank) 1 : Fin τ.rank → ℤ)
      = extJ' J (fun m : J => blockP w J m i) := by
    intro i
    funext a
    by_cases ha : a ∈ J
    · rw [extJ'_apply_mem (fun m : J => blockP w J m i) ha]; rfl
    · rw [extJ'_apply_notMem (fun m : J => blockP w J m i) ha]
      exact smul_single_apply_eq_zero hJ i.2 ha
  have hiform : iform (w • (Pi.single (j : Fin τ.rank) 1 : Fin τ.rank → ℤ))
      (w • (Pi.single (k : Fin τ.rank) 1 : Fin τ.rank → ℤ))
      = ∑ m : J, ∑ l : J, blockP w J m j * blockP w J l k * τ.cartan m l := by
    rw [hcol j, hcol k, iform_extJ'_cartan hsym]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun l _ => by ring
  have hbase : iform (Pi.single (j : Fin τ.rank) 1 : Fin τ.rank → ℤ)
      (Pi.single (k : Fin τ.rank) 1) = τ.cartan (j : Fin τ.rank) (k : Fin τ.rank) := by
    rw [iform_single_left]
    have hsymm : τ.symmetrizer (j : Fin τ.rank) (j : Fin τ.rank) = 1 := by
      rw [hsym]; simp
    rw [hsymm, one_mul]
    rw [Finset.sum_eq_single (k : Fin τ.rank)
      (fun b _ hb => by rw [Pi.single_eq_of_ne hb]; simp)
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [hL, ← hiform, iform_smul, hbase]

end Block

section E8

private def e6NodesEquiv : Fin 6 ≃ ↥(e6Nodes Tag.E8) where
  toFun i := ⟨Fin.castLE (by decide) i, by
    simp only [e6Nodes, Set.mem_setOf_eq, Fin.val_castLE]
    omega⟩
  invFun j := ⟨j.1.val, by
    have h := j.2
    simp only [e6Nodes, Set.mem_setOf_eq] at h
    omega⟩
  left_inv i := by
    apply Fin.ext
    rfl
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    rfl

private def d4NodesEquiv : Fin 4 ≃ ↥(d4Nodes Tag.E8) where
  toFun i := ⟨⟨i.val + 1, by
    have hrank : Tag.E8.rank = 8 := rfl
    rw [hrank] at *
    omega⟩, by
    simp only [d4Nodes, Set.mem_setOf_eq]
    omega⟩
  invFun j := ⟨j.1.val - 1, by
    have h := j.2
    simp only [d4Nodes, Set.mem_setOf_eq] at h
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have h := j.2
    simp only [d4Nodes, Set.mem_setOf_eq] at h
    change j.1.val - 1 + 1 = j.1.val
    omega

theorem det_cartanBlock_e6Nodes [Fintype ↥(e6Nodes Tag.E8)] [DecidableEq ↥(e6Nodes Tag.E8)] :
    (cartanBlock Tag.E8 (e6Nodes Tag.E8)).det = 3 := by
  classical
  have hsub : (cartanBlock Tag.E8 (e6Nodes Tag.E8)).submatrix e6NodesEquiv e6NodesEquiv
      = Tag.E6.cartan := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← Matrix.det_submatrix_equiv_self e6NodesEquiv
    (cartanBlock Tag.E8 (e6Nodes Tag.E8)), hsub]
  exact det_cartan_E6

theorem det_cartanBlock_d4Nodes [Fintype ↥(d4Nodes Tag.E8)] [DecidableEq ↥(d4Nodes Tag.E8)] :
    (cartanBlock Tag.E8 (d4Nodes Tag.E8)).det = 4 := by
  classical
  have hsub : (cartanBlock Tag.E8 (d4Nodes Tag.E8)).submatrix d4NodesEquiv d4NodesEquiv
      = Tag.D4.cartan := by
    ext i j
    fin_cases i <;> fin_cases j <;> decide
  rw [← Matrix.det_submatrix_equiv_self d4NodesEquiv
    (cartanBlock Tag.E8 (d4Nodes Tag.E8)), hsub]
  exact det_cartan_D4

theorem card_e6Nodes [Fintype ↥(e6Nodes Tag.E8)] : Fintype.card ↥(e6Nodes Tag.E8) = 6 :=
  (Fintype.card_congr e6NodesEquiv).symm.trans (Fintype.card_fin 6)

theorem card_d4Nodes [Fintype ↥(d4Nodes Tag.E8)] : Fintype.card ↥(d4Nodes Tag.E8) = 4 :=
  (Fintype.card_congr d4NodesEquiv).symm.trans (Fintype.card_fin 4)

end E8

end CFSG.StandardType
