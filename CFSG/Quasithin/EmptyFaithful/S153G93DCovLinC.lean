module

public import CFSG.Quasithin.EmptyFaithful.S153G93DCovLinA
public import CFSG.RankThree.SubgroupLists.SymplecticHeisenberg
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9Eighteen
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.G2Omega4PlusQuot
public import CFSG.Quasithin.Background.G2Relaxed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S153Baum
public import CFSG.Quasithin.EmptyFaithful.S153E58In
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin

namespace S153G93D

namespace CovLin

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists

section Elements

variable {K : Type} [Field K]

@[expose] def sp4OrderThreeMat (K : Type) [Field K] :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks !![1, 0; 0, 0] !![0, 0; 0, 1] !![0, 0; 0, 1] 1

theorem sp4OrderThreeMat_cube [CharP K 2] :
    sp4OrderThreeMat K * sp4OrderThreeMat K * sp4OrderThreeMat K = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [sp4OrderThreeMat, fromBlocks_multiply, fromBlocks_multiply, ← fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination h2

theorem sp4OrderThreeMat_symplectic [CharP K 2] :
    (sp4OrderThreeMat K)ᵀ * fromBlocks 0 1 (-1) 0 * sp4OrderThreeMat K =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) K) 1 (-1) 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [sp4OrderThreeMat, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h2 | linear_combination (-1 : K) * h2

theorem sp4OrderThreeMat_mulVec_spE : sp4OrderThreeMat K *ᵥ (spE : Fin 2 ⊕ Fin 2 → K) = spE := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [sp4OrderThreeMat, spE, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem sp4OrderThreeMat_ne_one : sp4OrderThreeMat K ≠ 1 := by
  intro h
  have h11 := congrFun (congrFun h (Sum.inl 1)) (Sum.inl 1)
  simp [sp4OrderThreeMat] at h11

theorem exists_sp4_order_three_fixing_basis [CharP K 2] :
    ∃ γ ∈ StatedSp 2 K, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
      ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        *ᵥ (spE : Fin 2 ⊕ Fin 2 → K) = spE := by
  have hc := sp4OrderThreeMat_cube (K := K)
  let γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K :=
    ⟨sp4OrderThreeMat K, sp4OrderThreeMat K * sp4OrderThreeMat K,
      by rw [← Matrix.mul_assoc]; exact hc, hc⟩
  have hγ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = sp4OrderThreeMat K := rfl
  refine ⟨γ, Subgroup.subset_closure ?_, ?_, ?_, ?_⟩
  · show (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * fromBlocks 0 1 (-1) 0 *
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 0 1 (-1) 0
    rw [hγ]
    exact sp4OrderThreeMat_symplectic
  · refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hγ, pow_three', Units.val_one]
    exact hc
  · intro h
    exact sp4OrderThreeMat_ne_one (by rw [← hγ, h, Units.val_one])
  · rw [hγ]
    exact sp4OrderThreeMat_mulVec_spE

end Elements

theorem exists_sp4_order_three_fixing {K : Type} [Field K] [CharP K 2] {v : Fin 2 ⊕ Fin 2 → K}
    (hv : v ≠ 0) : ∃ γ ∈ StatedSp 2 K, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
      ((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        *ᵥ v = v := by
  obtain ⟨γ₀, hγ₀, h3, h1, hfix⟩ := exists_sp4_order_three_fixing_basis (K := K)
  have hspE : (spE : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h0 => by
    simpa [spE] using congrFun h0 (Sum.inl 0)
  obtain ⟨h, hh, hhe⟩ := exists_mem_statedSp_mulVec_eq (K := K) hspE hv
  exact exists_order_three_fixing_of_conj (c := 1) one_ne_zero hγ₀ hh h3 h1 hfix
    (by rw [one_smul]; exact hhe)

end CovLin

end S153G93D

end CFSG.Quasithin
