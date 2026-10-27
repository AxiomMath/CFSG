
module

public import CFSG.LargeExtraspecial.AS35QCoSp6Spec
import CFSG.Certificates.Kernel.C21205.CritSound
import CFSG.Certificates.Kernel.C21205.ProdSound
import Certificates.Kernel.C21205.SylowCheck
import Certificates.Kernel.C21205.CritCheck0
import Certificates.Kernel.C21205.CritCheck1
import Certificates.Kernel.C21205.ProdCheck
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LargeExtraspecial.OfFStar
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18

@[expose] public section

namespace Certificates

open CFSG.KC.C21205 CFSG.KD.C21205C CFSG.LargeExtraspecial.AS35QCo
  CFSG.LargeExtraspecial.AS35QCo.Native

theorem c21205_false_of_small_rep {k : ℕ} (hk : k = 0 ∨ k = 1) {ρ : CFSG.Sporadic.Co2Smith.Sp62}
    (hρ : Rep (repc k) ρ) {y : CFSG.Sporadic.Co2Smith.Sp62}
    (hy : y ∈ Subgroup.centralizer ({ρ} : Set CFSG.Sporadic.Co2Smith.Sp62)) (hy1 : y ≠ 1)
    (hyρ : y ≠ ρ)
    (hsmall : ((fun h : CFSG.Sporadic.Co2Smith.Sp62 => h * y * h⁻¹) ''
      (Subgroup.centralizer ({ρ} : Set CFSG.Sporadic.Co2Smith.Sp62) :
        Set CFSG.Sporadic.Co2Smith.Sp62)).ncard ≤ 6)
    {h₀ : CFSG.Sporadic.Co2Smith.Sp62}
    (hh₀ : h₀ ∈ Subgroup.centralizer ({ρ} : Set CFSG.Sporadic.Co2Smith.Sp62))
    (hconj : h₀ * y * h₀⁻¹ = ρ * y) : False := by
  rcases hk with rfl | rfl
  · have hS : S0 = [] := List.eq_nil_of_length_eq_zero (Nat.eq_of_beq_eq_true ch21205k0_s)
    have hsc : ∀ L ∈ D0, scanK (repc 0) S0 L = true := by
      rw [hS]
      exact fun L _ => scanK_nil _ L
    exact false_of_small_of_critK ch21205k0_crit
      (forall_mem_of_chunkAt (f := chunkK (repc 0) nA0 A0 B0 F0 W0 S0) ch21205k0_len
        fun i hi => ch21205k0_all i hi)
      hsc hρ hy hy1 hyρ hsmall hh₀ hconj
  · exact false_of_small_of_critK ch21205k1_crit
      (forall_mem_of_chunkAt (f := chunkK (repc 1) nA1 A1 B1 F1 W1 S1) ch21205k1_len
        fun i hi => ch21205k1_all i hi)
      (forall_mem_of_chunkAt (f := scanK (repc 1) S1) ch21205k1_len
        fun i hi => ch21205s1_all i hi)
      hρ hy hy1 hyρ hsmall hh₀ hconj

end Certificates
