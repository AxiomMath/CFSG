module

public import CFSG.RankThree.PartOne.KGD.D4T36Plane
public import CFSG.RankThree.PartOne.KE.Statements
public import CFSG.RankThree.PartOne.KE.FamilyArith
public import CFSG.RankThree.PartOne.S8.CatalogAssembly
public import CFSG.RankThree.Chevalley.SteinbergBLTrialitySplitInnerComponent
public import CFSG.RankThree.Chevalley.SteinbergBLTrialityNoninnerComponent
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityTwelveComponent
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityDefiningComponent
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion
public import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.RankThree.CentralCover.SteinbergBNSL2InversionBasis
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.KGD

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ChevalleyExceptionalModel)
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial

theorem triality_family : OriginalTrialityComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL ℓ f hℓ hf hmod hpT hEL hSL
  have hrank : localRank p X ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp (by omega)).trans hX
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact triality_D4_defining_prime_actual_component_exclusion hp hp3 N hN hrank L f hmod
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨hrow, -, -⟩ := exact_E_type_and_triality_cross_prime_factor_exhaustion hp hp3 hℓp hmod
  obtain ⟨m, hm, hdvd⟩ := (hrow hpT).2.2.2.2 rfl
  have hd : (p : ℤ) ∣ cycloVal m ℓ f := hdvd
  have hnon : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : L ⧸ Subgroup.center L →* MulAut (L ⧸ Subgroup.center L)).range →
      ComponentLocalCoreOddConclusion p E t L := fun hnon => by
    obtain ⟨hset, hle⟩ := triality_noninner_actual_component_local_core_product_centralizes hp hp3
      hE hEc ht ht1 hL hℓ hf hmod hEL hSL hnon
    exact componentLocalCoreOddConclusion_of_le_centralizer hset hle
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  ·
    have hpq : p ∣ ℓ ^ f - 1 := by
      rw [cycloVal_one] at hd
      have h1 : (p : ℤ) ∣ ((ℓ ^ f - 1 : ℕ) : ℤ) := by rw [Nat.cast_sub hq1]; exact hd
      exact_mod_cast h1
    by_cases hinn : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∈
        (MulAut.conj : L ⧸ Subgroup.center L →* MulAut (L ⧸ Subgroup.center L)).range
    · exact (triality_split_prime_inner_actor_actual_component_odd_action hp hp3 hE hEc ht ht1 hL
        hℓ hf hpq hmod hEL hSL).1 hinn
    · exact hnon hinn
  ·
    rw [cycloVal_two] at hd
    exact (triality_qplus_component hp hp3 hE hEc ht ht1 hL hℓ hf hd hmod hEL hSL).1
  ·
    rw [cycloVal_three] at hd
    exact (triality_36_component hp hp3 hE hEc ht ht1 hL hℓ hf (ε := 1) (Or.inl rfl)
      (by simpa using hd) hmod hEL hSL).1
  ·
    rw [cycloVal_six] at hd
    exact (triality_36_component hp hp3 hE hEc ht ht1 hL hℓ hf (ε := -1) (Or.inr rfl)
      (by simpa [sub_eq_add_neg] using hd) hmod hEL hSL).1
  ·
    rw [cycloVal_twelve] at hd
    have hpd : p ∣ (ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 := by
      have h24 : (ℓ ^ f) ^ 2 ≤ (ℓ ^ f) ^ 4 := Nat.pow_le_pow_right hq1 (by omega)
      have h1 : (p : ℤ) ∣ (((ℓ ^ f) ^ 4 - (ℓ ^ f) ^ 2 + 1 : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub h24]
        push_cast
        exact hd
      exact_mod_cast h1
    obtain ⟨hset, hWN, hodd, -⟩ := triality_cyclotomic_twelve_actual_component_odd_action hp hp3 hE
      hEc ht ht1 hL hℓ hf hpd hmod hEL hSL
    exact ⟨hset, hWN, hodd⟩

end CFSG.RankThree.PartOne.KGD
