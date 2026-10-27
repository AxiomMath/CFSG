module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Glue4TorusReduction
import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

section Model

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K] [Finite K]

private theorem g4sz_relIndex (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiU a K).relIndex (suzukiB a K) = 2 ^ (2 * a + 1) - 1 := by
  have h := (suzukiU a K).relIndex_mul_card (K := suzukiB a K)
  rw [inf_of_le_left (suzukiU_le_suzukiB a K), (suzuki_unipotent_structure hK).2.1,
    (suzuki_borel_structure hK).2.2.2.2.2.2.2] at h
  have h' : (suzukiU a K).relIndex (suzukiB a K) * (2 ^ (2 * a + 1)) ^ 2 =
      (2 ^ (2 * a + 1) - 1) * (2 ^ (2 * a + 1)) ^ 2 := by
    rw [h, mul_comm]
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h'

private theorem g4sz_pow_mem (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : suzukiGroup a K}
    (hx : x ∈ suzukiB a K) : x ^ (2 ^ (2 * a + 1) - 1) ∈ suzukiU a K := by
  haveI : ((suzukiU a K).subgroupOf (suzukiB a K)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (suzukiU_le_suzukiB a K)).mpr
      (uc22pwr1_sz_normalizer hK).ge
  have h := Subgroup.pow_index_mem ((suzukiU a K).subgroupOf (suzukiB a K))
    (⟨x, hx⟩ : suzukiB a K)
  have hi : ((suzukiU a K).subgroupOf (suzukiB a K)).index = 2 ^ (2 * a + 1) - 1 :=
    g4sz_relIndex hK
  rw [hi, mem_subgroupOf, SubgroupClass.coe_pow] at h
  exact h

private theorem g4sz_torus_equiv (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nonempty (suzukiT a K ≃* Multiplicative (ZMod (2 ^ (2 * a + 1) - 1))) := by
  have hcard : Nat.card (suzukiT a K) = 2 ^ (2 * a + 1) - 1 := (suzuki_borel_structure hK).2.2.1
  have e := (zmodCyclicMulEquiv (uc22pwr1_sz_isCyclic_T (a := a) (K := K))).symm
  rw [hcard] at e
  exact ⟨e⟩

private theorem g4sz_isSylowOf [Finite (suzukiGroup a K)] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.ABGLocalTools.IsSylowOf 2 (suzukiU a K) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_top, CFSG.LieType.SteinbergBR.isPGroup_suzukiU hK,
    ?_⟩
  rw [relIndex_top_right]
  exact CFSG.LieType.SteinbergBR.not_two_dvd_index_suzukiU hK

private theorem g4sz_cartanAt (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CartanAt (suzukiU a K) (2 * a + 1) (Multiplicative (ZMod (2 ^ (2 * a + 1) - 1))) := by
  refine ⟨suzukiT a K, suzukiWElt a K, (suzuki_borel_structure hK).2.2.2.1,
    g4sz_torus_equiv hK, ?_, ?_, ?_⟩
  · intro x hx
    rw [uc22pwr1_sz_normalizer hK] at hx
    refine iff_of_true (g4sz_pow_mem hK hx) ?_
    rw [sup_comm]
    exact hx
  · have h2 : suzukiWElt a K ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact suzukiWElt_mul_self
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2)
    exact ⟨k, hk⟩
  · intro d hd
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hd
    rw [suzukiWElt_inv, suzukiWElt_D_W hK, suzukiDElt_inv]

end Model

theorem cartanAt_of_isSz {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : IsSz Y n) :
    ∃ U : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
      CartanAt U n (Multiplicative (ZMod (2 ^ n - 1))) := by
  obtain ⟨-, -, a, -, K, _, _, hn, hcard, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.suzukiModel h
  subst hn
  haveI : Finite (CFSG.Blueprint.suzukiGroup a K) := Finite.of_equiv Y e.toEquiv
  exact ⟨_, isSylowOf_map_equiv (g4sz_isSylowOf hcard) e.symm, (g4sz_cartanAt hcard).map e.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
