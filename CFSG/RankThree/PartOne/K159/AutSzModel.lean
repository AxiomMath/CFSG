module

public import CFSG.RankThree.PartOne.K159.AutSzOvoid
public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LieType.BorelTits.Suzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.RankThree.PartOne.K159.SzAbs

open CFSG.LieType.Ree CFSG.Blueprint
open scoped LinearAlgebra.Projectivization

theorem szSylow_model
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * 2 + 1)) :
    SzSylow (suzukiGroup 2 K) := by
  have hcardS : Nat.card (suzukiGroup 2 K) = 32537600 := by
    rw [suzuki_order hK]
    norm_num
  have hfin : Finite (suzukiGroup 2 K) := Nat.finite_of_card_ne_zero (by rw [hcardS]; norm_num)
  obtain ⟨-, -, -, -, -, hΩ6, hΩcard'⟩ := suzuki_ovoid_unipotent_action (a := 2) (K := K) hK
  have hΩcard : (suzukiOmega 2 K).ncard = 1025 := by
    rw [hΩcard']
    norm_num
  have hUcard : Nat.card (suzukiU 2 K) = 1024 := by
    rw [(suzuki_unipotent_structure hK).2.1]
    norm_num
  have hBN : suzukiB 2 K ≤ Subgroup.normalizer (suzukiU 2 K : Set (suzukiGroup 2 K)) :=
    sup_le Subgroup.le_normalizer (suzuki_borel_structure hK).2.2.2.1
  have hstabB := (suzuki_ovoid_stabilizer (a := 2) hK).1
  obtain ⟨hdata1, hdata2⟩ := sylow_data_of_ovoid (S := suzukiGroup 2 K)
    (X := ℙ K (Fin 4 → K)) hcardS (suzukiOmega 2 K)
    (fun g x hx => suzuki_smul_mem_suzukiOmega hK g hx) (suzukiInfty K)
    (suzukiInfty_mem_suzukiOmega 2 K) (fun x hx => exists_smul_eq_suzukiInfty hK hx) hΩcard
    (suzukiU 2 K) hUcard
    (fun u hu => by
      have := suzukiB_le_stabilizer hK (suzukiU_le_suzukiB 2 K hu)
      exact MulAction.mem_stabilizer_iff.1 this)
    (fun u hu x hx hxne hux => by
      have hxΩ : x ∈ suzukiOmega 2 K \ {suzukiInfty K} := ⟨hx, hxne⟩
      obtain ⟨g, -, hg⟩ := hΩ6 x hxΩ x hxΩ
      have h2 : (⟨u, hu⟩ : suzukiU 2 K) = 1 :=
        (hg ⟨u, hu⟩ hux).trans (hg 1 (one_smul _ _)).symm
      exact congrArg Subtype.val h2)
    (fun g hg => by
      have : g ∈ MulAction.stabilizer (suzukiGroup 2 K) (suzukiInfty K) := hg
      rw [hstabB] at this
      exact hBN this)
  refine ⟨hcardS, hdata1, hdata2, ?_⟩
  intro T
  have e : suzukiGroup 2 K ≃* CFSG.Open.GLASzGroup 2 K :=
    MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 2 K)
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    2 (by norm_num) hK e 5 (by norm_num) T

end CFSG.RankThree.PartOne.K159.SzAbs
