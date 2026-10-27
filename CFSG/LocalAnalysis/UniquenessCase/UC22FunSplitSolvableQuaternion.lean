module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement
public import CFSG.ClassicalInvolution.QuaternionStructure.OddCoreQuotient
public import CFSG.ClassicalInvolution.Balance.Basic
public import CFSG.GroupTheory.PCoreOfSubnormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.QuaternionStructure

theorem isPGroup_two_of_quaternion_of_oddCore_eq_bot_of_threePrime
    {G : Type} [Group G] [Finite G]
    (hO : classicalInvolutionOddCore G = ⊥) (h3 : ¬ 3 ∣ Nat.card G)
    (S : Sylow 2 G) {k : ℕ} (hk : 1 ≤ k)
    (eS : (S : Subgroup G) ≃* QuaternionGroup (2 ^ k)) : IsPGroup 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (QuaternionGroup (2 ^ k)) :=
    S.isPGroup'.of_equiv eS
  have hcomp := CFSG.BenderSuzuki.External.huppert_IV_5_11_hasNormalPComplement_of_quaternion_sylow_two
    S ⟨2 ^ k, by
      calc 2 = 2 ^ 1 := by norm_num
           _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk,
      hQ2, ⟨eS⟩⟩ h3
  have hOp : CFSG.pPrimeCore 2 G = ⊥ := by
    rw [← oddCore_eq_pPrimeCore_two]
    exact hO
  have he := CFSG.BenderSuzuki.External.quotientPPrimeCoreEquivSylowOfHasNormalPComplement hcomp S
  exact S.isPGroup'.of_equiv
    (((QuotientGroup.quotientMulEquivOfEq hOp).trans QuotientGroup.quotientBot).symm.trans he).symm

theorem le_pCore_two_of_subnormal_quaternion_of_threePrime
    {G : Type} [Group G] [Finite G]
    (hO : classicalInvolutionOddCore G = ⊥) (h3 : ¬ 3 ∣ Nat.card G)
    {K : Subgroup G} (hK : CFSG.Open.IsSubnormal K ⊤)
    (S : Sylow 2 K) {k : ℕ} (hk : 1 ≤ k)
    (eS : (S : Subgroup K) ≃* QuaternionGroup (2 ^ k)) : K ≤ CFSG.pCore 2 G := by
  have hOK : classicalInvolutionOddCore K = ⊥ := by
    have hle := oddCoreIn_le_of_isSubnormal hK
    have htop : oddCoreIn (⊤ : Subgroup G) = ⊥ := by
      have hmap := CFSG.ComponentClassification.OddCore.equiv_invariant
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
      change (classicalInvolutionOddCore (⊤ : Subgroup G)).map
        (⊤ : Subgroup G).subtype = ⊥
      exact hmap.trans hO
    rw [htop] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp (le_bot_iff.mp hle)
  have hK2 : IsPGroup 2 K := isPGroup_two_of_quaternion_of_oddCore_eq_bot_of_threePrime
    hOK (fun hdvd => h3 (hdvd.trans (Subgroup.card_subgroup_dvd_card K))) S hk eS
  have hKcore : CFSG.Open.pCoreOf 2 K = K := by
    apply le_antisymm
    · exact CFSG.LieType.BorelTits.pCoreOf_le 2 K
    · exact CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl (by
        rw [Subgroup.subgroupOf_self]
        infer_instance) hK2
  have heq := CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hK
  have htop : CFSG.Open.pCoreOf 2 (⊤ : Subgroup G) = CFSG.pCore 2 G := by
    exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2
      (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
  rw [hKcore, htop] at heq
  exact heq ▸ inf_le_right

end CFSG.LocalAnalysis.UniquenessCase.UC22
