module

public import CFSG.GH74.GLS.Basic
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T114B
import CFSG.RankThree.PartTwo.Sec15.Item155R2ProofMaxT
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem commutator_pCoreOf_le {p : ℕ} [Fact p.Prime] {L K : Subgroup G} (hLK : L ≤ K) :
    ⁅L, CFSG.Open.pCoreOf p K⁆ ≤ CFSG.Open.pCoreOf p K := by
  rw [Subgroup.commutator_le]
  intro l hl v hv
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p K (hLK hl)) v).mp hv)
    (Subgroup.inv_mem _ hv)

theorem eq_sup_commutator_of_eq_sup {L K : Subgroup G}
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) (hK3 : oPrimeResidualOf 3 K = K) :
    K = L ⊔ ⁅L, CFSG.Open.pCoreOf 2 K⁆ := by
  set V := CFSG.Open.pCoreOf 2 K with hV
  have hLK : L ≤ K := le_sup_left.trans hKL.ge
  have hVK : V ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  refine le_antisymm ?_ (sup_le hLK ?_)
  · calc K = oPrimeResidualOf 3 K := hK3.symm
      _ = oPrimeResidualOf 3 (L ⊔ V) := congrArg (oPrimeResidualOf 3) hKL
      _ ≤ L ⊔ ⁅L, V⁆ :=
        Sec15.Proof155R2.oPrimeResidualOf_sup_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (commutator_pCoreOf_le hLK).trans hVK

theorem inf_pCoreOf_two_eq_of_eq_sup {L K : Subgroup G}
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) :
    L ⊓ CFSG.Open.pCoreOf 2 K = CFSG.Open.pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact inf_pCoreOf_eq_pCoreOf_of_le_sup (le_sup_left.trans hKL.ge) hKL.le

theorem pCoreOf_two_eq_commutator_sup {L K : Subgroup G}
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) (hK3 : oPrimeResidualOf 3 K = K) :
    CFSG.Open.pCoreOf 2 K = ⁅L, CFSG.Open.pCoreOf 2 K⁆ ⊔ CFSG.Open.pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := CFSG.Open.pCoreOf 2 K with hV
  have hLK : L ≤ K := le_sup_left.trans hKL.ge
  have hcV : ⁅L, V⁆ ≤ V := commutator_pCoreOf_le hLK
  refine le_antisymm (fun v hv => ?_)
    (sup_le hcV (pCoreOf_le_pCoreOf_of_le_sup hLK hKL.le))
  have hvK : v ∈ L ⊔ ⁅L, V⁆ := by
    rw [← eq_sup_commutator_of_eq_sup hKL hK3]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 K hv
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right L _
    (Subgroup.normalizer_commutator_ge_left L V)] at hvK
  obtain ⟨l, hl, w, hw, rfl⟩ := hvK
  have hlV : l ∈ V := by
    have h := V.mul_mem hv (V.inv_mem (hcV hw))
    rwa [mul_inv_cancel_right] at h
  have hlU : l ∈ CFSG.Open.pCoreOf 2 L := by
    rw [← inf_pCoreOf_two_eq_of_eq_sup hKL]
    exact ⟨hl, hlV⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlU) (Subgroup.mem_sup_left hw)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
