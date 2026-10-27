module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPSL2TorusPartition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The PSL₂ orbit-count adapter for equation (11)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The split-half version of the PSL₂ torus-family orbit count. -/
public theorem secondCase_linear_psl2_split_orbit_card
    {K : Type u} [Field K] [Finite K]
    {p k k' : ℕ} [Fact p.Prime]
    (hK : IsOddPrimePower (Nat.card K)) (U : Subgroup (PSL2 K))
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hk : k = (Nat.card K - 1) / 2)
    (hk' : k' = (Nat.card K + 1) / 2)
    (hUN : Nat.card (Subgroup.normalizer (U : Set (PSL2 K))) = 2 * k)
    (hpart : ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : PSL2 K) ∈ T.1)
    (hpk : p ∣ k) :
    Nat.card {P : Subgroup (PSL2 K) // Nat.card P = p} = Nat.card K * k' := by
  classical
  have hodd : Odd (Nat.card K) := by
    rcases hK with ⟨r, f, hr, hrOdd, hf, hcard⟩
    rw [hcard]
    exact hrOdd.pow
  have h2minus : 2 ∣ Nat.card K - 1 := by
    rcases hodd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    omega
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hodd with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hminus : 2 * ((Nat.card K - 1) / 2) = Nat.card K - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel h2minus
  have hplus : 2 * ((Nat.card K + 1) / 2) = Nat.card K + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel h2plus
  have hsq : Nat.card K ^ 2 - 1 =
      (Nat.card K - 1) * (Nat.card K + 1) := by
    calc
      Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        rw [← Nat.sq_sub_sq (Nat.card K) 1]
      _ = (Nat.card K - 1) * (Nat.card K + 1) := by ac_rfl
  have hGcard : Nat.card (PSL2 K) = 2 * Nat.card K * k * k' := by
    rw [psl2_card_formula K hK]
    rw [hk, hk']
    apply Nat.div_eq_of_eq_mul_right (by norm_num)
    calc
      Nat.card K * (Nat.card K ^ 2 - 1) =
          Nat.card K * (Nat.card K - 1) * (Nat.card K + 1) := by
            rw [hsq]
            ac_rfl
      _ = Nat.card K * (2 * ((Nat.card K - 1) / 2)) *
          (2 * ((Nat.card K + 1) / 2)) := by rw [hminus, hplus]
      _ = 2 * (2 * Nat.card K * ((Nat.card K - 1) / 2) *
          ((Nat.card K + 1) / 2)) := by
            ring
  exact psl2_order_p_subgroup_card_of_unique_torus_family U hcyc hUcard hUN hpart hpk hGcard

/-- The nonsplit-half version of the PSL₂ torus-family orbit count. -/
public theorem secondCase_linear_psl2_nonsplit_orbit_card
    {K : Type u} [Field K] [Finite K]
    {p k k' : ℕ} [Fact p.Prime]
    (hK : IsOddPrimePower (Nat.card K)) (U : Subgroup (PSL2 K))
    (hcyc : IsCyclic U) (hUcard : Nat.card U = k)
    (hk : k = (Nat.card K + 1) / 2)
    (hk' : k' = (Nat.card K - 1) / 2)
    (hUN : Nat.card (Subgroup.normalizer (U : Set (PSL2 K))) = 2 * k)
    (hpart : ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = U.map (MulAut.conj g).toMonoidHom}, (x : PSL2 K) ∈ T.1)
    (hpk : p ∣ k) :
    Nat.card {P : Subgroup (PSL2 K) // Nat.card P = p} = Nat.card K * k' := by
  classical
  have hodd : Odd (Nat.card K) := by
    rcases hK with ⟨r, f, hr, hrOdd, hf, hcard⟩
    rw [hcard]
    exact hrOdd.pow
  have h2minus : 2 ∣ Nat.card K - 1 := by
    rcases hodd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    omega
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hodd with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hminus : 2 * ((Nat.card K - 1) / 2) = Nat.card K - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel h2minus
  have hplus : 2 * ((Nat.card K + 1) / 2) = Nat.card K + 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_cancel h2plus
  have hsq : Nat.card K ^ 2 - 1 =
      (Nat.card K - 1) * (Nat.card K + 1) := by
    calc
      Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
        rw [← Nat.sq_sub_sq (Nat.card K) 1]
      _ = (Nat.card K - 1) * (Nat.card K + 1) := by ac_rfl
  have hGcard : Nat.card (PSL2 K) = 2 * Nat.card K * k * k' := by
    rw [psl2_card_formula K hK]
    rw [hk, hk']
    apply Nat.div_eq_of_eq_mul_right (by norm_num)
    calc
      Nat.card K * (Nat.card K ^ 2 - 1) =
          Nat.card K * (Nat.card K - 1) * (Nat.card K + 1) := by
            rw [hsq]
            ac_rfl
      _ = Nat.card K * (2 * ((Nat.card K - 1) / 2)) *
          (2 * ((Nat.card K + 1) / 2)) := by rw [hminus, hplus]
      _ = 2 * (2 * Nat.card K * ((Nat.card K + 1) / 2) *
          ((Nat.card K - 1) / 2)) := by
            ring
  exact psl2_order_p_subgroup_card_of_unique_torus_family U hcyc hUcard hUN hpart hpk hGcard

end CFSG.GorensteinWalter
