module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearIndexParameters
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaEqualityIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Oddness of the relative line index
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The relative index `p₀` is odd because it divides the order of the odd
subgroup `U`. -/
public theorem secondCase_linear_p0_odd
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (p0 : ℕ) (hp0 : p0 =
      (normalizerIn c.U od.P).relIndex (normalizerIn c.U od.A)) :
    Odd p0 := by
  classical
  have hNPleNA := secondCase_linear_omega_NU_P_le_NU_A c w d od
  have hNAleU : normalizerIn c.U od.A ≤ c.U := inf_le_left
  have hp0div : p0 ∣ (normalizerIn c.U od.P).relIndex c.U := by
    rw [hp0]
    refine ⟨(normalizerIn c.U od.A).relIndex c.U, ?_⟩
    exact (Subgroup.relIndex_mul_relIndex
      (normalizerIn c.U od.P) (normalizerIn c.U od.A) c.U
      hNPleNA hNAleU).symm
  have hNPindex : (normalizerIn c.U od.P).relIndex c.U ∣ Nat.card (↥c.U) := by
    refine ⟨Nat.card (normalizerIn c.U od.P), ?_⟩
    let N : Subgroup (↥c.U) := (normalizerIn c.U od.P).subgroupOf c.U
    have hNcard : Nat.card N = Nat.card (normalizerIn c.U od.P) := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hmul := Subgroup.card_mul_index N
    change Nat.card (↥c.U) =
      (normalizerIn c.U od.P).relIndex c.U * Nat.card (normalizerIn c.U od.P)
    simpa [N, Subgroup.relIndex, hNcard, Nat.mul_comm] using hmul.symm
  have hp0U : p0 ∣ Nat.card (↥c.U) := dvd_trans hp0div hNPindex
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  exact Odd.of_dvd_nat hUodd hp0U

/-- The parameter `p₀` is at most `p` once its orbit bound is at most
`p + 1`.  The ambient normalizer is an odd-order subgroup, so the generic
odd-index lemma removes the endpoint `+ 1`. -/
public theorem secondCase_linear_p0_le_p_of_le_add_one
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (p0 : ℕ)
    (hp0 : p0 =
      (normalizerIn c.U od.P).relIndex (normalizerIn c.U od.A))
    (hp0le : p0 ≤ od.p + 1) :
    p0 ≤ od.p := by
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hNAodd : Odd (Nat.card (normalizerIn c.U od.A)) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hindex := odd_relIndex_le_of_le_add_one
    (normalizerIn c.U od.P) (normalizerIn c.U od.A) hNAodd
    (secondCase_linear_omega_p_odd c w d od)
    (by simpa [hp0] using hp0le)
  simpa [hp0] using hindex

end CFSG.GorensteinWalter
