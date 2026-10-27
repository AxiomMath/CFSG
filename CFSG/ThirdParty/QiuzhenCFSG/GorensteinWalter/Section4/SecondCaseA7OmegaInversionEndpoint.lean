module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaInvertedElements
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1

namespace CFSG
end CFSG
open CFSG

/-! # The inversion endpoint of the A7 omega argument -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the inversion branch of the A7 omega trichotomy, the fixed subgroup
and the Fitting subgroup generate `U`. -/
public theorem secondCase_a7_omega_inversion_eq
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hFnotleQ : ¬ od.F ≤ od.Q.map c.FU.subtype)
    (hinvQ : ∀ x : G, x ∈ od.Q.map c.FU.subtype →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) :
    c.U = od.B ⊔ c.FU := by
  let s : G := od.s
  have hsI : IsInvolution s := od.s_involution
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hcopU : Nat.Coprime 2 (Nat.card c.U) :=
    Nat.coprime_two_left.mpr hUodd
  have hsU : ∀ x : G, x ∈ c.U → s * x * s⁻¹ ∈ c.U :=
    (centralizerSetup_U_isNormalIn_H c).2 s od.s_mem_H
  obtain ⟨I, _hIdef, hIeq, _hInormal, hIleFU⟩ :=
    secondCase_a7_omega_invertedElements_le_fitting
      c w d od hFnotleQ hinvQ
  have hInvLeFU : ∀ x : G, x ∈ invertedElements c.U s → x ∈ c.FU := by
    intro x hx
    apply hIleFU
    change x ∈ (I : Set G)
    rw [hIeq]
    simpa [s] using hx
  apply le_antisymm
  · intro x hxU
    obtain ⟨b, hb, i, hi, hxi⟩ :=
      fact_1_5_ii_decomposition (X := c.U) hsI hcopU hsU x hxU
    have hbB : b ∈ od.B := by
      rw [od.B_fixed]
      simpa [s] using hb
    rw [hxi]
    exact (od.B ⊔ c.FU).mul_mem
      (Subgroup.mem_sup_left hbB)
      (Subgroup.mem_sup_right (hInvLeFU i hi))
  · exact sup_le
      (od.B_fixed.trans_le inf_le_left)
      (fittingSubgroupOf_le c.U)

end CFSG.GorensteinWalter
