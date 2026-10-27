module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7AmbientModel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvolutionCentralizerOddPart
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the odd intersection in the A₇ quotient

The image of `U ∩ M` in `M / O₂′(M)` is an odd-order subgroup centralizing
the distinguished involution.  In the A₇ model its order is therefore at
most three.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_a7_u_inter_m_quotient_card_le_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    Nat.card (((c.U ⊓ w.M).subgroupOf w.M).map
      (QuotientGroup.mk' (pPrimeCore 2 w.M))) ≤ 3 := by
  classical
  let M : Subgroup G := w.M
  let O : Subgroup M := pPrimeCore 2 M
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  let Y : Subgroup M := (c.U ⊓ M).subgroupOf M
  let Ybar : Subgroup (M ⧸ O) := Y.map q
  have hOodd : Odd (Nat.card O) := by
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := M))
  have hUodd : Odd (Nat.card (↥c.U)) := by
    change Odd (Nat.card (↥(oddCoreOf c.H)))
    exact odd_card_oddCoreOf c.H
  have hYcard : Nat.card Y = Nat.card (↥(c.U ⊓ M)) := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := c.U ⊓ M) (K := M) inf_le_right).toEquiv
  have hYodd : Odd (Nat.card Y) := by
    rw [hYcard]
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hYbarodd : Odd (Nat.card Ybar) :=
    Odd.of_dvd_nat hYodd (Subgroup.card_map_dvd Y q)
  have htM : c.t ∈ M :=
    (componentLayerOf_isNormalIn M).1 w.t_mem_componentLayer
  let tM : M := ⟨c.t, htM⟩
  have htM_i : IsInvolution tM := by
    constructor
    · intro h
      exact c.t_involution.1 (by simpa [tM] using congrArg Subtype.val h)
    · exact Subtype.ext c.t_involution.2
  have hqt_i : IsInvolution (q tM) := by
    constructor
    · intro hq
      have htO : tM ∈ O := (QuotientGroup.eq_one_iff (N := O) tM).mp hq
      have h2dvd : 2 ∣ Nat.card O := by
        rw [← orderOf_eq_prime htM_i.2 htM_i.1]
        exact Subgroup.orderOf_dvd_natCard O htO
      exact hOodd.not_two_dvd_nat h2dvd
    · simpa [map_pow] using congrArg q htM_i.2
  have hUleH : c.U ≤ c.H := by
    unfold CentralizerSetup.U oddCoreOf
    exact Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hYbarcent : Ybar ≤ Subgroup.centralizer ({q tM} : Set (M ⧸ O)) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hyY : (y0 : G) ∈ c.U :=
      (Subgroup.mem_subgroupOf.mp hy0).1
    have hyH : (y0 : G) ∈ c.H := hUleH hyY
    have hycent : (y0 : G) * c.t = c.t * (y0 : G) := by
      rw [c.H_eq_centralizer] at hyH
      exact Subgroup.mem_centralizer_singleton_iff.mp hyH
    have hycomm : y0 * tM = tM * y0 := Subtype.ext hycent
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa using congrArg q hycomm
  have hAmbient := secondCase_a7_ambient_quotient_model hmin c w d hA7 hmodel
  let eQ : (M ⧸ O) ≃* alternatingGroup (Fin 7) := hAmbient.some
  let Y7 : Subgroup (alternatingGroup (Fin 7)) := Ybar.map eQ.toMonoidHom
  have hY7odd : Odd (Nat.card Y7) := by
    have hcard : Nat.card Y7 = Nat.card Ybar :=
      Subgroup.card_map_of_injective (K := Ybar) eQ.injective
    rw [hcard]
    exact hYbarodd
  let t7 := eQ (q tM)
  have ht7 : IsInvolution t7 := by
    constructor
    · intro h
      apply hqt_i.1
      apply eQ.injective
      simpa [t7] using h
    · simpa [t7, map_pow] using congrArg eQ hqt_i.2
  have hY7cent : Y7 ≤ Subgroup.centralizer ({t7} : Set (alternatingGroup (Fin 7))) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨y0, hy0, rfl⟩
    have hycomm : y0 * q tM = q tM * y0 :=
      Subgroup.mem_centralizer_singleton_iff.mp (hYbarcent hy0)
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    simpa [t7] using congrArg eQ hycomm
  have hY7le : Nat.card Y7 ≤ 3 :=
    aSeven_odd_subgroup_centralizing_involution_card_le_three
      hY7odd ht7 hY7cent
  have hcard : Nat.card Y7 = Nat.card Ybar :=
    Subgroup.card_map_of_injective (K := Ybar) eQ.injective
  have hYbarle : Nat.card Ybar ≤ 3 := by
    rw [← hcard]
    exact hY7le
  simpa [Ybar, Y, q, O, M] using hYbarle

end CFSG.GorensteinWalter
