module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7TwoCoreCentralizesFitting
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(7) two-core centralizes U

The preceding theorem gives centralization of `F(U)`.  Since `F(U)` is
normal and self-centralizing in the odd solvable group `U`, the normal-case
Fact 1.1(iv) transfer upgrades this to centralization of all of `U`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The two-core of `H \inter M` centralizes `U` in the A7 branch. -/
public theorem secondCase_a7_twoCore_inter_centralizes_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    twoCoreOf (c.H ⊓ w.M) ≤ Subgroup.centralizer (c.U : Set G) := by
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  have hPcentFU : P ≤ Subgroup.centralizer (c.FU : Set G) := by
    simpa [P, C] using
      secondCase_a7_twoCore_inter_centralizes_fitting
        hmin c w d hA7 hmodel
  have hUleH : c.U ≤ c.H := Subgroup.map_subtype_le (pPrimeCore 2 c.H)
  have hUnormalH : IsNormalIn c.U c.H := by
    refine ⟨hUleH, ?_⟩
    intro h hh x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have hconj : (⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹ ∈
        pPrimeCore 2 c.H :=
      (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
        p hp (⟨h, hh⟩ : c.H)
    exact Subgroup.mem_map.mpr
      ⟨(⟨h, hh⟩ : c.H) * p * (⟨h, hh⟩ : c.H)⁻¹, hconj, by simp⟩
  have hPleH : P ≤ c.H := by
    intro p hp
    exact (show p ∈ C from (by
      rcases Subgroup.mem_map.mp hp with ⟨pC, hpC, rfl⟩
      exact pC.2)).1
  have hPnormU : P ≤ Subgroup.normalizer (c.U : Set G) :=
    hPleH.trans (le_normalizer_of_isNormalIn hUnormalH)
  have hFUleU : c.FU ≤ c.U := fittingSubgroupOf_le c.U
  have hFUnormalU : IsNormalIn c.FU c.U := by
    change IsNormalIn ((fittingSubgroup c.U).map c.U.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup c.U) (hKchar := by infer_instance)
      (hHnormal := ⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩)
  have hFUnormalSub : (c.FU.subgroupOf c.U).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (H := c.U) (N := c.FU) (le_normalizer_of_isNormalIn hFUnormalU)
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hUsolv : IsSolvable c.U := odd_order_theorem c.U hUodd
  have hself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU := by
    change c.U ⊓ Subgroup.centralizer
        (((fittingSubgroup c.U).map c.U.subtype : Subgroup G) : Set G) ≤
      (fittingSubgroup c.U).map c.U.subtype
    exact fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hcop : Nat.Coprime (Nat.card P) (Nat.card c.U) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hUodd.coprime_two_left.pow_left n
  exact centralizes_of_normal_selfCentralizing_coprime
    P c.U c.FU hPnormU hFUleU hFUnormalSub hPcentFU hself hcop hUsolv

end CFSG.GorensteinWalter
