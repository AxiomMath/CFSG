module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingFixedNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Two-subgroups centralizing the fitting intersection

This is the branch-independent equation-(7) transfer: a two-subgroup of
`H ∩ M` centralizing `F(U) ∩ M` centralizes first `F(U)` and then all of
`U`.  The proof only needs the nontrivial normal fixed factor whose normalizer
is `M`; it is shared by the alternating and linear branches.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A two-subgroup of `H ∩ M` centralizing `F(U) ∩ M` centralizes `U`. -/
public theorem secondCase_twoSubgroup_centralizes_U_of_centralizes_fitting_inter
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (F : Subgroup G)
    (hFnormalM : IsNormalIn F w.M)
    (hFne : F ≠ ⊥)
    (hFleY : F ≤ c.FU ⊓ w.M)
    (P : Subgroup G) (hPp : IsPGroup 2 P)
    (hPleC : P ≤ c.H ⊓ w.M)
    (hPcentY : P ≤ Subgroup.centralizer
      ((c.FU ⊓ w.M : Subgroup G) : Set G)) :
    P ≤ Subgroup.centralizer (c.U : Set G) := by
  classical
  let Y : Subgroup G := c.FU ⊓ w.M
  have hUleH : c.U ≤ c.H :=
    Subgroup.map_subtype_le (pPrimeCore 2 c.H)
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
  have hFUnormalH : IsNormalIn c.FU c.H := by
    change IsNormalIn ((fittingSubgroup c.U).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup c.U) (hKchar := by infer_instance)
      (hHnormal := hUnormalH)
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hPnormFU : P ≤ Subgroup.normalizer (c.FU : Set G) :=
    hPleC.trans (inf_le_left.trans (le_normalizer_of_isNormalIn hFUnormalH))
  let : P.Normalizes c.FU := ⟨hPnormFU⟩
  let : MulDistribMulAction P c.FU :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer P c.FU hPnormFU
  have hfixEq : fixedPointSubgroup P c.FU =
      (subgroupCentralizerIn c.FU P).subgroupOf c.FU :=
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
      c.FU P hPnormFU
  have hYcentP : Y ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff.mp hPcentY
  have hcentralizerFix :
      Subgroup.centralizer (fixedPointSubgroup P c.FU : Set c.FU) ≤
        fixedPointSubgroup P c.FU := by
    rw [hfixEq]
    intro x hx
    have hxCentF : (x : G) ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      let fFU : c.FU := ⟨f, hFleY hf |>.1⟩
      have hfC : f ∈ subgroupCentralizerIn c.FU P :=
        ⟨hFleY hf |>.1, hYcentP (hFleY hf)⟩
      have hfFix : fFU ∈
          (subgroupCentralizerIn c.FU P).subgroupOf c.FU :=
        Subgroup.mem_subgroupOf.mpr hfC
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx) fFU hfFix
      exact congrArg Subtype.val hcomm
    have hxM : (x : G) ∈ w.M := by
      have hxN := Subgroup.centralizer_le_normalizer (F : Set G) hxCentF
      rw [hNFeq] at hxN
      exact hxN
    have hxY : (x : G) ∈ Y := ⟨x.2, hxM⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hYcentP hxY⟩
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hFUodd : Odd (Nat.card c.FU) :=
    Odd.of_dvd_nat hUodd
      (Subgroup.card_dvd_of_le (fittingSubgroupOf_le c.U))
  have hPFUcop : Nat.Coprime (Nat.card P) (Nat.card c.FU) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hFUodd.coprime_two_left.pow_left n
  have htriv : ActsTrivially (A := P) (G := c.FU) :=
    actsTrivially_of_nilpotent_coprime_and_centralizer_fixedPointSubgroup
      (fittingSubgroupOf_isNilpotent c.U) hPFUcop hcentralizerFix
  have hPcentFU : P ≤ Subgroup.centralizer (c.FU : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    let pP : P := ⟨p, hp⟩
    let fFU : c.FU := ⟨f, hf⟩
    have hfix : pP • fFU = fFU := htriv pP fFU
    have hconj : p * f * p⁻¹ = f := by
      simpa [pP, fFU,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        hPnormFU] using congrArg Subtype.val hfix
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  have hPleH : P ≤ c.H := hPleC.trans inf_le_left
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
  have hUsolv : IsSolvable c.U := odd_order_theorem c.U hUodd
  have hself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU := by
    change c.U ⊓ Subgroup.centralizer
        (((fittingSubgroup c.U).map c.U.subtype : Subgroup G) : Set G) ≤
      (fittingSubgroup c.U).map c.U.subtype
    exact fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hcop : Nat.Coprime (Nat.card P) (Nat.card c.U) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hUodd.coprime_two_left.pow_left n
  exact centralizes_of_normal_selfCentralizing_coprime
    P c.U c.FU hPnormU hFUleU hFUnormalSub hPcentFU hself hcop hUsolv

end CFSG.GorensteinWalter
