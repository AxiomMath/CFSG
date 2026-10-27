module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationSix
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(7) two-core centralizes the Fitting subgroup

Write `C = H \inter M`, `P = O2(C)`, and `Y = F(U) \inter M`.  The normal
subgroups `P` and `Y` have coprime orders, so `P` centralizes `Y`.  The fixed
subgroup of the resulting coprime action on `F(U)` is self-centralizing:
anything centralizing it centralizes the equation-(6) subgroup `F`, hence
lies in `N_G(F) = M` and therefore in `Y`.  Proposition 1.10 then makes the
action on all of `F(U)` trivial.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The two-core of `H \inter M` centralizes `F(U)` in the A7 branch. -/
public theorem secondCase_a7_twoCore_inter_centralizes_fitting
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    twoCoreOf (c.H ⊓ w.M) ≤ Subgroup.centralizer (c.FU : Set G) := by
  classical
  obtain ⟨K, B, s, _hsI, _hsH, hK_eq, hK_cyc, hB_def, hjoinX, hKcard,
      _hKleE,
      K0, F, hK0_def, hF_def, hF_eq, hjoinY, hFnormalM,
      hFcentE, hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  let C : Subgroup G := c.H ⊓ w.M
  let P : Subgroup G := twoCoreOf C
  let Y : Subgroup G := c.FU ⊓ w.M
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
  have hFUnormalH : IsNormalIn c.FU c.H := by
    change IsNormalIn ((fittingSubgroup (c.U)).map c.U.subtype) c.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := fittingSubgroup c.U) (hKchar := by infer_instance)
      (hHnormal := hUnormalH)
  have hYleC : Y ≤ C := by
    intro y hy
    exact ⟨hUleH (fittingSubgroupOf_le c.U hy.1), hy.2⟩
  have hYnormalC : IsNormalIn Y C := by
    refine ⟨hYleC, ?_⟩
    intro z hz y hy
    refine ⟨hFUnormalH.2 z hz.1 y hy.1, ?_⟩
    exact w.M.mul_mem (w.M.mul_mem hz.2 hy.2) (w.M.inv_mem hz.2)
  have hPleC : P ≤ C := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xC, hxC, rfl⟩
    exact xC.2
  have hPnormalC : IsNormalIn P C := by
    refine ⟨hPleC, ?_⟩
    intro z hz x hx
    rcases Subgroup.mem_map.mp hx with ⟨xC, hxP, rfl⟩
    refine Subgroup.mem_map.mpr
      ⟨(⟨z, hz⟩ : C) * xC * (⟨z, hz⟩ : C)⁻¹, ?_, by simp⟩
    exact (pCore_normal (p := 2) (G := C)).conj_mem
      xC hxP (⟨z, hz⟩ : C)
  have hPp : IsPGroup 2 P := by
    change IsPGroup 2 ((pCore 2 C).map C.subtype)
    exact (pCore_isPGroup (p := 2) (G := C)).map C.subtype
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hYleU : Y ≤ c.U := by
    intro y hy
    exact fittingSubgroupOf_le c.U hy.1
  have hYodd : Odd (Nat.card Y) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hYleU)
  have hPYcop : Nat.Coprime (Nat.card P) (Nat.card Y) := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact hYodd.coprime_two_left.pow_left n
  let PC : Subgroup C := P.subgroupOf C
  let YC : Subgroup C := Y.subgroupOf C
  have hPCnormal : PC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPleC]
    intro p z hp hz
    exact hPnormalC.2 z hz p hp
  have hYCnormal : YC.Normal := by
    rw [Subgroup.normal_subgroupOf_iff hYleC]
    intro y z hy hz
    exact hYnormalC.2 z hz y hy
  let : PC.Normal := hPCnormal
  let : YC.Normal := hYCnormal
  have hPCcard : Nat.card PC = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleC).toEquiv
  have hYCcard : Nat.card YC = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYleC).toEquiv
  have hPCYCcop : Nat.Coprime (Nat.card PC) (Nat.card YC) := by
    simpa [hPCcard, hYCcard] using hPYcop
  have hPCYCdisj : Disjoint PC YC :=
    Subgroup.disjoint_of_coprime_natCard hPCYCcop
  have hcommbot : ⁅PC, YC⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_le_inf PC YC).trans
      (by rw [hPCYCdisj.eq_bot])
  have hPcentY : P ≤ Subgroup.centralizer (Y : Set G) := by
    have hPCcentYC : PC ≤ Subgroup.centralizer (YC : Set C) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcommbot
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let pC : C := ⟨p, hPleC hp⟩
    let yC : C := ⟨y, hYleC hy⟩
    have hpPC : pC ∈ PC := Subgroup.mem_subgroupOf.mpr hp
    have hyYC : yC ∈ YC := Subgroup.mem_subgroupOf.mpr hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hPCcentYC hpPC)) yC hyYC
    exact congrArg Subtype.val hcomm
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card F = 1 := by rw [hbot]; simp
    omega
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
  have hFleY : F ≤ Y := by
    change F ≤ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoinY]
    exact le_sup_right
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
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  let pP : P := ⟨p, hp⟩
  let fFU : c.FU := ⟨f, hf⟩
  have hfix : pP • fFU = fFU := htriv pP fFU
  have hconj : p * f * p⁻¹ = f := by
    simpa [pP, fFU,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hPnormFU] using
      congrArg Subtype.val hfix
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

end CFSG.GorensteinWalter
