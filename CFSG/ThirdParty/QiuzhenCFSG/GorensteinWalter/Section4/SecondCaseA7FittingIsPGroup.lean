module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7EquationSix
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Prime support of the A7 Fitting subgroup

The order-three fixed subgroup from equation (6) controls every Sylow
subgroup of the nilpotent Fitting subgroup through its ambient normalizer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, the Fitting subgroup of `U` is a `3`-group. -/
public theorem secondCase_a7_fitting_isPGroup_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    IsPGroup 3 c.FU := by
  classical
  obtain ⟨K, _B, s, _hsI, _hsH, hK_eq, _hKcyc, _hBdef, _hjoinX,
      _hKcard, _hKleE,
      K0, F, hK0_def, _hFdef, hF_eq, hjoinY, hFnormalM,
      _hFcentE, _hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  let Y : Subgroup G := c.FU ⊓ w.M
  have hK0leY : K0 ≤ Y := by
    change K0 ≤ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoinY]
    exact le_sup_left
  have hFleY : F ≤ Y := by
    change F ≤ fittingSubgroupOf c.U ⊓ w.M
    rw [← hjoinY]
    exact le_sup_right
  have hK0leM : K0 ≤ w.M := hK0leY.trans inf_le_right
  have hFleFU : F ≤ c.FU := hFleY.trans inf_le_left
  have hK0normF : K0 ≤ Subgroup.normalizer (F : Set G) :=
    hK0leM.trans (le_normalizer_of_isNormalIn hFnormalM)
  have hK0Fdisj : Disjoint K0 F := by
    rw [disjoint_iff]
    apply le_bot_iff.mp
    intro x hx
    have hxInv : (s : G) * x * (s : G)⁻¹ = x⁻¹ := by
      have hxK : x ∈ K := by
        rw [hK0_def] at hx
        exact hx.1.2
      have hxI : x ∈ invertedElements (c.U ⊓ w.M) (s : G) := by
        rw [← hK_eq]
        exact hxK
      exact hxI.2
    have hxFix : (s : G) * x * (s : G)⁻¹ = x := by
      have hxC : x ∈ centralizerIn
          (fittingSubgroupOf c.U ⊓ w.M) (s : G) := by
        rw [← hF_eq]
        exact hx.2
      have hcomm : x * (s : G) = (s : G) * x :=
        ((Subgroup.mem_centralizer_iff.mp hxC.2) (s : G) (by simp)).symm
      calc
        (s : G) * x * (s : G)⁻¹ = x * (s : G) * (s : G)⁻¹ := by
          rw [hcomm]
        _ = x := by simp
    have hxinv_eq : x⁻¹ = x := hxInv.symm.trans hxFix
    have hxsq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x * x := pow_two x
        _ = x * x⁻¹ := congrArg (fun y => x * y) hxinv_eq.symm
        _ = 1 := by simp
    let xF : F := ⟨x, hx.2⟩
    have hxFsq : xF ^ 2 = 1 := by
      apply Subtype.ext
      exact hxsq
    have hcopF : Nat.Coprime 2 (Nat.card F) := by
      rw [hFcard]
      decide
    have hxFone : xF = 1 :=
      eq_one_of_sq_eq_one_of_coprime_two hcopF hxFsq
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxFone)
  have hYcard : Nat.card Y = 9 := by
    have hcard :=
      card_sup_eq_mul_of_disjoint_of_le_normalizer
        F K0 hK0normF hK0Fdisj.symm
    rw [sup_comm, hjoinY, hFcard, hK0card] at hcard
    norm_num at hcard ⊢
    exact hcard
  apply isPGroup_of_primeFactors_subset_singleton c.FU Nat.prime_three
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  by_cases hq3 : q = 3
  · exact hq3
  let : Fact q.Prime := ⟨hqprime⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let Q : Sylow q c.FU := Classical.choice Sylow.nonempty
  have hFp : IsPGroup 3 F := by
    apply IsPGroup.of_card (n := 1)
    simpa using hFcard
  have hFsubp : IsPGroup 3 (F.subgroupOf c.FU) :=
    hFp.of_equiv (Subgroup.subgroupOfEquivOfLe hFleFU).symm
  obtain ⟨R, hFleR⟩ := hFsubp.exists_le_sylow
  have hQnormal : (Q : Subgroup c.FU).Normal :=
    Group.IsNilpotent.sylow_normal
      (fittingSubgroupOf_isNilpotent c.U) q Q
  have hRnormal : (R : Subgroup c.FU).Normal :=
    Group.IsNilpotent.sylow_normal
      (fittingSubgroupOf_isNilpotent c.U) 3 R
  let : (Q : Subgroup c.FU).Normal := hQnormal
  let : (R : Subgroup c.FU).Normal := hRnormal
  have hQRdisj : Disjoint (Q : Subgroup c.FU) (R : Subgroup c.FU) :=
    IsPGroup.disjoint_of_ne q 3 hq3
      (Q : Subgroup c.FU) (R : Subgroup c.FU)
      Q.isPGroup' R.isPGroup'
  have hQRcomm : ⁅(Q : Subgroup c.FU), (R : Subgroup c.FU)⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_le_inf
      (Q : Subgroup c.FU) (R : Subgroup c.FU)).trans
        (by rw [hQRdisj.eq_bot])
  have hQcentR : (Q : Subgroup c.FU) ≤
      Subgroup.centralizer (R : Set c.FU) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQRcomm
  let QG : Subgroup G := (Q : Subgroup c.FU).map c.FU.subtype
  have hQGleFU : QG ≤ c.FU :=
    Subgroup.map_subtype_le (Q : Subgroup c.FU)
  have hQGcentF : QG ≤ Subgroup.centralizer (F : Set G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xFU, hxQ, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    let fFU : c.FU := ⟨f, hFleFU hf⟩
    have hfR : fFU ∈ (R : Subgroup c.FU) :=
      hFleR (Subgroup.mem_subgroupOf.mpr hf)
    have hcomm :=
      (Subgroup.mem_centralizer_iff.mp (hQcentR hxQ)) fFU hfR
    exact congrArg Subtype.val hcomm
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card F = 1 := by rw [hbot]; simp
    omega
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hQGleM : QG ≤ w.M := by
    intro x hx
    have hxN := Subgroup.centralizer_le_normalizer (F : Set G) (hQGcentF hx)
    rwa [hNFeq] at hxN
  have hQGleY : QG ≤ Y := fun x hx => ⟨hQGleFU hx, hQGleM hx⟩
  have hqdvdFU : q ∣ Nat.card c.FU := Nat.dvd_of_mem_primeFactors hq
  have hqfact : (Nat.card c.FU).factorization q ≠ 0 :=
    (hqprime.factorization_pos_of_dvd Nat.card_pos.ne' hqdvdFU).ne'
  have hqdvdQ : q ∣ Nat.card (Q : Subgroup c.FU) := by
    rw [Q.card_eq_multiplicity]
    exact dvd_pow_self q hqfact
  have hQGcard : Nat.card QG = Nat.card (Q : Subgroup c.FU) :=
    Subgroup.card_map_of_injective c.FU.subtype_injective
  have hqdvdY : q ∣ Nat.card Y := by
    exact (hQGcard ▸ hqdvdQ).trans (Subgroup.card_dvd_of_le hQGleY)
  rw [hYcard] at hqdvdY
  have hqdvdPow : q ∣ 3 ^ 2 := by
    rw [show 3 ^ 2 = 9 by norm_num]
    exact hqdvdY
  have hqdvd3 : q ∣ 3 := hqprime.dvd_of_dvd_pow hqdvdPow
  exact (Nat.prime_dvd_prime_iff_eq hqprime Nat.prime_three).mp hqdvd3

end CFSG.GorensteinWalter
