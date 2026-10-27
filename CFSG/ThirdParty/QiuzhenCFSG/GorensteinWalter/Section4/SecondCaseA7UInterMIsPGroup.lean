module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingIsPGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Prime support of the A7 intersection with the maximal subgroup

Equation (6) controls the fixed and inverted factors of `U ∩ M`.  The
odd-order fixed factor centralizes the corresponding factors of `F(U) ∩ M`,
which excludes every prime other than three by the subnormal centralizer
transfer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the A7 branch, `U ∩ M` is a `3`-group. -/
public theorem secondCase_a7_U_inter_M_isPGroup_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    IsPGroup 3 ↥(c.U ⊓ w.M) := by
  classical
  obtain ⟨K, B, s, _hsI, _hsH, hK_eq, _hKcyc, hB_def, hjoinX, hKcard,
      _hKleE,
      K0, F, hK0_def, _hFdef, hF_eq, hjoinY, hFnormalM,
      _hFcentE, _hFcyc, hK0card, hFcard⟩ :=
    secondCase_a7_equation6 hmin c w d hA7 hmodel
  let X : Subgroup G := c.U ⊓ w.M
  let Y : Subgroup G := c.FU ⊓ w.M
  have hKleX : K ≤ X := by
    change K ≤ c.U ⊓ w.M
    rw [← hjoinX]
    exact le_sup_left
  have hBleX : B ≤ X := by
    change B ≤ c.U ⊓ w.M
    rw [← hjoinX]
    exact le_sup_right
  have hYeq : K0 ⊔ F = Y := by
    simpa [Y, CentralizerSetup.FU] using hjoinY
  have hK0leK : K0 ≤ K := by
    rw [hK0_def]
    exact inf_le_right
  have hK0eqK : K0 = K :=
    Subgroup.eq_of_le_of_card_ge hK0leK (by rw [hK0card, hKcard])
  have hKleFU : K ≤ c.FU := by
    rw [← hK0eqK, hK0_def]
    exact inf_le_left
  have hFleY : F ≤ Y := by
    rw [← hYeq]
    exact le_sup_right
  have hFleFU : F ≤ c.FU := hFleY.trans inf_le_left
  have hBleU : B ≤ c.U := hBleX.trans inf_le_left
  have hBleM : B ≤ w.M := hBleX.trans inf_le_right
  have hBodd : Odd (Nat.card B) := by
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    exact Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le hBleU)
  have hBnormK : B ≤ Subgroup.normalizer (K : Set G) := by
    have hconj_mem : ∀ b : G, b ∈ B → ∀ k : G, k ∈ K →
        b * k * b⁻¹ ∈ K := by
      intro b hb k hk
      have hbC : b ∈ centralizerIn X (s : G) := by
        simpa [X] using (hB_def ▸ hb)
      have hbfix : (s : G) * b * (s : G)⁻¹ = b := by
        have hcomm : (s : G) * b = b * (s : G) :=
          (Subgroup.mem_centralizer_iff.mp hbC.2) (s : G) (by simp)
        calc
          (s : G) * b * (s : G)⁻¹ = b * (s : G) * (s : G)⁻¹ := by
            rw [hcomm]
          _ = b := by simp
      have hbinvfix : (s : G) * b⁻¹ * (s : G)⁻¹ = b⁻¹ := by
        calc
          (s : G) * b⁻¹ * (s : G)⁻¹ =
              ((s : G) * b * (s : G)⁻¹)⁻¹ := by group
          _ = b⁻¹ := by rw [hbfix]
      have hkI : k ∈ invertedElements X (s : G) := by
        simpa [X] using (hK_eq ▸ hk)
      have hconjX : b * k * b⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem (hBleX hb) hkI.1) (X.inv_mem (hBleX hb))
      have hconjInv :
          (s : G) * (b * k * b⁻¹) * (s : G)⁻¹ =
            (b * k * b⁻¹)⁻¹ := by
        calc
          (s : G) * (b * k * b⁻¹) * (s : G)⁻¹ =
              ((s : G) * b * (s : G)⁻¹) *
                ((s : G) * k * (s : G)⁻¹) *
                  ((s : G) * b⁻¹ * (s : G)⁻¹) := by group
          _ = b * k⁻¹ * b⁻¹ := by rw [hbfix, hkI.2, hbinvfix]
          _ = (b * k * b⁻¹)⁻¹ := by group
      change b * k * b⁻¹ ∈ (K : Set G)
      rw [hK_eq]
      exact ⟨hconjX, hconjInv⟩
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact hconj_mem b hb k
    · intro hconj
      have hback := hconj_mem b⁻¹ (B.inv_mem hb)
        (b * k * b⁻¹) hconj
      simpa [mul_assoc] using hback
  have hBnormF : B ≤ Subgroup.normalizer (F : Set G) :=
    hBleM.trans (le_normalizer_of_isNormalIn hFnormalM)
  have hBcentK : B ≤ Subgroup.centralizer (K : Set G) :=
    odd_subgroup_le_centralizer_of_le_normalizer_card_three
      B K hBodd hKcard hBnormK
  have hBcentK0 : B ≤ Subgroup.centralizer (K0 : Set G) :=
    hBcentK.trans (Subgroup.centralizer_le (SetLike.coe_mono hK0leK))
  have hBcentF : B ≤ Subgroup.centralizer (F : Set G) :=
    odd_subgroup_le_centralizer_of_le_normalizer_card_three
      B F hBodd hFcard hBnormF
  have hBcentY : B ≤ Subgroup.centralizer (Y : Set G) := by
    rw [← hYeq]
    exact le_centralizer_sup_of_le_centralizers hBcentK0 hBcentF
  have hFUp : IsPGroup 3 c.FU :=
    secondCase_a7_fitting_isPGroup_three hmin c w d hA7 hmodel
  have hFnil : Group.IsNilpotent c.FU :=
    fittingSubgroupOf_isNilpotent c.U
  let : Group.IsNilpotent c.FU := hFnil
  have hYleFU : Y ≤ c.FU := inf_le_left
  have hYsub : (Y.subgroupOf c.FU).IsSubnormal :=
    isSubnormal_of_nilpotent hFnil Y hYleFU
  have hFne : F ≠ ⊥ := by
    intro hbot
    have hcard1 : Nat.card F = 1 := by rw [hbot]; simp
    omega
  have hNFeq : Subgroup.normalizer (F : Set G) = w.M :=
    secondCase_normalizer_fitting_fixed_eq_M hmin c w F hFne hFnormalM
  have hYself : c.FU ⊓ Subgroup.centralizer (Y : Set G) ≤ Y := by
    intro x hx
    have hxCentF : x ∈ Subgroup.centralizer (F : Set G) :=
      (Subgroup.centralizer_le (SetLike.coe_mono hFleY)) hx.2
    have hxN : x ∈ Subgroup.normalizer (F : Set G) :=
      Subgroup.centralizer_le_normalizer (F : Set G) hxCentF
    have hxM : x ∈ w.M := hNFeq ▸ hxN
    exact ⟨hx.1, hxM⟩
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hUsolv : Group.IsSolvable c.U := odd_order_theorem c.U hUodd
  have hFUself : c.U ⊓ Subgroup.centralizer (c.FU : Set G) ≤ c.FU :=
    fact_1_2_centralizer_fitting_le_fitting c.U hUsolv
  have hBp : IsPGroup 3 B := by
    apply isPGroup_of_primeFactors_subset_singleton B Nat.prime_three
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    by_cases hq3 : q = 3
    · exact hq3
    let : Fact q.Prime := ⟨hqprime⟩
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let Q : Sylow q B := Classical.choice Sylow.nonempty
    let P : Subgroup G := (Q : Subgroup B).map B.subtype
    have hPp : IsPGroup q P := Q.isPGroup'.map B.subtype
    have hPleB : P ≤ B := Subgroup.map_subtype_le (Q : Subgroup B)
    have hPleU : P ≤ c.U := hPleB.trans hBleU
    have hFUnormalU : IsNormalIn c.FU c.U :=
      fittingSubgroupOf_isNormalIn c.U
    have hPnormFU : P ≤ Subgroup.normalizer (c.FU : Set G) :=
      hPleU.trans (le_normalizer_of_isNormalIn hFUnormalU)
    have hPcentY : P ≤ Subgroup.centralizer (Y : Set G) :=
      hPleB.trans hBcentY
    have hcop : Nat.Coprime (Nat.card P) (Nat.card c.FU) :=
      IsPGroup.coprime_card_of_ne q 3 hq3 P c.FU hPp hFUp
    have hPcentFU : P ≤ Subgroup.centralizer (c.FU : Set G) :=
      centralizes_of_subnormal_selfCentralizing_coprime
        P c.FU Y hPnormFU hYleFU hYsub hPcentY hYself hcop
          (inferInstance : Group.IsSolvable c.FU)
    have hPleFU : P ≤ c.FU := by
      intro x hx
      exact hFUself ⟨hPleU hx, hPcentFU hx⟩
    have hPdisj : Disjoint P c.FU :=
      IsPGroup.disjoint_of_ne q 3 hq3 P c.FU hPp hFUp
    have hPbot : P = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      exact hPdisj.le_bot ⟨hx, hPleFU hx⟩
    have hqdvdB : q ∣ Nat.card B := Nat.dvd_of_mem_primeFactors hq
    have hQne : (Q : Subgroup B) ≠ ⊥ := Q.ne_bot_of_dvd_card hqdvdB
    have hQbot : (Q : Subgroup B) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (Q : Subgroup B)) (f := B.subtype)
          (hf := B.subtype_injective)).mp hPbot
    exact False.elim (hQne hQbot)
  have hKp : IsPGroup 3 K := by
    apply IsPGroup.of_card (n := 1)
    simpa using hKcard
  have hXp : IsPGroup 3 (K ⊔ B : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hKp hBp hBnormK
  rw [← hjoinX]
  exact hXp

end CFSG.GorensteinWalter
