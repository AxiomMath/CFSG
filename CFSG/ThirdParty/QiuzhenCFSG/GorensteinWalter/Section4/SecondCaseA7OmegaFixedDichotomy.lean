module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The fixed-point split for the A7 omega subgroup -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Either the order-nine equation-(6) subgroup lies in `Q`, or the chosen
involution acts fixed-point-freely on `Q` and hence inverts it. -/
public theorem secondCase_a7_omega_fixed_dichotomy
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d) :
    let QG : Subgroup G := od.Q.map c.FU.subtype
    od.K ⊔ od.F ≤ QG ∨
      (¬ od.F ≤ QG ∧
        ∀ x : G, x ∈ QG →
          (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hAleFU : A ≤ c.FU := by
    change od.K ⊔ od.F ≤ c.FU
    rw [od.FU_inter_M_eq]
    exact inf_le_left
  have hFleA : od.F ≤ A := le_sup_right
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  let eQ : od.Q ≃* QG :=
    Subgroup.equivMapOfInjective od.Q c.FU.subtype c.FU.subtype_injective
  have hQGnc : ¬ IsCyclic QG := by
    intro hcyc
    exact od.Q_not_cyclic (eQ.isCyclic.mpr hcyc)
  have hAcard : Nat.card A = 9 := by
    change Nat.card (od.K ⊔ od.F : Subgroup G) = 9
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  by_cases hFleQ : od.F ≤ QG
  · left
    let FQ : Subgroup QG := od.F.subgroupOf QG
    have hFQcard : Nat.card FQ = 3 := by
      calc
        Nat.card FQ = Nat.card od.F :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleQ).toEquiv
        _ = 3 := od.F_card
    have hFQneTop : FQ ≠ ⊤ := by
      intro htop
      have hQGcard : Nat.card QG = 3 := by
        calc
          Nat.card QG = Nat.card (⊤ : Subgroup QG) := by simp
          _ = Nat.card FQ := by rw [← htop]
          _ = 3 := hFQcard
      exact hQGnc (isCyclic_of_prime_card hQGcard)
    have hQGp : IsPGroup 3 QG := by
      have hQsubp : IsPGroup 3 (QG.subgroupOf c.FU) :=
        od.FU_isPGroup.to_subgroup (QG.subgroupOf c.FU)
      exact hQsubp.of_equiv (Subgroup.subgroupOfEquivOfLe hQGleFU)
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let : Group.IsNilpotent QG := hQGp.isNilpotent
    have hlt : FQ < Subgroup.normalizer (FQ : Set QG) :=
      Group.normalizerCondition_of_isNilpotent FQ
        (lt_top_iff_ne_top.mpr hFQneTop)
    let NQ : Subgroup QG := Subgroup.normalizer (FQ : Set QG)
    let NG : Subgroup G := NQ.map QG.subtype
    have hNGleA : NG ≤ A := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨xQ, hxN, rfl⟩
      have hxNormF : (xQ : G) ∈ Subgroup.normalizer (od.F : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          let yQ : QG := ⟨y, hFleQ hy⟩
          have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          have hconj :=
            (Subgroup.mem_normalizer_iff.mp hxN yQ).mp hyFQ
          exact Subgroup.mem_subgroupOf.mp hconj
        · intro hy
          have hyQ : y ∈ QG := by
            have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ QG := hFleQ hy
            have hbackQ := QG.mul_mem
              (QG.mul_mem (QG.inv_mem xQ.2) hconjQ) xQ.2
            simpa [mul_assoc] using hbackQ
          let yQ : QG := ⟨y, hyQ⟩
          have hconjFQ : xQ * yQ * xQ⁻¹ ∈ FQ :=
            Subgroup.mem_subgroupOf.mpr hy
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hxN yQ).mpr hconjFQ)
      have hxM : (xQ : G) ∈ w.M := od.F_normalizer ▸ hxNormF
      change (xQ : G) ∈ od.K ⊔ od.F
      rw [od.FU_inter_M_eq]
      exact ⟨hQGleFU xQ.2, hxM⟩
    have hNQcardGt : 3 < Nat.card NQ := by
      have hcardlt : Nat.card FQ < Nat.card NQ :=
        natCard_lt_of_subgroup_lt hlt
      rwa [hFQcard] at hcardlt
    have hNGcard : Nat.card NG = Nat.card NQ :=
      Subgroup.card_map_of_injective QG.subtype_injective
    have hNGdiv : Nat.card NG ∣ 9 := by
      rw [← hAcard]
      exact Subgroup.card_dvd_of_le hNGleA
    have hNGcard9 : Nat.card NG = 9 := by
      have hgt : 3 < Nat.card NG := by rw [hNGcard]; exact hNQcardGt
      have hdivPow : Nat.card NG ∣ 3 ^ 2 := by
        norm_num
        exact hNGdiv
      obtain ⟨k, hk, heq⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).mp hdivPow
      rw [heq] at hgt ⊢
      interval_cases k <;> norm_num at hgt
      norm_num
    have hNGeqA : NG = A :=
      Subgroup.eq_of_le_of_card_ge hNGleA (by rw [hNGcard9, hAcard])
    change A ≤ QG
    rw [← hNGeqA]
    exact Subgroup.map_subtype_le NQ
  · right
    have hFQdisj : Disjoint od.F QG := by
      rw [disjoint_iff]
      let I : Subgroup G := od.F ⊓ QG
      have hIdiv : Nat.card I ∣ 3 := by
        rw [← od.F_card]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hIcard : Nat.card I = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hIdiv with h1 | h3
        · exact h1
        · exfalso
          have hIeqF : I = od.F :=
            Subgroup.eq_of_le_of_card_ge inf_le_left
              (by rw [h3, od.F_card])
          apply hFleQ
          rw [← hIeqF]
          exact inf_le_right
      exact (Subgroup.eq_bot_iff_card (H := I)).mpr hIcard
    have hQGnormalH : IsNormalIn QG c.H := by
      exact map_characteristic_isNormalIn_of_isNormalIn od.Q
        od.Q_characteristic (centralizerSetup_FU_isNormalIn_H c)
    have hsNQ : (od.s : G) ∈ Subgroup.normalizer (QG : Set G) :=
      le_normalizer_of_isNormalIn hQGnormalH od.s_mem_H
    let sN : Subgroup.normalizer (QG : Set G) := ⟨(od.s : G), hsNQ⟩
    let phi : MulAut QG := QG.normalizerMonoidHom sN
    have hphiInv : Function.Involutive phi := by
      intro x
      apply Subtype.ext
      simp only [phi, sN, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hsInv : (od.s : G)⁻¹ = (od.s : G) :=
        inv_eq_of_mul_eq_one_right
          (by simpa [pow_two] using od.s_involution.2)
      rw [hsInv]
      calc
        (od.s : G) * ((od.s : G) * (x : G) * (od.s : G)) *
              (od.s : G) =
            ((od.s : G) * (od.s : G)) * (x : G) *
              ((od.s : G) * (od.s : G)) := by group
        _ = (x : G) := by
          simp [show (od.s : G) * (od.s : G) = 1 by
            simpa [pow_two] using od.s_involution.2]
    have hphiFPF : MonoidHom.FixedPointFree phi := by
      intro x hx
      apply Subtype.ext
      have hxfix : (od.s : G) * (x : G) * (od.s : G)⁻¹ = (x : G) := by
        simpa [phi, sN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val hx
      have hxF : (x : G) ∈ od.F := by
        rw [od.F_fixed]
        refine ⟨hQGleFU x.2, ?_⟩
        change (x : G) ∈ Subgroup.centralizer ({(od.s : G)} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hmul := congrArg (fun z : G => z * (od.s : G)) hxfix
        have hcomm : (od.s : G) * (x : G) = (x : G) * (od.s : G) := by
          simpa [mul_assoc] using hmul
        exact hcomm.symm
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hFQdisj.eq_bot]
        exact ⟨hxF, x.2⟩
      exact Subgroup.mem_bot.mp hxbot
    refine ⟨hFleQ, ?_⟩
    intro x hx
    let xQ : QG := ⟨x, hx⟩
    have hinv := congrFun
      (hphiFPF.coe_eq_inv_of_involutive hphiInv) xQ
    simpa [phi, sN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hinv

end CFSG.GorensteinWalter
