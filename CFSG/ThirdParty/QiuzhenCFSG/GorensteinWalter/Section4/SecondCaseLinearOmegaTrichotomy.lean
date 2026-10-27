module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaGeneric
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaConjugation
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNilpotentNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
open scoped Pointwise commutatorElement
namespace CFSG.GorensteinWalter
universe u
local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)
namespace SecondCaseLinearOmegaView


variable {G : Type u} [Group G] [Finite G]
variable {c : CentralizerSetup G} {w : SecondCaseWitness c}
variable {d : SecondCaseComponentData w}

/-- Inside `Q`, the normalizer of the fixed prime-order part `P` is exactly
`A`. -/
public theorem normalizer_P_eq (od : SecondCaseLinearOmegaView c w d)
    (hPleQ : od.P ≤ od.QG) :
    (Subgroup.normalizer (od.P : Set G)) ⊓ od.QG = od.A := by
  classical
  let QG : Subgroup G := od.QG
  let FQ : Subgroup QG := od.P.subgroupOf QG
  have hFQcard : Nat.card FQ = od.p := by
    calc
      Nat.card FQ = Nat.card od.P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleQ).toEquiv
      _ = od.p := od.P_card
  let : Fact (Nat.Prime od.p) := ⟨od.p_prime⟩
  have hFQneTop : FQ ≠ ⊤ := by
    intro htop
    have hQGcard : Nat.card QG = od.p := by
      calc
        Nat.card QG = Nat.card (⊤ : Subgroup QG) := by simp
        _ = Nat.card FQ := by rw [← htop]
        _ = od.p := hFQcard
    exact od.QG_not_cyclic (isCyclic_of_prime_card (p := od.p) hQGcard)
  have hQGp : IsPGroup od.p QG := od.QG_isPGroup
  let : Group.IsNilpotent QG := hQGp.isNilpotent
  have hlt : FQ < Subgroup.normalizer (FQ : Set QG) :=
    Group.normalizerCondition_of_isNilpotent FQ (lt_top_iff_ne_top.mpr hFQneTop)
  let NQ : Subgroup QG := Subgroup.normalizer (FQ : Set QG)
  let NG : Subgroup G := NQ.map QG.subtype
  have hNGleA : NG ≤ od.A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xQ, hxN, rfl⟩
    have hxNormP : (xQ : G) ∈ Subgroup.normalizer (od.P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        let yQ : QG := ⟨y, hPleQ hy⟩
        have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
        have hconj := (Subgroup.mem_normalizer_iff.mp hxN yQ).mp hyFQ
        exact Subgroup.mem_subgroupOf.mp hconj
      · intro hy
        have hyQ : y ∈ QG := by
          have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ QG := hPleQ hy
          have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem xQ.2) hconjQ) xQ.2
          simpa [mul_assoc] using hbackQ
        let yQ : QG := ⟨y, hyQ⟩
        have hconjFQ : xQ * yQ * xQ⁻¹ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
        exact Subgroup.mem_subgroupOf.mp
          ((Subgroup.mem_normalizer_iff.mp hxN yQ).mpr hconjFQ)
    exact od.normalizer_le_A ⟨hxNormP, xQ.2⟩
  have hNQcardGt : od.p < Nat.card NQ := by
    have hcardlt : Nat.card FQ < Nat.card NQ :=
      natCard_lt_of_subgroup_lt hlt
    rwa [hFQcard] at hcardlt
  have hNGcard : Nat.card NG = Nat.card NQ :=
    Subgroup.card_map_of_injective QG.subtype_injective
  have hNGdiv : Nat.card NG ∣ od.p ^ 2 := by
    rw [← od.A_card]
    exact Subgroup.card_dvd_of_le hNGleA
  have hNGcard_p2 : Nat.card NG = od.p ^ 2 := by
    have hgt : od.p < Nat.card NG := by rw [hNGcard]; exact hNQcardGt
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow od.p_prime).mp hNGdiv
    rw [heq] at hgt
    have hp2 : 2 ≤ od.p := od.p_prime.two_le
    have hk2 : k = 2 := by
      interval_cases k
      · exfalso
        have h : od.p < 1 := by simpa using hgt
        omega
      · exfalso
        have h : od.p < od.p := by simpa using hgt
        omega
      · rfl
    simpa [hk2] using heq
  have hNGeqA : NG = od.A :=
    Subgroup.eq_of_le_of_card_ge hNGleA (by rw [hNGcard_p2, od.A_card])
  have hNGeq : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = NG := by
    ext x
    constructor
    · intro hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hx.2⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro yQ
      constructor
      · intro hy
        have hyP : (yQ : G) ∈ od.P := Subgroup.mem_subgroupOf.mp hy
        have hconj := (Subgroup.mem_normalizer_iff.mp hx.1 (yQ : G)).mp hyP
        exact Subgroup.mem_subgroupOf.mpr hconj
      · intro hy
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hx.1 (yQ : G)).mpr
            (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xQ, hxN, rfl⟩
      constructor
      · change (xQ : G) ∈ Subgroup.normalizer ((od.P : Set G))
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          have hyQ : y ∈ QG := hPleQ hy
          let yQ : QG := ⟨y, hyQ⟩
          have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          have hconj := (Subgroup.mem_normalizer_iff.mp hxN yQ).mp hyFQ
          exact Subgroup.mem_subgroupOf.mp hconj
        · intro hy
          have hyQ : y ∈ QG := by
            have hconjQ : (xQ : G) * y * (xQ : G)⁻¹ ∈ QG := hPleQ hy
            have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem xQ.2) hconjQ) xQ.2
            simpa [mul_assoc] using hbackQ
          let yQ : QG := ⟨y, hyQ⟩
          have hconjFQ : xQ * yQ * xQ⁻¹ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hxN yQ).mpr hconjFQ)
      · exact xQ.2
  rw [hNGeq]
  exact hNGeqA

/-- Either the whole rank-two subgroup `A` lies in `Q`, or `P` is disjoint
from `Q` and the chosen involution acts fixed-point-freely — hence by
inversion — on `Q`. -/
public theorem fixed_dichotomy (od : SecondCaseLinearOmegaView c w d) :
    od.A ≤ od.QG ∨
      (¬ od.P ≤ od.QG ∧
        ∀ x : G, x ∈ od.QG → (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) := by
  classical
  let QG : Subgroup G := od.QG
  by_cases hPleQ : od.P ≤ QG
  · left
    have hNGeq : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = od.A :=
      normalizer_P_eq od hPleQ
    rw [← hNGeq]
    exact inf_le_right
  · right
    refine ⟨hPleQ, ?_⟩
    have hFQdisj : Disjoint od.F QG := by
      rw [disjoint_iff]
      apply le_bot_iff.mp
      intro x hx
      have hxP : x ∈ od.P := od.F_inter_QG_le_P ⟨hx.1, hx.2⟩
      have hxPQ : x ∈ od.P ⊓ QG := ⟨hxP, hx.2⟩
      rw [P_inter_QG_eq_bot_of_not_le od hPleQ] at hxPQ
      exact Subgroup.mem_bot.mp hxPQ
    have hQnormalH : IsNormalIn QG c.H := by
      exact map_characteristic_isNormalIn_of_isNormalIn od.Q od.Q_characteristic
        (centralizerSetup_U_isNormalIn_H c)
    have hsNQ : (od.s : G) ∈ Subgroup.normalizer (QG : Set G) :=
      le_normalizer_of_isNormalIn hQnormalH od.s_mem_H
    let sN : Subgroup.normalizer (QG : Set G) := ⟨(od.s : G), hsNQ⟩
    let phi : MulAut QG := QG.normalizerMonoidHom sN
    have hphiInv : Function.Involutive phi := by
      intro x
      apply Subtype.ext
      simp only [phi, sN, Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hsInv : (od.s : G)⁻¹ = (od.s : G) :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using od.s_involution.2)
      rw [hsInv]
      calc
        (od.s : G) * ((od.s : G) * (x : G) * (od.s : G)) * (od.s : G) =
            ((od.s : G) * (od.s : G)) * (x : G) * ((od.s : G) * (od.s : G)) := by group
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
        refine ⟨od.QG_le_FU x.2, ?_⟩
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
    intro x hx
    let xQ : QG := ⟨x, hx⟩
    have hinv := congrFun (hphiFPF.coe_eq_inv_of_involutive hphiInv) xQ
    simpa [phi, sN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hinv




variable {G : Type u} [Group G] [Finite G]
variable {c : CentralizerSetup G} {w : SecondCaseWitness c}
variable {d : SecondCaseComponentData w}

/-- In the strict branch, the centre of `Q` has order `p`. -/
public theorem center_card_eq_p_of_lt (od : SecondCaseLinearOmegaView c w d)
    (hAltQ : od.A < od.QG) :
    Nat.card (Subgroup.center od.QG) = od.p := by
  classical
  let QG : Subgroup G := od.QG
  have hAleQ : od.A ≤ QG := hAltQ.le
  have hPleQ : od.P ≤ QG := (od.P_le_A).trans hAleQ
  have hZleA : (Subgroup.center QG).map QG.subtype ≤ od.A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hzNP : (z : G) ∈ Subgroup.normalizer (od.P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : y ∈ QG := hPleQ hy
        have hcomm := (Subgroup.mem_center_iff.mp hz) ⟨y, hyQ⟩
        have hcomm' : (z : G) * y = y * (z : G) := by
          simpa using (congrArg Subtype.val hcomm).symm
        have hconj : (z : G) * y * (z : G)⁻¹ = y := by
          calc
            (z : G) * y * (z : G)⁻¹ = y * (z : G) * (z : G)⁻¹ := by rw [hcomm']
            _ = y := by simp
        rwa [hconj]
      · intro hy
        have hyQ : y ∈ QG := by
          have hcQ : (z : G) * y * (z : G)⁻¹ ∈ QG := hPleQ hy
          have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem z.2) hcQ) z.2
          simpa [mul_assoc] using hbackQ
        have hcomm := (Subgroup.mem_center_iff.mp hz) ⟨y, hyQ⟩
        have hcomm' : (z : G) * y = y * (z : G) := by
          simpa using (congrArg Subtype.val hcomm).symm
        have hconj : (z : G) * y * (z : G)⁻¹ = y := by
          calc
            (z : G) * y * (z : G)⁻¹ = y * (z : G) * (z : G)⁻¹ := by rw [hcomm']
            _ = y := by simp
        rwa [hconj] at hy
    rw [← normalizer_P_eq od hPleQ]
    exact ⟨hzNP, z.2⟩
  have hZdiv : Nat.card (Subgroup.center QG) ∣ od.p ^ 2 := by
    have hcard : Nat.card ((Subgroup.center QG).map QG.subtype) ∣ od.p ^ 2 := by
      rw [← od.A_card]
      exact Subgroup.card_dvd_of_le hZleA
    exact (Subgroup.card_map_of_injective QG.subtype_injective) ▸ hcard
  let : Fact (Nat.Prime od.p) := ⟨od.p_prime⟩
  have hZne : Nat.card (Subgroup.center QG) ≠ 1 := by
    intro h1
    have : Nontrivial QG := od.QG_nontrivial
    have hnt : Nontrivial (Subgroup.center QG) :=
      IsPGroup.center_nontrivial (G := QG) od.QG_isPGroup
    have hgt : 1 < Nat.card (Subgroup.center QG) :=
      (Finite.one_lt_card_iff_nontrivial (α := Subgroup.center QG)).mpr hnt
    omega
  have hZneP2 : Nat.card (Subgroup.center QG) ≠ od.p ^ 2 := by
    intro hZP2
    have hZA : (Subgroup.center QG).map QG.subtype = od.A := by
      apply Subgroup.eq_of_le_of_card_ge hZleA
      rw [Subgroup.card_map_of_injective QG.subtype_injective, hZP2, od.A_card]
    have hPleZ : od.P ≤ (Subgroup.center QG).map QG.subtype := by
      intro p hp
      have hpZ : (p : G) ∈ (Subgroup.center QG).map QG.subtype := by
        rw [hZA]
        exact od.P_le_A hp
      rcases Subgroup.mem_map.mp hpZ with ⟨zp, hzp, hEq⟩
      exact Subgroup.mem_map.mpr ⟨zp, hzp, hEq⟩
    have hPnormal : (od.P.subgroupOf QG).Normal := by
      refine ⟨?_⟩
      intro f hf q
      have hfP : (f : G) ∈ od.P := Subgroup.mem_subgroupOf.mp hf
      have hfZ : (f : G) ∈ (Subgroup.center QG).map QG.subtype := hPleZ hfP
      rcases Subgroup.mem_map.mp hfZ with ⟨zf, hzf, hEq⟩
      have hcomm := (Subgroup.mem_center_iff.mp hzf) q
      have hEq' : (zf : G) = (f : G) := by simpa using hEq
      have hconj : q * f * q⁻¹ = f := by
        apply Subtype.ext
        have hqzf : (q : G) * (zf : G) = (zf : G) * (q : G) := by
          simpa using congrArg Subtype.val hcomm
        calc
          ((q * f * q⁻¹ : ↥QG) : G) = (q : G) * (f : G) * (q : G)⁻¹ := rfl
          _ = (q : G) * (zf : G) * (q : G)⁻¹ := by rw [← hEq']
          _ = (zf : G) * (q : G) * (q : G)⁻¹ := by rw [hqzf]
          _ = (zf : G) := by simp
          _ = (f : G) := hEq'
      rw [hconj]
      exact hf
    have hnormTop : Subgroup.normalizer ((od.P.subgroupOf QG) : Set QG) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hPnormal
    have hnormAQ : Subgroup.normalizer ((od.P.subgroupOf QG) : Set QG) =
        (od.A.subgroupOf QG) := by
      have hNP : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = od.A :=
        normalizer_P_eq od hPleQ
      ext x
      constructor
      · intro hx
        have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro y
          constructor
          · intro hy
            let yQ : QG := ⟨y, hPleQ hy⟩
            have hyFQ : yQ ∈ od.P.subgroupOf QG := Subgroup.mem_subgroupOf.mpr hy
            have hconj := (Subgroup.mem_normalizer_iff.mp hx yQ).mp hyFQ
            exact Subgroup.mem_subgroupOf.mp hconj
          · intro hy
            have hyQ : y ∈ QG := by
              have hconjQ : (x : G) * y * (x : G)⁻¹ ∈ QG := hPleQ hy
              have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem x.2) hconjQ) x.2
              simpa [mul_assoc] using hbackQ
            let yQ : QG := ⟨y, hyQ⟩
            have hconjFQ : x * yQ * x⁻¹ ∈ od.P.subgroupOf QG :=
              Subgroup.mem_subgroupOf.mpr hy
            exact Subgroup.mem_subgroupOf.mp
              ((Subgroup.mem_normalizer_iff.mp hx yQ).mpr hconjFQ)
        apply Subgroup.mem_subgroupOf.mpr
        rw [← hNP]
        exact ⟨hxNP, x.2⟩
      · intro hx
        have hxA : (x : G) ∈ od.A := Subgroup.mem_subgroupOf.mp hx
        have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
          rw [← hNP] at hxA
          exact hxA.1
        rw [Subgroup.mem_normalizer_iff]
        intro yQ
        constructor
        · intro hy
          have hyP : (yQ : G) ∈ od.P := Subgroup.mem_subgroupOf.mp hy
          have hconj := (Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mp hyP
          exact Subgroup.mem_subgroupOf.mpr hconj
        · intro hy
          exact Subgroup.mem_subgroupOf.mpr
            ((Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mpr
              (Subgroup.mem_subgroupOf.mp hy))
    have hAQtop : od.A.subgroupOf QG = ⊤ := hnormAQ.symm.trans hnormTop
    have hAQneTop : od.A.subgroupOf QG ≠ ⊤ := by
      intro htop
      apply hAltQ.ne
      apply le_antisymm hAleQ
      intro x hx
      have hxAQ : (⟨x, hx⟩ : QG) ∈ od.A.subgroupOf QG := by rw [htop]; simp
      exact Subgroup.mem_subgroupOf.mp hxAQ
    exact (hAQneTop hAQtop).elim
  have hZdiv' : Nat.card (Subgroup.center QG) ∣ od.p ^ 2 := hZdiv
  obtain ⟨k, hk, hZcard⟩ := (Nat.dvd_prime_pow od.p_prime).mp hZdiv'
  have hk1 : k = 1 := by
    interval_cases k
    · exfalso
      have h1 : od.p ^ 0 = 1 := by simp
      have : Nat.card (Subgroup.center QG) = 1 := by simpa [h1] using hZcard
      exact hZne this
    · rfl
    · exfalso
      have h2 : od.p ^ 2 = od.p ^ 2 := rfl
      have : Nat.card (Subgroup.center QG) = od.p ^ 2 := by simpa using hZcard
      exact hZneP2 this
  simpa [hk1] using hZcard

/-- In the strict branch, the ambient centre of `Q` is properly contained in
`A`. -/
public theorem center_lt_A_of_lt (od : SecondCaseLinearOmegaView c w d)
    (hAltQ : od.A < od.QG) :
    (Subgroup.center od.QG).map od.QG.subtype < od.A := by
  let QG : Subgroup G := od.QG
  have hle : (Subgroup.center od.QG).map od.QG.subtype ≤ od.A := by
    have hAleQ : od.A ≤ QG := hAltQ.le
    have hPleQ : od.P ≤ od.QG := (od.P_le_A).trans hAleQ
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hzNP : (z : G) ∈ Subgroup.normalizer (od.P : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : y ∈ QG := hPleQ hy
        have hcomm := (Subgroup.mem_center_iff.mp hz) ⟨y, hyQ⟩
        have hcomm' : (z : G) * y = y * (z : G) := by
          simpa using (congrArg Subtype.val hcomm).symm
        have hconj : (z : G) * y * (z : G)⁻¹ = y := by
          calc
            (z : G) * y * (z : G)⁻¹ = y * (z : G) * (z : G)⁻¹ := by rw [hcomm']
            _ = y := by simp
        rwa [hconj]
      · intro hy
        have hyQ : y ∈ QG := by
          have hcQ : (z : G) * y * (z : G)⁻¹ ∈ QG := hPleQ hy
          have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem z.2) hcQ) z.2
          simpa [mul_assoc] using hbackQ
        have hcomm := (Subgroup.mem_center_iff.mp hz) ⟨y, hyQ⟩
        have hcomm' : (z : G) * y = y * (z : G) := by
          simpa using (congrArg Subtype.val hcomm).symm
        have hconj : (z : G) * y * (z : G)⁻¹ = y := by
          calc
            (z : G) * y * (z : G)⁻¹ = y * (z : G) * (z : G)⁻¹ := by rw [hcomm']
            _ = y := by simp
        rwa [hconj] at hy
    rw [← normalizer_P_eq od hPleQ]
    exact ⟨hzNP, z.2⟩
  have hne : (Subgroup.center od.QG).map od.QG.subtype ≠ od.A := by
    have hcard : Nat.card ((Subgroup.center od.QG).map od.QG.subtype) = od.p := by
      rw [Subgroup.card_map_of_injective od.QG.subtype_injective]
      exact center_card_eq_p_of_lt od hAltQ
    intro hEq
    have hA : Nat.card od.A = od.p := by
      rw [← hEq, hcard]
    have hp2 : 1 < od.p := od.p_prime.one_lt
    have hpp : od.p < od.p ^ 2 := by
      calc
        od.p = od.p * 1 := by simp
        _ < od.p * od.p := Nat.mul_lt_mul_of_pos_left (by exact hp2) od.p_prime.pos
        _ = od.p ^ 2 := by rw [pow_two]
    have : od.p = od.p ^ 2 := by
      calc
        od.p = Nat.card od.A := hA.symm
        _ = od.p ^ 2 := od.A_card
    exact (ne_of_lt hpp) this
  exact lt_of_le_of_ne hle hne




variable {G : Type u} [Group G] [Finite G]
variable {c : CentralizerSetup G} {w : SecondCaseWitness c}
variable {d : SecondCaseComponentData w}

/-- If the rank-two subgroup `A` is properly contained in `Q`, then `A` has
relative index `p` in `Q`. -/
public theorem relIndex_eq_p_of_lt (od : SecondCaseLinearOmegaView c w d)
    (hAltQ : od.A < od.QG) :
    (od.A.subgroupOf od.QG).index = od.p := by
  classical
  let QG : Subgroup G := od.QG
  have hAleQ : od.A ≤ QG := hAltQ.le
  have hPleQ : od.P ≤ QG := (od.P_le_A).trans hAleQ
  have hPleA : od.P ≤ od.A := od.P_le_A
  let FQ : Subgroup QG := od.P.subgroupOf QG
  let AQ : Subgroup QG := od.A.subgroupOf QG
  have hFQcard : Nat.card FQ = od.p := by
    calc
      Nat.card FQ = Nat.card od.P :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPleQ).toEquiv
      _ = od.p := od.P_card
  have hAQcard : Nat.card AQ = od.p ^ 2 := by
    calc
      Nat.card AQ = Nat.card od.A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleQ).toEquiv
      _ = od.p ^ 2 := od.A_card
  let : Fact (Nat.Prime od.p) := ⟨od.p_prime⟩
  have hQGp : IsPGroup od.p QG := od.QG_isPGroup
  have mem_smul_iff (x y : QG) (T : Subgroup QG) :
      y ∈ x • T ↔ x⁻¹ * y * x ∈ T := by
    change y ∈ T.map (MulAut.conj x).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    have hNP : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = od.A :=
      normalizer_P_eq od hPleQ
    ext x
    constructor
    · intro hx
      have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          let yQ : QG := ⟨y, hPleQ hy⟩
          have hyFQ : yQ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          have hconj := (Subgroup.mem_normalizer_iff.mp hx yQ).mp hyFQ
          exact Subgroup.mem_subgroupOf.mp hconj
        · intro hy
          have hyQ : y ∈ QG := by
            have hconjQ : (x : G) * y * (x : G)⁻¹ ∈ QG := hPleQ hy
            have hbackQ := QG.mul_mem (QG.mul_mem (QG.inv_mem x.2) hconjQ) x.2
            simpa [mul_assoc] using hbackQ
          let yQ : QG := ⟨y, hyQ⟩
          have hconjFQ : x * yQ * x⁻¹ ∈ FQ := Subgroup.mem_subgroupOf.mpr hy
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hx yQ).mpr hconjFQ)
      apply Subgroup.mem_subgroupOf.mpr
      rw [← hNP]
      exact ⟨hxNP, x.2⟩
    · intro hx
      have hxA : (x : G) ∈ od.A := Subgroup.mem_subgroupOf.mp hx
      have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
        rw [← hNP] at hxA
        exact hxA.1
      rw [Subgroup.mem_normalizer_iff]
      intro yQ
      constructor
      · intro hy
        have hyP : (yQ : G) ∈ od.P := Subgroup.mem_subgroupOf.mp hy
        have hconj := (Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mp hyP
        exact Subgroup.mem_subgroupOf.mpr hconj
      · intro hy
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mpr
            (Subgroup.mem_subgroupOf.mp hy))
  have hstab : MulAction.stabilizer QG FQ = AQ := by
    have hstabNorm : MulAction.stabilizer QG FQ =
        Subgroup.normalizer (FQ : Set QG) := by
      ext x
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_normalizer_iff]
      constructor
      · intro h y
        constructor
        · intro hy
          have hmem : x * y * x⁻¹ ∈ x • FQ :=
            (mem_smul_iff x (x * y * x⁻¹) FQ).mpr (by simpa [mul_assoc] using hy)
          rwa [h] at hmem
        · intro hconj
          have hmem : x * y * x⁻¹ ∈ x • FQ := by rwa [h]
          have hm := (mem_smul_iff x (x * y * x⁻¹) FQ).mp hmem
          simpa [mul_assoc] using hm
      · intro h
        ext y
        rw [mem_smul_iff]
        simpa [mul_assoc] using h (x⁻¹ * y * x)
    exact hstabNorm.trans hnormFQ
  let Orb := MulAction.orbit QG FQ
  have hTcard : ∀ T : Orb, Nat.card T.1 = od.p := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    have hcard : Nat.card ↥(q • FQ : Subgroup QG) = Nat.card FQ := by
      change Nat.card (FQ.map (MulAut.conj q).toMonoidHom) = Nat.card FQ
      exact Subgroup.card_map_of_injective (MulAut.conj q).injective
    rw [← hq]
    exact hcard.trans hFQcard
  have hTleA : ∀ T : Orb, (T.1.map QG.subtype) ≤ od.A := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨yQ, hyT, rfl⟩
    have hySmul : yQ ∈ q • FQ := by
      change yQ ∈ (fun m : QG => m • FQ) q
      rw [hq]
      exact hyT
    have hpre : q⁻¹ * yQ * q ∈ FQ :=
      (mem_smul_iff q yQ FQ).mp hySmul
    have hpreP : ((q⁻¹ * yQ * q : QG) : G) ∈ od.P :=
      Subgroup.mem_subgroupOf.mp hpre
    have hconj := od.conj_le_A (q : G) q.2
      (((q⁻¹ * yQ * q : QG) : G)) hpreP
    simpa [mul_assoc] using hconj
  have hTne : ∀ T : Orb, T.1 ≠ ⊥ := by
    intro T hbot
    have hcard1 : Nat.card T.1 = 1 := by rw [hbot]; simp
    have hcardp := hTcard T
    have hp2 : 2 ≤ od.p := od.p_prime.two_le
    omega
  let pick : ∀ T : Orb, T.1 := fun T =>
    Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp (hTne T))
  have pick_ne (T : Orb) : pick T ≠ 1 :=
    Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp (hTne T))
  let target := {x : od.A // x ≠ 1}
  let f : Orb → target := fun T =>
    ⟨⟨((pick T : T.1) : QG), hTleA T
      (Subgroup.mem_map.mpr ⟨(pick T : T.1), (pick T).2, rfl⟩)⟩,
      by
        intro h1
        apply pick_ne T
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : od.A => (z : G)) h1⟩
  have hfInj : Function.Injective f := by
    intro T S hTS
    have hvalG : ((((f T).1 : od.A) : G)) = (((f S).1 : od.A) : G) :=
      congrArg (fun z : target => ((z.1 : od.A) : G)) hTS
    have hval : ((pick T : T.1) : QG) = ((pick S : S.1) : QG) :=
      Subtype.ext hvalG
    have hpickS_ne : ((pick S : S.1) : QG) ≠ 1 := by
      intro h1
      apply pick_ne S
      exact Subtype.ext h1
    have hsubEq : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one od.p_prime
        T.1 S.1 (hTcard T) (hTcard S)
        (by
          have hmem := (pick T).2
          change ((pick T : T.1) : QG) ∈ T.1 at hmem
          rw [hval] at hmem
          exact hmem)
        (pick S).2 hpickS_ne
    exact Subtype.ext hsubEq
  have htargetCard : Nat.card target = od.p ^ 2 - 1 := by
    let : Fintype od.A := Fintype.ofFinite od.A
    let : Fintype target := Fintype.ofFinite target
    have hAF : Fintype.card od.A = od.p ^ 2 := by
      simpa [Nat.card_eq_fintype_card] using od.A_card
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [hAF]
  have hOrbLe : Nat.card Orb ≤ od.p ^ 2 - 1 := by
    rw [← htargetCard]
    exact Nat.card_le_card_of_injective f hfInj
  have hOrbIndex : Nat.card Orb = AQ.index := by
    calc
      Nat.card Orb = Nat.card (QG ⧸ MulAction.stabilizer QG FQ) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer QG FQ)
      _ = (MulAction.stabilizer QG FQ).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer QG FQ)).symm
      _ = AQ.index := by rw [hstab]
  have hindexLe : AQ.index ≤ od.p ^ 2 - 1 := by rw [← hOrbIndex]; exact hOrbLe
  obtain ⟨n, hn⟩ := hQGp.index AQ
  have hindexGt : 1 < AQ.index := by
    have hAQlt : AQ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hAltQ.ne
      apply le_antisymm hAleQ
      intro x hx
      have hxAQ : (⟨x, hx⟩ : QG) ∈ AQ := by rw [htop]; simp
      exact Subgroup.mem_subgroupOf.mp hxAQ
    have hidxne : AQ.index ≠ 1 := by
      intro hidx
      exact (lt_top_iff_ne_top.mp hAQlt) (Subgroup.index_eq_one.mp hidx)
    have hidxpos : 0 < AQ.index := by
      rw [Subgroup.index_eq_card]
      exact Nat.card_pos
    omega
  have hnOne : n = 1 := by
    have hnPos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      rw [hn, this] at hindexGt
      simpa using hindexGt
    by_contra hn1
    have hnTwo : 2 ≤ n := by omega
    have hpow : od.p ^ 2 ≤ od.p ^ n :=
      Nat.pow_le_pow_right (by exact od.p_prime.pos) hnTwo
    rw [← hn] at hpow
    have hsub : od.p ^ 2 - 1 < od.p ^ 2 :=
      Nat.sub_lt (pow_pos od.p_prime.pos 2) (by norm_num)
    have hle : od.p ^ 2 ≤ od.p ^ 2 - 1 := le_trans hpow hindexLe
    exact (not_lt_of_ge hle) hsub
  have hindex : AQ.index = od.p := by rw [hn, hnOne]; norm_num
  simpa [AQ, QG] using hindex




variable {G : Type u} [Group G] [Finite G]
variable {c : CentralizerSetup G} {w : SecondCaseWitness c}
variable {d : SecondCaseComponentData w}

/-- The omega trichotomy: either the rank-two subgroup `A` equals `Q`, or
the centre of `Q` is properly contained in `A` and `A` is properly contained
in `Q` with relative index `p`, or the chosen involution inverts `Q`. -/
public theorem trichotomy (od : SecondCaseLinearOmegaView c w d) :
    od.A = od.QG ∨
      ((Subgroup.center od.QG).map od.QG.subtype < od.A ∧ od.A < od.QG ∧
        (od.A.subgroupOf od.QG).index = od.p) ∨
      (∀ x : G, x ∈ od.QG → (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) := by
  rcases fixed_dichotomy od with hle | ⟨hPnotleQ, hinvQ⟩
  · by_cases heq : od.A = od.QG
    · exact Or.inl heq
    · right
      left
      have hlt : od.A < od.QG := lt_of_le_of_ne hle heq
      exact ⟨center_lt_A_of_lt od hlt, hlt, relIndex_eq_p_of_lt od hlt⟩
  · exact Or.inr (Or.inr hinvQ)


end SecondCaseLinearOmegaView
private noncomputable def make_linear_omega_view
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    SecondCaseLinearOmegaView c w d := by
  let hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
    c.U c.FU w.M od.F od.B (od.s : G)
      (fittingSubgroupOf_isNilpotent c.U)
      (fittingSubgroupOf_isNormalIn c.U)
      od.F_fixed od.B_fixed od.F_normalizer
  have hpodd : Odd od.p := secondCase_linear_omega_p_odd c w d od
  have hP0inv : ∀ x : G, x ∈ od.P0 →
      (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹ := by
    intro x hx
    have hxK0 : x ∈ od.K0 := od.P0_le_K0 hx
    have hxK : x ∈ od.K := by
      rw [od.K0_eq] at hxK0
      exact hxK0.2
    have hxI : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
      rw [← od.K_inverted]
      exact hxK
    exact hxI.2
  have hcontrol := secondCase_linear_omega_conjugation_control c w d od
  exact {
    p := od.p
    p_prime := od.hp_prime
    p_odd := hpodd
    s := od.s
    s_involution := od.s_involution
    s_mem_H := od.s_mem_H
    F := od.F
    F_cyclic := od.F_cyclic
    F_fixed := hfull.1
    P := od.P
    P_card := od.P_card
    P_le_F := od.P_le_F
    P0 := od.P0
    P0_card := od.P0_card
    P0_inverted := hP0inv
    A := od.A
    A_eq := by
      calc
        od.A = od.P ⊔ od.P0 := od.A_eq
        _ = od.P0 ⊔ od.P := sup_comm _ _
    A_card := od.A_card
    Q := od.Q
    Q_le_upperCentralSeries_two := od.Q_le_upperCentralSeries_two
    Q_not_cyclic := od.Q_not_cyclic
    Q_exponent := od.Q_exponent
    Q_characteristic := od.Q_characteristic
    normalizer_le_A := hcontrol.1
    conj_le_A := hcontrol.2 }

/-- The linear omega trichotomy: equality, the strict index-`p` case, or
inversion by the chosen reflection. -/
public theorem secondCase_linear_omega_trichotomy
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    let QG : Subgroup G := od.Q.map c.U.subtype
    od.A = QG ∨
      ((Subgroup.center QG).map QG.subtype < od.A ∧ od.A < QG ∧
        (od.A.subgroupOf QG).index = od.p) ∨
      (∀ x : G, x ∈ QG →
        (od.s : G) * x * (od.s : G)⁻¹ = x⁻¹) := by
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  let v := make_linear_omega_view c w d od
  convert (SecondCaseLinearOmegaView.trichotomy v) using 1 <;>
    simp only [v, make_linear_omega_view, SecondCaseLinearOmegaView.QG]
  · constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
end CFSG.GorensteinWalter
