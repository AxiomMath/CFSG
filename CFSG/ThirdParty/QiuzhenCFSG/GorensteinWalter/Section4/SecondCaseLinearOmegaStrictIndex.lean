module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaEqualityIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaTrichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupFittingNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FixedCentralizerFromNilpotentNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The strict branch of the linear omega equation-(8) index bound

This is the generic consumer for the strict omega branch.  From the strict
trichotomy tuple it derives the order and centre cardinalities of the ambient
copy of `Q`.  It then counts the `Q`-orbit of `P` to obtain the normalizer
containment, counts the `U`-orbit of `A`, and uses oddness to remove the `+1`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)

/-! The strict trichotomy hypothesis is `A < Q`; the cardinal and normalizer
    facts are exactly the branch outputs needed by equation (8). -/

private theorem secondCase_linear_omega_strict_index_bounds
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hstrict :
      (Subgroup.center (od.Q.map c.U.subtype)).map
          (od.Q.map c.U.subtype).subtype < od.A ∧
      od.A < od.Q.map c.U.subtype ∧
      (od.A.subgroupOf (od.Q.map c.U.subtype)).index = od.p) :
    (normalizerIn c.U od.A).relIndex c.U ≤ od.p ∧
      (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p := by
  classical
  let QG : Subgroup G := od.Q.map c.U.subtype
  let ZQ : Subgroup QG := Subgroup.center QG
  let ZG : Subgroup G := ZQ.map QG.subtype
  let AQ : Subgroup QG := od.A.subgroupOf QG
  let FQ : Subgroup QG := od.P.subgroupOf QG
  have hAZlt : ZG < od.A := hstrict.1
  have hAleQ : od.A ≤ QG := hstrict.2.1.le
  have hPleA : od.P ≤ od.A := by rw [od.A_eq]; exact le_sup_left
  have hPleQ : od.P ≤ QG := hPleA.trans hAleQ
  have hAQcard : Nat.card AQ = od.p ^ 2 := by
    calc
      Nat.card AQ = Nat.card od.A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleQ).toEquiv
      _ = od.p ^ 2 := od.A_card
  have hAQindex : AQ.index = od.p := hstrict.2.2
  have hQcard : Nat.card QG = od.p ^ 3 := by
    have hmul := Subgroup.card_mul_index AQ
    rw [hAQcard, hAQindex] at hmul
    calc
      Nat.card QG = od.p ^ 2 * od.p := hmul.symm
      _ = od.p ^ 3 := by ring
  let : Fact od.p.Prime := ⟨od.hp_prime⟩
  have hQp : IsPGroup od.p QG := by
    intro x
    refine ⟨1, ?_⟩
    let eQ : od.Q ≃* QG :=
      Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
    have hexp : Monoid.exponent QG = od.p :=
      (Monoid.exponent_eq_of_mulEquiv eQ).symm.trans od.Q_exponent
    have hx : x ^ od.p = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (by rw [hexp]) x)
    simpa using hx
  have hZGcard : Nat.card ZG = od.p := by
    have hdiv : Nat.card ZG ∣ od.p ^ 2 := by
      rw [← od.A_card]
      exact Subgroup.card_dvd_of_le hAZlt.le
    have hneOne : Nat.card ZG ≠ 1 := by
      intro h1
      have : Nontrivial QG := by
        apply Finite.one_lt_card_iff_nontrivial.mp
        rw [hQcard]
        exact one_lt_pow₀ od.hp_prime.one_lt (by norm_num)
      have hnt : Nontrivial (Subgroup.center QG) :=
        IsPGroup.center_nontrivial (G := QG) hQp
      have hcenterGt : 1 < Nat.card (Subgroup.center QG) :=
        (Finite.one_lt_card_iff_nontrivial (α := Subgroup.center QG)).mpr hnt
      have hmapcard : Nat.card ZG = Nat.card (Subgroup.center QG) :=
        Subgroup.card_map_of_injective QG.subtype_injective
      rw [hmapcard] at h1
      omega
    have hltP2 : Nat.card ZG < od.p ^ 2 := by
      rw [← od.A_card]
      exact natCard_lt_of_subgroup_lt hAZlt
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow od.hp_prime).mp hdiv
    have hkOne : k = 1 := by
      interval_cases k
      · have : Nat.card ZG = 1 := by simpa using heq
        exact (hneOne this).elim
      · rfl
      · rw [heq] at hltP2
        exact (lt_irrefl _ hltP2).elim
    simpa [hkOne] using heq
  have hZQcard : Nat.card ZQ = od.p := by
    rw [← hZGcard]
    exact (Subgroup.card_map_of_injective QG.subtype_injective).symm
  have hAQnormal : AQ.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hAQindex, hQcard]
    rw [od.hp_prime.pow_minFac (by norm_num : 3 ≠ 0)]
  let hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
    c.U c.FU w.M od.F od.B (od.s : G)
      (fittingSubgroupOf_isNilpotent c.U)
      (fittingSubgroupOf_isNormalIn c.U)
      od.F_fixed od.B_fixed od.F_normalizer
  let v : SecondCaseLinearOmegaView c w d := {
    p := od.p
    p_prime := od.hp_prime
    p_odd := secondCase_linear_omega_p_odd c w d od
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
    P0_inverted := by
      intro x hx
      have hxK0 : x ∈ od.K0 := od.P0_le_K0 hx
      have hxK : x ∈ od.K := by rw [od.K0_eq] at hxK0; exact hxK0.2
      have hxI : x ∈ invertedElements (c.U ⊓ w.M) (od.s : G) := by
        rw [← od.K_inverted]
        exact hxK
      exact hxI.2
    A := od.A
    A_eq := by rw [od.A_eq, sup_comm]
    A_card := od.A_card
    Q := od.Q
    Q_le_upperCentralSeries_two := od.Q_le_upperCentralSeries_two
    Q_not_cyclic := od.Q_not_cyclic
    Q_exponent := od.Q_exponent
    Q_characteristic := od.Q_characteristic
    normalizer_le_A := (secondCase_linear_omega_conjugation_control c w d od).1
    conj_le_A := (secondCase_linear_omega_conjugation_control c w d od).2 }
  have hNP : (Subgroup.normalizer (od.P : Set G)) ⊓ QG = od.A := by
    simpa [QG, v, SecondCaseLinearOmegaView.QG] using
      (SecondCaseLinearOmegaView.normalizer_P_eq v hPleQ)
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    ext x
    constructor
    · intro hx
      have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy
          let yQ : QG := ⟨y, hPleQ hy⟩
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hx yQ).mp
              (Subgroup.mem_subgroupOf.mpr hy))
        · intro hy
          have hyQ : y ∈ QG := by
            have hcQ : (x : G) * y * (x : G)⁻¹ ∈ QG := hPleQ hy
            simpa [mul_assoc] using QG.mul_mem (QG.mul_mem (QG.inv_mem x.2) hcQ) x.2
          let yQ : QG := ⟨y, hyQ⟩
          exact Subgroup.mem_subgroupOf.mp
            ((Subgroup.mem_normalizer_iff.mp hx yQ).mpr
              (Subgroup.mem_subgroupOf.mpr hy))
      exact Subgroup.mem_subgroupOf.mpr (by rw [← hNP]; exact ⟨hxNP, x.2⟩)
    · intro hx
      have hxA : (x : G) ∈ od.A := Subgroup.mem_subgroupOf.mp hx
      have hxNP : (x : G) ∈ Subgroup.normalizer (od.P : Set G) := by
        rw [← hNP] at hxA
        exact hxA.1
      rw [Subgroup.mem_normalizer_iff]
      intro yQ
      constructor
      · intro hy
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mp
            (Subgroup.mem_subgroupOf.mp hy))
      · intro hy
        exact Subgroup.mem_subgroupOf.mpr
          ((Subgroup.mem_normalizer_iff.mp hxNP (yQ : G)).mpr
            (Subgroup.mem_subgroupOf.mp hy))
  have hQnormalU : IsNormalIn QG c.U := by
    change IsNormalIn (od.Q.map c.U.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q od.Q_characteristic
      ⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩
  have hZnormalU : IsNormalIn ZG c.U :=
    map_characteristic_isNormalIn_of_isNormalIn ZQ
      Subgroup.centerCharacteristic hQnormalU
  have mem_q_smul_iff (q : QG) (y : G) (T : Subgroup G) :
      y ∈ q • T ↔ (q : G)⁻¹ * y * (q : G) ∈ T := by
    change y ∈ T.map (MulAut.conj (q : G)).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  let OrbP := MulAction.orbit QG od.P
  have hstabP : MulAction.stabilizer QG od.P = AQ := by
    ext q
    rw [MulAction.mem_stabilizer_iff]
    change od.P.map (MulAut.conj (q : G)).toMonoidHom = od.P ↔ q ∈ AQ
    constructor
    · intro hmap
      have hqN : (q : G) ∈ Subgroup.normalizer (od.P : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
      exact Subgroup.mem_subgroupOf.mpr (by rw [← hNP]; exact ⟨hqN, q.2⟩)
    · intro hq
      have hqA : (q : G) ∈ od.A := Subgroup.mem_subgroupOf.mp hq
      rw [← hNP] at hqA
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hqA.1
  have hOrbPcard : Nat.card OrbP = od.p := by
    calc
      Nat.card OrbP = Nat.card (QG ⧸ MulAction.stabilizer QG od.P) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer QG od.P)
      _ = (MulAction.stabilizer QG od.P).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer QG od.P)).symm
      _ = AQ.index := by rw [hstabP]
      _ = od.p := hAQindex
  have hTPcard : ∀ T : OrbP, Nat.card T.1 = od.p := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    rw [← hq]
    exact (Subgroup.card_map_of_injective (MulAut.conj (q : G)).injective).trans
      od.P_card
  have hTPleA : ∀ T : OrbP, T.1 ≤ od.A := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    intro y hy
    have hySmul : y ∈ q • od.P := (le_of_eq hq.symm) hy
    rcases Subgroup.mem_map.mp hySmul with ⟨p, hp, rfl⟩
    let pQ : QG := ⟨p, hPleQ hp⟩
    have hpAQ : pQ ∈ AQ := Subgroup.mem_subgroupOf.mpr (hPleA hp)
    exact Subgroup.mem_subgroupOf.mp (hAQnormal.conj_mem pQ hpAQ q)
  have hPneZG : od.P ≠ ZG := by
    intro hPZ
    have hFQnormal : FQ.Normal := by
      refine ⟨?_⟩
      intro p hp q
      have hpZ : (p : G) ∈ ZG := by
        rw [← hPZ]
        exact Subgroup.mem_subgroupOf.mp hp
      rcases Subgroup.mem_map.mp hpZ with ⟨z, hz, hzp⟩
      have hcomm := Subgroup.mem_center_iff.mp hz q
      have hconj : q * p * q⁻¹ = p := by
        apply Subtype.ext
        have hcommG : (q : G) * (z : G) = (z : G) * (q : G) :=
          congrArg Subtype.val hcomm
        calc
          ((q * p * q⁻¹ : QG) : G) = (q : G) * (p : G) * (q : G)⁻¹ := rfl
          _ = (q : G) * (z : G) * (q : G)⁻¹ := by
            exact congrArg (fun a : G => (q : G) * a * (q : G)⁻¹) hzp.symm
          _ = (z : G) := by rw [hcommG]; simp
          _ = (p : G) := hzp
      rw [hconj]
      exact hp
    have hnormTop : Subgroup.normalizer (FQ : Set QG) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hFQnormal
    have hAQtop : AQ = ⊤ := hnormFQ.symm.trans hnormTop
    have hAQneTop : AQ ≠ ⊤ := by
      intro htop
      apply hstrict.2.1.ne
      apply le_antisymm hAleQ
      intro x hx
      have hxAQ : (⟨x, hx⟩ : QG) ∈ AQ := by rw [htop]; simp
      exact Subgroup.mem_subgroupOf.mp hxAQ
    exact hAQneTop hAQtop
  have hTPneZ : ∀ T : OrbP, T.1 ≠ ZG := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    intro hTZ
    apply hPneZG
    apply Subgroup.eq_of_le_of_card_ge
    · intro p hp
      have hconjP : (q : G) * p * (q : G)⁻¹ ∈ q • od.P :=
        (mem_q_smul_iff q ((q : G) * p * (q : G)⁻¹) od.P).mpr
          (by simpa [mul_assoc] using hp)
      have hconjZ : (q : G) * p * (q : G)⁻¹ ∈ ZG :=
        (le_of_eq hTZ) ((le_of_eq hq) hconjP)
      have hqU : (q : G) ∈ c.U :=
        fittingSubgroupOf_le c.U (secondCase_linear_omega_QG_le_FU c w d od q.2)
      have hback := hZnormalU.2 (q : G)⁻¹ (c.U.inv_mem hqU)
        ((q : G) * p * (q : G)⁻¹) hconjZ
      simpa [mul_assoc] using hback
    · rw [od.P_card, hZGcard]
  let PairsP := Σ T : OrbP, {x : T.1 // x ≠ 1}
  let targetA := {x : od.A // (x : G) ∉ ZG}
  let fP : PairsP → targetA := fun a =>
    ⟨⟨(a.2 : G), hTPleA a.1 a.2.1.2⟩, by
      intro hxZ
      have hxNe : (a.2 : G) ≠ 1 := fun h1 => a.2.2 (Subtype.ext h1)
      have hTZ : a.1.1 = ZG :=
        subgroup_eq_of_card_eq_prime_of_common_ne_one od.hp_prime
          a.1.1 ZG (hTPcard a.1) hZGcard a.2.1.2 hxZ hxNe
      exact hTPneZ a.1 hTZ⟩
  have hfPInj : Function.Injective fP := by
    rintro ⟨T, x⟩ ⟨S, y⟩ hxy
    have hvalG : (x : G) = (y : G) :=
      congrArg (fun z : targetA => ((z.1 : od.A) : G)) hxy
    have hyNe : (y : G) ≠ 1 := fun h1 => y.2 (Subtype.ext h1)
    have hxNe : (x : G) ≠ 1 := fun h1 => hyNe (hvalG.symm.trans h1)
    have hxS : (x : G) ∈ S.1 := by rw [hvalG]; exact y.1.2
    have hTS : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one od.hp_prime
        T.1 S.1 (hTPcard T) (hTPcard S) x.1.2 hxS hxNe
    have hOrbEq : T = S := Subtype.ext hTS
    subst S
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvalG
    rw [hxy']
  have htargetCard : Nat.card targetA = od.p ^ 2 - od.p := by
    let : Fintype od.A := Fintype.ofFinite od.A
    let : Fintype targetA := Fintype.ofFinite targetA
    have hZF : Fintype.card (ZG.subgroupOf od.A) = od.p := by
      simpa [Nat.card_eq_fintype_card, hZGcard] using
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZlt.le).toEquiv)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    change Fintype.card od.A - Fintype.card (ZG.subgroupOf od.A) = _
    rw [show Fintype.card od.A = od.p ^ 2 by
      simpa [Nat.card_eq_fintype_card] using od.A_card, hZF]
  have hPairsCard : Nat.card PairsP = od.p ^ 2 - od.p := by
    let : Fintype OrbP := Fintype.ofFinite OrbP
    rw [Nat.card_sigma]
    have hfiber : ∀ T : OrbP, Nat.card {x : T.1 // x ≠ 1} = od.p - 1 := by
      intro T
      let : Fintype T.1 := Fintype.ofFinite T.1
      let : Fintype {x : T.1 // x ≠ 1} := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp [show Fintype.card T.1 = od.p by
        simpa [Nat.card_eq_fintype_card] using hTPcard T]
    calc
      (∑ T : OrbP, Nat.card {x : T.1 // x ≠ 1}) =
          ∑ _T : OrbP, (od.p - 1) := by
        apply Finset.sum_congr rfl
        intro T _hT
        exact hfiber T
      _ = Nat.card OrbP * (od.p - 1) := by
        simp [Nat.card_eq_fintype_card]
      _ = od.p * (od.p - 1) := by rw [hOrbPcard]
      _ = od.p * od.p - od.p * 1 := Nat.mul_sub_left_distrib od.p od.p 1
      _ = od.p ^ 2 - od.p := by rw [pow_two, Nat.mul_one]
  have hfPSurj : Function.Surjective fP :=
    ((Nat.bijective_iff_injective_and_card fP).mpr
      ⟨hfPInj, hPairsCard.trans htargetCard.symm⟩).2
  have hNormalizer : normalizerIn c.U od.A ≤ od.B ⊔ od.K ⊔ c.FU := by
    intro x hx
    let xU : c.U := ⟨x, hx.1⟩
    let Px : Subgroup G := xU • od.P
    have hPxcard : Nat.card Px = od.p :=
      (Subgroup.card_map_of_injective (MulAut.conj x).injective).trans od.P_card
    have hxAeq : xU • od.A = od.A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hx.2
    have hPxleA : Px ≤ od.A := by
      calc Px = xU • od.P := rfl
        _ ≤ xU • od.A := Subgroup.map_mono hPleA
        _ = od.A := hxAeq
    have hPxneZ : Px ≠ ZG := by
      intro hPxZ
      apply hPneZG
      apply Subgroup.eq_of_le_of_card_ge
      · intro p hp
        have hconjPx : x * p * x⁻¹ ∈ Px :=
          (by
            change x * p * x⁻¹ ∈ od.P.map (MulAut.conj x).toMonoidHom
            exact Subgroup.mem_map_of_mem _ hp)
        have hconjZ : x * p * x⁻¹ ∈ ZG := (le_of_eq hPxZ) hconjPx
        have hback := hZnormalU.2 x⁻¹ (c.U.inv_mem hx.1) (x * p * x⁻¹) hconjZ
        simpa [mul_assoc] using hback
      · rw [od.P_card, hZGcard]
    have hPxneBot : Px ≠ ⊥ := by
      intro hbot
      have := hPxcard
      rw [hbot] at this
      exact od.hp_prime.ne_one (by simpa using this.symm)
    let a : Px := Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp hPxneBot)
    have haNe : a ≠ 1 :=
      Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp hPxneBot)
    have haGNe : (a : G) ≠ 1 := fun h1 => haNe (Subtype.ext h1)
    have haNotZ : (a : G) ∉ ZG := by
      intro haZ
      apply hPxneZ
      exact subgroup_eq_of_card_eq_prime_of_common_ne_one od.hp_prime
        Px ZG hPxcard hZGcard a.2 haZ haGNe
    let aTarget : targetA := ⟨⟨(a : G), hPxleA a.2⟩, haNotZ⟩
    obtain ⟨pair, hpair⟩ := hfPSurj aTarget
    rcases pair with ⟨T, y⟩
    have hvalG : (a : G) = (y : G) :=
      congrArg (fun z : targetA => ((z.1 : od.A) : G)) hpair.symm
    have haT : (a : G) ∈ T.1 := by rw [hvalG]; exact y.1.2
    have hPxT : Px = T.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one od.hp_prime
        Px T.1 hPxcard (hTPcard T) a.2 haT haGNe
    rcases T.2 with ⟨q, hq⟩
    have hPxEq : Px = q • od.P := hPxT.trans hq.symm
    let qU : c.U := ⟨(q : G),
      (fittingSubgroupOf_le c.U)
        (secondCase_linear_omega_QG_le_FU c w d od q.2)⟩
    have hqAction : qU • od.P = q • od.P := rfl
    let rU : c.U := qU⁻¹ * xU
    have hrStab : rU • od.P = od.P := by
      change (qU⁻¹ * xU) • od.P = od.P
      rw [mul_smul]
      change qU⁻¹ • Px = od.P
      rw [hPxEq, ← hqAction, ← mul_smul]
      simp
    have hrNorm : (rU : G) ∈ Subgroup.normalizer (od.P : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hrStab
    have hrNU : (rU : G) ∈ normalizerIn c.U od.P := ⟨rU.2, hrNorm⟩
    have hrKB : (rU : G) ∈ od.K ⊔ od.B := by
      rw [secondCase_linear_omega_NU_P_eq_U_inter_M c w d od,
        ← od.U_inter_M_eq] at hrNU
      exact hrNU
    have hrL : (rU : G) ∈ od.B ⊔ od.K ⊔ c.FU := by
      exact (sup_le
        ((le_sup_right : od.K ≤ od.B ⊔ od.K).trans le_sup_left)
        ((le_sup_left : od.B ≤ od.B ⊔ od.K).trans le_sup_left)) hrKB
    have hqL : (q : G) ∈ od.B ⊔ od.K ⊔ c.FU :=
      Subgroup.mem_sup_right
        (secondCase_linear_omega_QG_le_FU c w d od q.2)
    have hxEq : x = (q : G) * (rU : G) := by
      dsimp [rU, qU, xU]
      group
    rw [hxEq]
    exact (od.B ⊔ od.K ⊔ c.FU).mul_mem hqL hrL
  have hpodd : Odd od.p := secondCase_linear_omega_p_odd c w d od
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hnormLe : (normalizerIn c.U od.A).relIndex c.U ≤ od.p + 1 := by
    apply conjugate_orbit_le_p_add_one (U := c.U) (Q := QG) (A := od.A)
      (p := od.p) hAleQ hQnormalU od.A_card hQcard hZGcard hAZlt.le
  have hnormLeP : (normalizerIn c.U od.A).relIndex c.U ≤ od.p :=
    odd_relIndex_le_of_le_add_one (normalizerIn c.U od.A) c.U hUodd hpodd hnormLe
  have hnormNe : (normalizerIn c.U od.A).relIndex c.U ≠ 0 := by
    let N : Subgroup G := c.U ⊓ Subgroup.normalizer (od.A : Set G)
    have hN : N = normalizerIn c.U od.A := rfl
    rw [← hN]
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_pos.ne'
  exact ⟨hnormLeP,
    (Subgroup.relIndex_le_of_le_left hNormalizer hnormNe).trans hnormLeP⟩

/-- In the strict branch, the `U`-normalizer index of `A` is at most `p`. -/
public theorem secondCase_linear_omega_strict_normalizerIndex_le_p
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hstrict :
      (Subgroup.center (od.Q.map c.U.subtype)).map
          (od.Q.map c.U.subtype).subtype < od.A ∧
      od.A < od.Q.map c.U.subtype ∧
      (od.A.subgroupOf (od.Q.map c.U.subtype)).index = od.p) :
    (normalizerIn c.U od.A).relIndex c.U ≤ od.p :=
  (secondCase_linear_omega_strict_index_bounds c w d od hstrict).1

/-- In the strict branch, equation (8)'s reflected-layer index is at most
`p`. -/
public theorem secondCase_linear_omega_strict_relIndex_le_p
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d)
    (hstrict :
      (Subgroup.center (od.Q.map c.U.subtype)).map
          (od.Q.map c.U.subtype).subtype < od.A ∧
      od.A < od.Q.map c.U.subtype ∧
      (od.A.subgroupOf (od.Q.map c.U.subtype)).index = od.p) :
    (od.B ⊔ od.K ⊔ c.FU).relIndex c.U ≤ od.p :=
  (secondCase_linear_omega_strict_index_bounds c w d od hstrict).2

end CFSG.GorensteinWalter
