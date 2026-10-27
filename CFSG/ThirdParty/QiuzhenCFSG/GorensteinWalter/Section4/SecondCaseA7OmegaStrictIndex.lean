module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaCenter
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddRelativeIndexBound
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27IndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaFNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The strict order-27 branch of the A7 omega index argument -/

open scoped Pointwise

noncomputable section

namespace CFSG.GorensteinWalter

universe u

local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)

/-- In the strict order-27 omega branch, equation (8) holds:
`B ⊔ F(U)` has relative index at most three in `U`. -/
public theorem secondCase_a7_omega_strict_relIndex_le_three
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hAltQ : od.K ⊔ od.F < od.Q.map c.FU.subtype) :
    (od.B ⊔ c.FU).relIndex c.U ≤ 3 := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  let U : Subgroup G := c.U
  let ZQ : Subgroup QG := Subgroup.center QG
  let ZG : Subgroup G := ZQ.map QG.subtype
  let : MulAction U (Subgroup G) :=
    MulAction.compHom (Subgroup G) U.subtype
  have hAleQ : A ≤ QG := hAltQ.le
  have hFleA : od.F ≤ A := le_sup_right
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  have hQGleU : QG ≤ U :=
    hQGleFU.trans (fittingSubgroupOf_le c.U)
  have hAcard : Nat.card A = 9 := by
    change Nat.card (od.K ⊔ od.F : Subgroup G) = 9
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hQcard : Nat.card QG = 27 := by
    simpa [QG] using
      secondCase_a7_omega_card_eq_twenty_seven_of_lt c w d od hAltQ
  have hZQcard : Nat.card ZQ = 3 := by
    simpa [QG, ZQ] using
      secondCase_a7_omega_center_card_eq_three_of_lt c w d od hAltQ
  have hZGcard : Nat.card ZG = 3 := by
    calc
      Nat.card ZG = Nat.card ZQ :=
        Subgroup.card_map_of_injective QG.subtype_injective
      _ = 3 := hZQcard
  let FQ : Subgroup QG := od.F.subgroupOf QG
  let AQ : Subgroup QG := A.subgroupOf QG
  have hAQcard : Nat.card AQ = 9 := by
    calc
      Nat.card AQ = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleQ).toEquiv
      _ = 9 := hAcard
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    simpa [A, QG, FQ, AQ] using
      secondCase_a7_omega_normalizer_F_eq c w d od hAleQ
  have hZQleAQ : ZQ ≤ AQ := by
    change Subgroup.center QG ≤ AQ
    rw [← hnormFQ]
    exact Subgroup.center_le_normalizer (FQ : Set QG)
  have hAQindex : AQ.index = 3 := by
    have hmul := Subgroup.card_mul_index AQ
    rw [hAQcard, hQcard] at hmul
    omega
  have hAQnormal : AQ.Normal := by
    apply Subgroup.normal_of_index_eq_minFac_card
    rw [hAQindex, hQcard]
    norm_num
  have hZGleA : ZG ≤ A := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨zq, hzq, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hZQleAQ hzq)
  have hQnormalU : IsNormalIn QG U := by
    change IsNormalIn (od.Q.map c.FU.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn od.Q
      od.Q_characteristic (fittingSubgroupOf_isNormalIn c.U)
  have hZnormalU : IsNormalIn ZG U := by
    exact map_characteristic_isNormalIn_of_isNormalIn ZQ
      Subgroup.centerCharacteristic hQnormalU
  have mem_smul_iff (x : U) (y : G) (T : Subgroup G) :
      y ∈ x • T ↔ (x : G)⁻¹ * y * (x : G) ∈ T := by
    change y ∈ T.map (MulAut.conj (x : G)).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  let Orb := MulAction.orbit U A
  have hTcard : ∀ T : Orb, Nat.card T.1 = 9 := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    have hcard : Nat.card ↥(u • A : Subgroup G) = Nat.card A := by
      change Nat.card (A.map (MulAut.conj (u : G)).toMonoidHom) = Nat.card A
      exact Subgroup.card_map_of_injective (MulAut.conj (u : G)).injective
    rw [← hu]
    exact hcard.trans hAcard
  have hTleQ : ∀ T : Orb, T.1 ≤ QG := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    intro y hy
    have hySmul : y ∈ u • A := by
      change y ∈ (fun m : U => m • A) u
      rw [hu]
      exact hy
    have hpre : (u : G)⁻¹ * y * (u : G) ∈ A :=
      (mem_smul_iff u y A).mp hySmul
    have hpreQ : (u : G)⁻¹ * y * (u : G) ∈ QG := hAleQ hpre
    have hconjQ := hQnormalU.2 (u : G) u.2
      ((u : G)⁻¹ * y * (u : G)) hpreQ
    simpa [mul_assoc] using hconjQ
  have hZleT : ∀ T : Orb, ZG ≤ T.1 := by
    intro T
    rcases T.2 with ⟨u, hu⟩
    intro z hz
    have hpreZ : (u : G)⁻¹ * z * (u : G) ∈ ZG := by
      have hconj := hZnormalU.2 (u : G)⁻¹ (U.inv_mem u.2) z hz
      simpa using hconj
    have hzSmul : z ∈ u • A :=
      (mem_smul_iff u z A).mpr (hZGleA hpreZ)
    rw [← hu]
    exact hzSmul
  let Pairs := Σ T : Orb, {x : T.1 // (x : G) ∉ ZG}
  let target := {x : QG // x ∉ ZQ}
  let f : Pairs → target := fun p =>
    ⟨⟨(p.2 : G), hTleQ p.1 p.2.1.2⟩,
      by
        intro hzq
        apply p.2.2
        exact Subgroup.mem_map.mpr ⟨⟨(p.2 : G), hTleQ p.1 p.2.1.2⟩,
          hzq, rfl⟩⟩
  have hfInj : Function.Injective f := by
    rintro ⟨T, x⟩ ⟨S, y⟩ hxy
    have hvalG : (x : G) = (y : G) :=
      congrArg (fun z : target => ((z.1 : QG) : G)) hxy
    have hxS : (x : G) ∈ S.1 := by
      rw [hvalG]
      exact y.1.2
    let I : Subgroup G := T.1 ⊓ S.1
    have hZleI : ZG ≤ I := le_inf (hZleT T) (hZleT S)
    have hxI : (x : G) ∈ I := ⟨x.1.2, hxS⟩
    have hZneI : ZG ≠ I := by
      intro hZI
      apply x.2
      exact (le_of_eq hZI.symm) hxI
    have hZltI : ZG < I := lt_of_le_of_ne hZleI hZneI
    have hIcardGt : 3 < Nat.card I := by
      rw [← hZGcard]
      exact natCard_lt_of_subgroup_lt hZltI
    have hIdiv : Nat.card I ∣ 3 ^ 2 := by
      norm_num
      rw [← hTcard T]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hIcard⟩ :=
      (Nat.dvd_prime_pow Nat.prime_three).mp hIdiv
    have hkTwo : k = 2 := by
      rw [hIcard] at hIcardGt
      have hkGt : 1 < k :=
        (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (by
          simpa using hIcardGt)
      omega
    have hIcardNine : Nat.card I = 9 := by
      rw [hIcard, hkTwo]
      norm_num
    have hIT : I = T.1 := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hIcardNine, hTcard T]
    have hIS : I = S.1 := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right
      rw [hIcardNine, hTcard S]
    have hTS : T.1 = S.1 := hIT.symm.trans hIS
    have hOrbEq : T = S := Subtype.ext hTS
    subst S
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvalG
    rw [hxy']
  have htargetCard : Nat.card target = 24 := by
    let : Fintype QG := Fintype.ofFinite QG
    let : Fintype target := Fintype.ofFinite target
    have hQF : Fintype.card QG = 27 := by
      simpa [Nat.card_eq_fintype_card] using hQcard
    have hZF : Fintype.card ZQ = 3 := by
      simpa [Nat.card_eq_fintype_card] using hZQcard
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    change Fintype.card QG - Fintype.card ZQ = 24
    rw [hQF, hZF]
  have hpairCard : Nat.card Pairs = Nat.card Orb * 6 := by
    let : Fintype Orb := Fintype.ofFinite Orb
    rw [Nat.card_sigma]
    have hfiber : ∀ T : Orb,
        Nat.card {x : T.1 // (x : G) ∉ ZG} = 6 := by
      intro T
      let : Fintype T.1 := Fintype.ofFinite T.1
      let : Fintype {x : T.1 // (x : G) ∉ ZG} := Fintype.ofFinite _
      have hTF : Fintype.card T.1 = 9 := by
        simpa [Nat.card_eq_fintype_card] using hTcard T
      have hZTF : Fintype.card (ZG.subgroupOf T.1) = 3 := by
        have hcard : Nat.card (ZG.subgroupOf T.1) = Nat.card ZG :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZleT T)).toEquiv
        simpa [Nat.card_eq_fintype_card, hZGcard] using hcard
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      change Fintype.card T.1 - Fintype.card (ZG.subgroupOf T.1) = 6
      rw [hTF, hZTF]
    simp_rw [hfiber]
    simp [mul_comm]
  have hOrbLe : Nat.card Orb ≤ 4 := by
    have hpairsLe : Nat.card Pairs ≤ Nat.card target :=
      Nat.card_le_card_of_injective f hfInj
    rw [hpairCard, htargetCard] at hpairsLe
    omega
  let NU : Subgroup U := (Subgroup.normalizer (A : Set G)).comap U.subtype
  have hstab : MulAction.stabilizer U A = NU := by
    ext u
    rw [MulAction.mem_stabilizer_iff]
    change u • A = A ↔ (u : G) ∈ Subgroup.normalizer (A : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rfl
  have hOrbIndex : Nat.card Orb = NU.index := by
    calc
      Nat.card Orb = Nat.card (U ⧸ MulAction.stabilizer U A) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer U A)
      _ = (MulAction.stabilizer U A).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer U A)).symm
      _ = NU.index := by rw [hstab]
  have hNUindexLe : NU.index ≤ 4 := by
    rw [← hOrbIndex]
    exact hOrbLe
  let N : Subgroup G := U ⊓ Subgroup.normalizer (A : Set G)
  have hNsub : N.subgroupOf U = NU := by
    ext x
    simp [N, NU]
  have hNrel : N.relIndex U = NU.index := by
    change (N.subgroupOf U).index = NU.index
    rw [hNsub]
  have hUodd : Odd (Nat.card U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hNrelLe : N.relIndex U ≤ 3 := by
    apply odd_relIndex_le_three_of_le_four N U hUodd
    rw [hNrel]
    exact hNUindexLe
  have mem_q_smul_iff (q : QG) (y : G) (T : Subgroup G) :
      y ∈ q • T ↔ (q : G)⁻¹ * y * (q : G) ∈ T := by
    change y ∈ T.map (MulAut.conj (q : G)).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  let OrbF := MulAction.orbit QG od.F
  have hstabF : MulAction.stabilizer QG od.F = AQ := by
    ext q
    rw [MulAction.mem_stabilizer_iff]
    change od.F.map (MulAut.conj (q : G)).toMonoidHom = od.F ↔
      (q : G) ∈ A
    constructor
    · intro hmap
      have hqM : (q : G) ∈ w.M := by
        rw [← od.F_normalizer]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap
      change (q : G) ∈ od.K ⊔ od.F
      rw [od.FU_inter_M_eq]
      exact ⟨hQGleFU q.2, hqM⟩
    · intro hqA
      change (q : G) ∈ od.K ⊔ od.F at hqA
      rw [od.FU_inter_M_eq] at hqA
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
      rw [od.F_normalizer]
      exact hqA.2
  have hOrbFcard : Nat.card OrbF = 3 := by
    calc
      Nat.card OrbF =
          Nat.card (QG ⧸ MulAction.stabilizer QG od.F) :=
        Nat.card_congr
          (MulAction.orbitEquivQuotientStabilizer QG od.F)
      _ = (MulAction.stabilizer QG od.F).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer QG od.F)).symm
      _ = AQ.index := by rw [hstabF]
      _ = 3 := hAQindex
  have hTFcard : ∀ T : OrbF, Nat.card T.1 = 3 := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    have hcard : Nat.card ↥(q • od.F : Subgroup G) = Nat.card od.F := by
      change Nat.card (od.F.map (MulAut.conj (q : G)).toMonoidHom) =
        Nat.card od.F
      exact Subgroup.card_map_of_injective (MulAut.conj (q : G)).injective
    rw [← hq]
    exact hcard.trans od.F_card
  have hTFleA : ∀ T : OrbF, T.1 ≤ A := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    intro y hy
    have hySmul : y ∈ q • od.F := by
      change y ∈ (fun m : QG => m • od.F) q
      rw [hq]
      exact hy
    rcases Subgroup.mem_map.mp hySmul with ⟨f, hf, rfl⟩
    let fQ : QG := ⟨f, hAleQ (hFleA hf)⟩
    have hfAQ : fQ ∈ AQ :=
      Subgroup.mem_subgroupOf.mpr (hFleA hf)
    exact Subgroup.mem_subgroupOf.mp
      (hAQnormal.conj_mem fQ hfAQ q)
  have hFneZG : od.F ≠ ZG := by
    intro hFZ
    have hFQleZQ : FQ ≤ ZQ := by
      intro f hf
      have hfZG : (f : G) ∈ ZG := by
        rw [← hFZ]
        exact Subgroup.mem_subgroupOf.mp hf
      rcases Subgroup.mem_map.mp hfZG with ⟨z, hz, hzf⟩
      have hfz : f = z := Subtype.ext hzf.symm
      rw [hfz]
      exact hz
    have hFQnormal : FQ.Normal := by
      refine ⟨?_⟩
      intro f hf q
      have hcomm := Subgroup.mem_center_iff.mp (hFQleZQ hf) q
      have hconj : q * f * q⁻¹ = f := by
        rw [hcomm]
        simp
      rw [hconj]
      exact hf
    have hnormTop : Subgroup.normalizer (FQ : Set QG) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hFQnormal
    have hAQtop : AQ = ⊤ := hnormFQ.symm.trans hnormTop
    have hAQneTop : AQ ≠ ⊤ := by
      intro htop
      apply hAltQ.ne
      apply le_antisymm hAleQ
      intro x hx
      have hxAQ : (⟨x, hx⟩ : QG) ∈ AQ := by
        rw [htop]
        simp
      exact Subgroup.mem_subgroupOf.mp hxAQ
    exact hAQneTop hAQtop
  have hTFneZ : ∀ T : OrbF, T.1 ≠ ZG := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    intro hTZ
    apply hFneZG
    apply Subgroup.eq_of_le_of_card_ge
    · intro f hf
      have hconjSmul : (q : G) * f * (q : G)⁻¹ ∈ q • od.F :=
        (mem_q_smul_iff q ((q : G) * f * (q : G)⁻¹) od.F).mpr
          (by simpa [mul_assoc] using hf)
      have hconjT : (q : G) * f * (q : G)⁻¹ ∈ T.1 :=
        (le_of_eq hq) hconjSmul
      have hconjZ : (q : G) * f * (q : G)⁻¹ ∈ ZG :=
        (le_of_eq hTZ) hconjT
      rcases Subgroup.mem_map.mp hconjZ with ⟨z, hz, hzval⟩
      have hzval' : (z : G) = (q : G) * f * (q : G)⁻¹ := hzval
      have hcomm := Subgroup.mem_center_iff.mp hz q
      have hcommG : (q : G) * (z : G) = (z : G) * (q : G) :=
        congrArg Subtype.val hcomm
      have hfz : f = (z : G) := by
        calc
          f = (q : G)⁻¹ * ((q : G) * f * (q : G)⁻¹) * (q : G) := by
            group
          _ = (q : G)⁻¹ * (z : G) * (q : G) := by rw [← hzval']
          _ = (z : G) := by
            rw [mul_assoc, ← hcommG]
            group
      exact Subgroup.mem_map.mpr ⟨z, hz, hfz.symm⟩
    · rw [od.F_card, hZGcard]
  let PairsF := Σ T : OrbF, {x : T.1 // x ≠ 1}
  let targetA := {x : A // (x : G) ∉ ZG}
  let fF : PairsF → targetA := fun p =>
    ⟨⟨(p.2 : G), hTFleA p.1 p.2.1.2⟩,
      by
        intro hxZ
        have hxGne : (p.2 : G) ≠ 1 := by
          intro h1
          apply p.2.2
          exact Subtype.ext h1
        have hTZ : p.1.1 = ZG :=
          subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
            p.1.1 ZG (hTFcard p.1) hZGcard p.2.1.2 hxZ hxGne
        exact hTFneZ p.1 hTZ⟩
  have hfFInj : Function.Injective fF := by
    rintro ⟨T, x⟩ ⟨S, y⟩ hxy
    have hvalG : (x : G) = (y : G) :=
      congrArg (fun z : targetA => ((z.1 : A) : G)) hxy
    have hyGne : (y : G) ≠ 1 := by
      intro h1
      apply y.2
      exact Subtype.ext h1
    have hxGne : (x : G) ≠ 1 := fun h1 =>
      hyGne (hvalG.symm.trans h1)
    have hxS : (x : G) ∈ S.1 := by
      rw [hvalG]
      exact y.1.2
    have hTS : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        T.1 S.1 (hTFcard T) (hTFcard S) x.1.2 hxS hxGne
    have hOrbEq : T = S := Subtype.ext hTS
    subst S
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hvalG
    rw [hxy']
  have htargetAcard : Nat.card targetA = 6 := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype targetA := Fintype.ofFinite targetA
    have hAF : Fintype.card A = 9 := by
      simpa [Nat.card_eq_fintype_card] using hAcard
    have hZAF : Fintype.card (ZG.subgroupOf A) = 3 := by
      have hcard : Nat.card (ZG.subgroupOf A) = Nat.card ZG :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZGleA).toEquiv
      simpa [Nat.card_eq_fintype_card, hZGcard] using hcard
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    change Fintype.card A - Fintype.card (ZG.subgroupOf A) = 6
    rw [hAF, hZAF]
  have hPairsFcard : Nat.card PairsF = 6 := by
    let : Fintype OrbF := Fintype.ofFinite OrbF
    rw [Nat.card_sigma]
    have hfiber : ∀ T : OrbF, Nat.card {x : T.1 // x ≠ 1} = 2 := by
      intro T
      let : Fintype T.1 := Fintype.ofFinite T.1
      let : Fintype {x : T.1 // x ≠ 1} := Fintype.ofFinite _
      have hTF : Fintype.card T.1 = 3 := by
        simpa [Nat.card_eq_fintype_card] using hTFcard T
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
      simp [hTF]
    simp_rw [hfiber]
    have hOrbFncard : OrbF.ncard = 3 := hOrbFcard
    simp [hOrbFncard]
  have hfFSurj : Function.Surjective fF :=
    ((Nat.bijective_iff_injective_and_card fF).mpr
      ⟨hfFInj, hPairsFcard.trans htargetAcard.symm⟩).2
  have hNleL : N ≤ od.B ⊔ c.FU := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hxNormA : x ∈ Subgroup.normalizer (A : Set G) := hx.2
    let xU : U := ⟨x, hxU⟩
    let Fx : Subgroup G := xU • od.F
    have hFxcard : Nat.card Fx = 3 := by
      change Nat.card (od.F.map (MulAut.conj x).toMonoidHom) = 3
      exact (Subgroup.card_map_of_injective (MulAut.conj x).injective).trans
        od.F_card
    have hxAeq : xU • A = A := by
      change A.map (MulAut.conj x).toMonoidHom = A
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hxNormA
    have hFxleA : Fx ≤ A := by
      calc
        Fx = xU • od.F := rfl
        _ ≤ xU • A := Subgroup.map_mono hFleA
        _ = A := hxAeq
    have hFxneZ : Fx ≠ ZG := by
      intro hFxZ
      apply hFneZG
      apply Subgroup.eq_of_le_of_card_ge
      · intro f hf
        have hconjSmul : x * f * x⁻¹ ∈ xU • od.F :=
          (mem_smul_iff xU (x * f * x⁻¹) od.F).mpr
            (by simpa [xU, mul_assoc] using hf)
        have hconjFx : x * f * x⁻¹ ∈ Fx := hconjSmul
        have hconjZ : x * f * x⁻¹ ∈ ZG :=
          (le_of_eq hFxZ) hconjFx
        have hback := hZnormalU.2 x⁻¹ (U.inv_mem hxU)
          (x * f * x⁻¹) hconjZ
        simpa [mul_assoc] using hback
      · rw [od.F_card, hZGcard]
    have hFxneBot : Fx ≠ ⊥ := by
      intro hbot
      have hcard := hFxcard
      rw [hbot] at hcard
      norm_num at hcard
    let a : Fx :=
      Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp hFxneBot)
    have haNe : a ≠ 1 :=
      Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp hFxneBot)
    have haGNe : (a : G) ≠ 1 := by
      intro h1
      apply haNe
      exact Subtype.ext h1
    have haNotZ : (a : G) ∉ ZG := by
      intro haZ
      apply hFxneZ
      exact subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        Fx ZG hFxcard hZGcard a.2 haZ haGNe
    let aTarget : targetA :=
      ⟨⟨(a : G), hFxleA a.2⟩, haNotZ⟩
    obtain ⟨p, hp⟩ := hfFSurj aTarget
    rcases p with ⟨T, y⟩
    have hvalG : (a : G) = (y : G) :=
      congrArg (fun z : targetA => ((z.1 : A) : G)) hp.symm
    have haT : (a : G) ∈ T.1 := by
      rw [hvalG]
      exact y.1.2
    have hFxT : Fx = T.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        Fx T.1 hFxcard (hTFcard T) a.2 haT haGNe
    rcases T.2 with ⟨q, hq⟩
    have hFxEq : Fx = q • od.F := hFxT.trans hq.symm
    let qU : U := ⟨(q : G), hQGleU q.2⟩
    have hqAction : qU • od.F = q • od.F := rfl
    let rU : U := qU⁻¹ * xU
    have hrStab : rU • od.F = od.F := by
      change (qU⁻¹ * xU) • od.F = od.F
      rw [mul_smul]
      change qU⁻¹ • Fx = od.F
      rw [hFxEq, ← hqAction, ← mul_smul]
      simp
    have hrNorm : (rU : G) ∈ Subgroup.normalizer (od.F : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      exact hrStab
    have hrM : (rU : G) ∈ w.M := by
      rw [← od.F_normalizer]
      exact hrNorm
    have hrKB : (rU : G) ∈ od.K ⊔ od.B := by
      rw [od.U_inter_M_eq]
      exact ⟨rU.2, hrM⟩
    have hKleFU : od.K ≤ c.FU := by
      calc
        od.K ≤ od.K ⊔ od.F := le_sup_left
        _ = c.FU ⊓ w.M := od.FU_inter_M_eq
        _ ≤ c.FU := inf_le_left
    have hKBle : od.K ⊔ od.B ≤ od.B ⊔ c.FU :=
      sup_le (hKleFU.trans le_sup_right) le_sup_left
    have hrL : (rU : G) ∈ od.B ⊔ c.FU := hKBle hrKB
    have hqL : (q : G) ∈ od.B ⊔ c.FU :=
      Subgroup.mem_sup_right (hQGleFU q.2)
    have hxEq : x = (q : G) * (rU : G) := by
      dsimp [rU, qU, xU]
      group
    rw [hxEq]
    exact (od.B ⊔ c.FU).mul_mem hqL hrL
  have hNrelne : N.relIndex U ≠ 0 := by
    rw [hNrel]
    exact Nat.card_pos.ne'
  exact (Subgroup.relIndex_le_of_le_left hNleL hNrelne).trans hNrelLe

end CFSG.GorensteinWalter
