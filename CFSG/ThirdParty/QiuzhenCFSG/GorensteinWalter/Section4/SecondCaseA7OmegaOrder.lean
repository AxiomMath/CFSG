module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaFixedDichotomy
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaFNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # The order-27 branch of the A7 omega argument -/

open scoped Pointwise commutatorElement

noncomputable section

namespace CFSG.GorensteinWalter

universe u

local instance {X : Type*} [Group X] : MulAction X (Subgroup X) :=
  MulAction.compHom (Subgroup X) (MulAut.conj : X →* MulAut X)

/-- If the equation-(6) subgroup is properly contained in the omega subgroup,
then the latter has order `27`. -/
public theorem secondCase_a7_omega_card_eq_twenty_seven_of_lt
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d)
    (hAltQ : od.K ⊔ od.F < od.Q.map c.FU.subtype) :
    Nat.card (od.Q.map c.FU.subtype) = 27 := by
  classical
  let A : Subgroup G := od.K ⊔ od.F
  let QG : Subgroup G := od.Q.map c.FU.subtype
  have hAleQ : A ≤ QG := hAltQ.le
  have hne : A ≠ QG := hAltQ.ne
  have hQGleFU : QG ≤ c.FU := Subgroup.map_subtype_le od.Q
  have hAcard : Nat.card A = 9 := by
    change Nat.card (od.K ⊔ od.F : Subgroup G) = 9
    rw [od.FU_inter_M_eq]
    exact od.FU_inter_M_card
  have hFleA : od.F ≤ A := le_sup_right
  have hFleQ : od.F ≤ QG := hFleA.trans hAleQ
  let FQ : Subgroup QG := od.F.subgroupOf QG
  let AQ : Subgroup QG := A.subgroupOf QG
  have hFQcard : Nat.card FQ = 3 := by
    calc
      Nat.card FQ = Nat.card od.F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleQ).toEquiv
      _ = 3 := od.F_card
  have hAQcard : Nat.card AQ = 9 := by
    calc
      Nat.card AQ = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleQ).toEquiv
      _ = 9 := hAcard
  have hQGp : IsPGroup 3 QG := by
    have hQsubp : IsPGroup 3 (QG.subgroupOf c.FU) :=
      od.FU_isPGroup.to_subgroup (QG.subgroupOf c.FU)
    exact hQsubp.of_equiv (Subgroup.subgroupOfEquivOfLe hQGleFU)
  have mem_smul_iff (x y : QG) (T : Subgroup QG) :
      y ∈ x • T ↔ x⁻¹ * y * x ∈ T := by
    change y ∈ T.map (MulAut.conj x).toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have hconjFleA : ∀ q : G, q ∈ QG → ∀ f : G, f ∈ od.F →
      q * f * q⁻¹ ∈ A := by
    intro q hq f hf
    rcases Subgroup.mem_map.mp hq with ⟨q0, hq0, hqval⟩
    let qR : c.FU := ⟨q, hQGleFU hq⟩
    let fR : c.FU := ⟨f, hQGleFU (hFleQ hf)⟩
    have hqRZ2 : qR ∈ Subgroup.upperCentralSeries c.FU 2 := by
      have hq0Z2 := od.Q_le_upperCentralSeries_two hq0
      have hqReq : qR = q0 := Subtype.ext hqval.symm
      rw [hqReq]
      exact hq0Z2
    have hcommCenter : ⁅qR, fR⁆ ∈ Subgroup.center c.FU := by
      have hstep :=
        (Subgroup.mem_upperCentralSeries_succ_iff
          (G := c.FU) (n := 1) (x := qR)).mp hqRZ2 fR
      simpa [Subgroup.upperCentralSeries_one, commutatorElement_def] using hstep
    let z : G := q * f * q⁻¹ * f⁻¹
    have hzQ : z ∈ QG := by
      exact QG.mul_mem (QG.mul_mem (QG.mul_mem hq (hFleQ hf)) (QG.inv_mem hq))
        (QG.inv_mem (hFleQ hf))
    have hzFU : z ∈ c.FU := hQGleFU hzQ
    have hzCentFU : z ∈ Subgroup.centralizer (c.FU : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yR : c.FU := ⟨y, hy⟩
      have hcomm := (Subgroup.mem_center_iff.mp hcommCenter) yR
      exact congrArg Subtype.val hcomm
    have hzNormF : z ∈ Subgroup.normalizer (od.F : Set G) :=
      Subgroup.centralizer_le_normalizer (od.F : Set G)
        ((Subgroup.centralizer_le (SetLike.coe_mono
          (show od.F ≤ c.FU from hFleQ.trans hQGleFU))) hzCentFU)
    have hzM : z ∈ w.M := od.F_normalizer ▸ hzNormF
    have hzA : z ∈ A := by
      change z ∈ od.K ⊔ od.F
      rw [od.FU_inter_M_eq]
      exact ⟨hzFU, hzM⟩
    have hfA : f ∈ A := hFleA hf
    have heq : q * f * q⁻¹ = z * f := by
      dsimp [z]
      group
    rw [heq]
    exact A.mul_mem hzA hfA
  have hnormFQ : Subgroup.normalizer (FQ : Set QG) = AQ := by
    simpa [A, QG, FQ, AQ] using
      secondCase_a7_omega_normalizer_F_eq c w d od hAleQ
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
            (mem_smul_iff x (x * y * x⁻¹) FQ).mpr
              (by simpa [mul_assoc] using hy)
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
  have hTcard : ∀ T : Orb, Nat.card T.1 = 3 := by
    intro T
    rcases T.2 with ⟨q, hq⟩
    have hcard : Nat.card ↥(q • FQ : Subgroup QG) = Nat.card FQ := by
      change Nat.card (FQ.map (MulAut.conj q).toMonoidHom) = Nat.card FQ
      exact Subgroup.card_map_of_injective (MulAut.conj q).injective
    rw [← hq]
    exact hcard.trans hFQcard
  have hTleA : ∀ T : Orb, (T.1.map QG.subtype) ≤ A := by
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
    have hpreF : ((q⁻¹ * yQ * q : QG) : G) ∈ od.F :=
      Subgroup.mem_subgroupOf.mp hpre
    have hconj := hconjFleA (q : G) q.2
      (((q⁻¹ * yQ * q : QG) : G)) hpreF
    simpa [mul_assoc] using hconj
  have hTne : ∀ T : Orb, T.1 ≠ ⊥ := by
    intro T hbot
    have hcard1 : Nat.card T.1 = 1 := by rw [hbot]; simp
    have hcard3 := hTcard T
    omega
  let pick : ∀ T : Orb, T.1 := fun T =>
    Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp (hTne T))
  have pick_ne (T : Orb) : pick T ≠ 1 :=
    Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp (hTne T))
  let target := {x : A // x ≠ 1}
  let f : Orb → target := fun T =>
    ⟨⟨((pick T : T.1) : QG), hTleA T
      (Subgroup.mem_map.mpr ⟨(pick T : T.1), (pick T).2, rfl⟩)⟩,
      by
        intro h1
        apply pick_ne T
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun z : A => (z : G)) h1⟩
  have hfInj : Function.Injective f := by
    intro T S hTS
    have hvalG : ((((f T).1 : A) : G)) = (((f S).1 : A) : G) :=
      congrArg (fun z : target => ((z.1 : A) : G)) hTS
    have hval : ((pick T : T.1) : QG) = ((pick S : S.1) : QG) :=
      Subtype.ext hvalG
    have hpickS_ne : ((pick S : S.1) : QG) ≠ 1 := by
      intro h1
      apply pick_ne S
      exact Subtype.ext h1
    have hsubEq : T.1 = S.1 :=
      subgroup_eq_of_card_eq_prime_of_common_ne_one Nat.prime_three
        T.1 S.1 (hTcard T) (hTcard S)
        (by
          have hmem := (pick T).2
          change ((pick T : T.1) : QG) ∈ T.1 at hmem
          rw [hval] at hmem
          exact hmem)
        (pick S).2 hpickS_ne
    exact Subtype.ext hsubEq
  have htargetCard : Nat.card target = 8 := by
    let : Fintype A := Fintype.ofFinite A
    let : Fintype target := Fintype.ofFinite target
    have hAF : Fintype.card A = 9 := by
      simpa [Nat.card_eq_fintype_card] using hAcard
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp [hAF]
  have hOrbLe : Nat.card Orb ≤ 8 := by
    rw [← htargetCard]
    exact Nat.card_le_card_of_injective f hfInj
  have hOrbIndex : Nat.card Orb = AQ.index := by
    calc
      Nat.card Orb = Nat.card (QG ⧸ MulAction.stabilizer QG FQ) :=
        Nat.card_congr (MulAction.orbitEquivQuotientStabilizer QG FQ)
      _ = (MulAction.stabilizer QG FQ).index :=
        (Subgroup.index_eq_card (MulAction.stabilizer QG FQ)).symm
      _ = AQ.index := by rw [hstab]
  have hindexLe : AQ.index ≤ 8 := by rw [← hOrbIndex]; exact hOrbLe
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hQGp.index AQ
  have hindexGt : 1 < AQ.index := by
    have hAQlt : AQ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
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
      norm_num at hindexGt
    by_contra hn1
    have hnTwo : 2 ≤ n := by omega
    have hpow : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hnTwo
    rw [← hn] at hpow
    omega
  have hindex : AQ.index = 3 := by rw [hn, hnOne]; norm_num
  have hmul := Subgroup.card_mul_index AQ
  rw [hAQcard, hindex] at hmul
  norm_num at hmul
  simpa [QG] using hmul.symm

end CFSG.GorensteinWalter
