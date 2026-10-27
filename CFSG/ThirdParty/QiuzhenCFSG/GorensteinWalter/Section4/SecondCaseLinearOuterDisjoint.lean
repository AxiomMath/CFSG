module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationSevenOuterSupport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearK0CardDvdTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Disjointness in the linear outer-involution branch

The transported odd reflected subgroup is disjoint from the equation-(8)
index subgroup.  The group-theoretic point is that an element of the
intersection has an odd square root in the intersection; its commutator with
the outer reflection lies in the equation-(7) support subgroup.  Prime
support and the two complementary field halves then force it to be trivial.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open scoped commutatorElement

universe u

/-- The odd reflected subgroup in the outer-involution branch is disjoint
from `B K F(U)`. -/
public theorem secondCase_linear_outer_disjoint
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kfield : Type u) [Field Kfield] [Finite Kfield]
    (od : SecondCaseLinearOmegaData c w d)
    (torus : SecondCasePSL2QuotientTorusCard d Kfield)
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤
      (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (hKcomm : od.K =
      ⁅(SE : Subgroup d.E).map d.E.subtype, c.U ⊓ w.M⁆)
    (hK0normal : IsNormalIn od.K0 (c.H ⊓ w.M))
    (hLayer : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ od.F →
      componentLayerOf (Subgroup.normalizer (X : Set G)) = d.E)
    (r : w.M) (R : Subgroup G)
    (hrSM : r ∈ (SM : Subgroup w.M))
    (hRodd : Odd (Nat.card R))
    (hRcard : Nat.card R = (Nat.card Kfield - 1) / 2 ∨
      Nat.card R = (Nat.card Kfield + 1) / 2)
    (hRinv : ∀ x : G, x ∈ R →
      (r : G) * x * (r : G)⁻¹ = x⁻¹) :
    Disjoint (od.B ⊔ od.K ⊔ c.FU) R := by
  classical
  let rG : G := r
  let Rr : Subgroup G := Subgroup.zpowers rG
  let A : Subgroup G := (SE : Subgroup d.E).map d.E.subtype
  let X : Subgroup G := c.U ⊓ w.M
  let Cmt : Subgroup G := ⁅Rr, od.B⁆
  let J : Subgroup G := Cmt ⊔ od.K ⊔ c.FU
  let L : Subgroup G := od.B ⊔ od.K ⊔ c.FU
  have hrS : rG ∈ (c.S : Subgroup G) := by
    exact hSMleS (Subgroup.mem_map.mpr ⟨r, hrSM, rfl⟩)
  have hrH : rG ∈ c.H := centralizerSetup_S_le_H c hrS
  have hRrleS : Rr ≤ (c.S : Subgroup G) := Subgroup.zpowers_le.mpr hrS
  have hRrleH : Rr ≤ c.H := hRrleS.trans (centralizerSetup_S_le_H c)
  have hRrleM : Rr ≤ w.M := Subgroup.zpowers_le.mpr r.2
  have hRr_norm_SMamb : Rr ≤ Subgroup.normalizer
      (((SM : Subgroup w.M).map w.M.subtype : Subgroup G) : Set G) := by
    apply Subgroup.zpowers_le.mpr
    exact ((SM : Subgroup w.M).map w.M.subtype).le_normalizer
      (Subgroup.mem_map.mpr ⟨r, hrSM, rfl⟩)
  have hRr_norm_E : Rr ≤ Subgroup.normalizer (d.E : Set G) := by
    apply Subgroup.zpowers_le.mpr
    exact le_normalizer_of_isNormalIn d.E_normal r.2
  have hRr_norm_A : Rr ≤ Subgroup.normalizer (A : Set G) := by
    rw [show A = ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E by
      exact hSEamb]
    intro z hz
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRr_norm_SMamb hz, hRr_norm_E hz⟩
  have hRr_norm_U : Rr ≤ Subgroup.normalizer (c.U : Set G) :=
    hRrleH.trans (le_normalizer_of_isNormalIn
      (centralizerSetup_U_isNormalIn_H c))
  have hRr_norm_M : Rr ≤ Subgroup.normalizer (w.M : Set G) :=
    hRrleM.trans w.M.le_normalizer
  have hRr_norm_X : Rr ≤ Subgroup.normalizer (X : Set G) := by
    intro z hz
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hRr_norm_U hz, hRr_norm_M hz⟩
  have hRr_norm_K : Rr ≤ Subgroup.normalizer (od.K : Set G) := by
    rw [hKcomm]
    exact le_normalizer_commutator_of_le_normalizer Rr A X
      hRr_norm_A hRr_norm_X
  have hRr_norm_FU : Rr ≤ Subgroup.normalizer (c.FU : Set G) :=
    hRrleH.trans (le_normalizer_of_isNormalIn
      (centralizerSetup_FU_isNormalIn_H c))
  have hUodd : Odd (Nat.card c.U) := by
    change Odd (Nat.card (oddCoreOf c.H))
    exact odd_card_oddCoreOf c.H
  have hXodd : Odd (Nat.card X) :=
    Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_left)
  have hsM : (od.s : G) ∈ w.M := d.E_component.1 od.s.2
  have hsX : ∀ x : G, x ∈ X →
      (od.s : G) * x * (od.s : G)⁻¹ ∈ X := by
    intro x hx
    exact ⟨(centralizerSetup_U_isNormalIn_H c).2
        (od.s : G) od.s_mem_H x hx.1,
      w.M.mul_mem (w.M.mul_mem hsM hx.2) (w.M.inv_mem hsM)⟩
  have hKnormalX : IsNormalIn od.K X :=
    (fact_1_5_iii_inverted_subgroup_abelian_normal
      (X := X) (s := (od.s : G)) od.s_involution
      (Nat.coprime_two_left.mpr hXodd) hsX
      (I := od.K) od.K_inverted).2.1
  have hBleX : od.B ≤ X := by
    rw [od.B_fixed]
    exact inf_le_left
  have hB_norm_K : od.B ≤ Subgroup.normalizer (od.K : Set G) :=
    hBleX.trans (le_normalizer_of_isNormalIn hKnormalX)
  have hBleU : od.B ≤ c.U := hBleX.trans inf_le_left
  have hKleU : od.K ≤ c.U := by
    intro x hx
    have hxI : x ∈ invertedElements X (od.s : G) := by
      rw [← od.K_inverted]
      exact hx
    exact hxI.1.1
  have hB_norm_FU : od.B ≤ Subgroup.normalizer (c.FU : Set G) :=
    hBleU.trans (le_normalizer_of_isNormalIn
      (fittingSubgroupOf_isNormalIn c.U))
  have hK_norm_FU : od.K ≤ Subgroup.normalizer (c.FU : Set G) :=
    hKleU.trans (le_normalizer_of_isNormalIn
      (fittingSubgroupOf_isNormalIn c.U))
  have hCmt_norm_K : Cmt ≤ Subgroup.normalizer (od.K : Set G) := by
    exact (Subgroup.commutator_le_sup Rr od.B).trans
      (sup_le hRr_norm_K hB_norm_K)
  have hRr_norm_Cmt : Rr ≤ Subgroup.normalizer (Cmt : Set G) := by
    exact Subgroup.normalizer_commutator_ge_left Rr od.B
  have hB_norm_Cmt : od.B ≤ Subgroup.normalizer (Cmt : Set G) := by
    exact Subgroup.normalizer_commutator_ge_right Rr od.B
  have normalizes_sup {Q P1 P2 : Subgroup G}
      (h1 : Q ≤ Subgroup.normalizer (P1 : Set G))
      (h2 : Q ≤ Subgroup.normalizer (P2 : Set G)) :
      Q ≤ Subgroup.normalizer ((P1 ⊔ P2 : Subgroup G) : Set G) := by
    intro q hq
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup P1 P2
      ⟨h1 hq, h2 hq⟩
  have hRr_norm_J : Rr ≤ Subgroup.normalizer (J : Set G) := by
    exact normalizes_sup (normalizes_sup hRr_norm_Cmt hRr_norm_K)
      hRr_norm_FU
  have hB_norm_J : od.B ≤ Subgroup.normalizer (J : Set G) := by
    exact normalizes_sup (normalizes_sup hB_norm_Cmt hB_norm_K) hB_norm_FU
  have hK_norm_CmtK : od.K ≤
      Subgroup.normalizer ((Cmt ⊔ od.K : Subgroup G) : Set G) := by
    exact (le_sup_right : od.K ≤ Cmt ⊔ od.K).trans
      (Cmt ⊔ od.K).le_normalizer
  have hK_norm_J : od.K ≤ Subgroup.normalizer (J : Set G) := by
    exact normalizes_sup hK_norm_CmtK hK_norm_FU
  have hFUleJ : c.FU ≤ J := le_sup_right
  have hFU_norm_J : c.FU ≤ Subgroup.normalizer (J : Set G) :=
    hFUleJ.trans J.le_normalizer
  have hBK_norm_J : od.B ⊔ od.K ≤ Subgroup.normalizer (J : Set G) :=
    sup_le hB_norm_J hK_norm_J
  have hcomm_R_B : ⁅Rr, od.B⁆ ≤ J := by
    exact (le_sup_left : Cmt ≤ Cmt ⊔ od.K).trans le_sup_left
  have hcomm_R_K : ⁅Rr, od.K⁆ ≤ J :=
    ((Subgroup.le_normalizer_iff_commutator_le_right.mp hRr_norm_K).trans
      ((le_sup_right : od.K ≤ Cmt ⊔ od.K).trans le_sup_left))
  have hcomm_R_FU : ⁅Rr, c.FU⁆ ≤ J :=
    ((Subgroup.le_normalizer_iff_commutator_le_right.mp hRr_norm_FU).trans
      le_sup_right)
  have hcomm_BK_R : ⁅od.B ⊔ od.K, Rr⁆ ≤ J := by
    apply commutator_sup_le_of_commutator_le_and_normalize
      od.B od.K Rr J
    · rw [Subgroup.commutator_comm]
      exact hcomm_R_B
    · rw [Subgroup.commutator_comm]
      exact hcomm_R_K
    · exact hB_norm_J
    · exact hK_norm_J
  have hcomm_L_R : ⁅L, Rr⁆ ≤ J := by
    apply commutator_sup_le_of_commutator_le_and_normalize
      (od.B ⊔ od.K) c.FU Rr J
    · exact hcomm_BK_R
    · rw [Subgroup.commutator_comm]
      exact hcomm_R_FU
    · exact hBK_norm_J
    · exact hFU_norm_J
  have hcomm_R_L : ⁅Rr, L⁆ ≤ J := by
    rw [Subgroup.commutator_comm]
    exact hcomm_L_R
  have hK0dvdT : Nat.card od.K0 ∣ Nat.card torus.T :=
    secondCase_linear_K0_card_dvd_quotientTorus c w d Kfield od torus
  have hTRcop : Nat.Coprime (Nat.card torus.T) (Nat.card R) := by
    have hqodd : Odd (Nat.card Kfield) := by
      rcases torus.primePower with ⟨p, n, hp, hpodd, hn, hcard⟩
      rw [hcard]
      exact hpodd.pow
    have hhalves : (Nat.card Kfield + 1) / 2 =
        (Nat.card Kfield - 1) / 2 + 1 := by
      rcases hqodd with ⟨a, ha⟩
      omega
    rcases torus.T_card with hTminus | hTplus <;>
      rcases hRcard with hRminus | hRplus
    · exfalso
      have hTeven : Even (Nat.card R) := by
        rw [hRminus, ← hTminus]
        exact torus.T_even
      exact (Nat.not_even_iff_odd.mpr hRodd) hTeven
    · rw [hTminus, hRplus, hhalves]
      exact Nat.coprime_self_add_right.mpr
        (Nat.coprime_one_right ((Nat.card Kfield - 1) / 2))
    · rw [hTplus, hRminus, hhalves]
      exact (Nat.coprime_self_add_right.mpr
        (Nat.coprime_one_right ((Nat.card Kfield - 1) / 2))).symm
    · exfalso
      have hTeven : Even (Nat.card R) := by
        rw [hRplus, ← hTplus]
        exact torus.T_even
      exact (Nat.not_even_iff_odd.mpr hRodd) hTeven
  have hK0Rcop : Nat.Coprime (Nat.card od.K0) (Nat.card R) :=
    Nat.Coprime.coprime_dvd_left hK0dvdT hTRcop
  have hsupport : ∀ p ∈ (Nat.card J).primeFactors,
      p ∣ Nat.card od.K0 := by
    simpa [J, Cmt, Rr, rG, CentralizerSetup.FU] using
      secondCase_equationSevenPrime_primeFactors_outerSupport_subset_K0
        hmin c w d od.K od.K0 od.F od.B od.s rG od.K_inverted
        od.K_cyclic od.K_le_E od.K0_eq od.F_fixed od.FU_inter_M_eq
        od.F_centralizes_E hLayer od.B_fixed hK0normal hrS r.2
  have hJRcop : Nat.Coprime (Nat.card J) (Nat.card R) := by
    apply Nat.coprime_of_dvd
    intro p hp hpdvdJ hpdvdR
    have hpJ : p ∈ (Nat.card J).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvdJ, Nat.card_pos.ne'⟩
    have hpdvdK0 : p ∣ Nat.card od.K0 := hsupport p hpJ
    have hpgcd : p ∣ Nat.gcd (Nat.card od.K0) (Nat.card R) :=
      Nat.dvd_gcd hpdvdK0 hpdvdR
    rw [hK0Rcop.gcd_eq_one] at hpgcd
    exact hp.not_dvd_one hpgcd
  have hJRdisj : Disjoint J R := Subgroup.disjoint_of_coprime_natCard hJRcop
  have hcap_le_J : R ⊓ L ≤ J := by
    intro x hx
    let Cap : Subgroup G := R ⊓ L
    have hCapodd : Odd (Nat.card Cap) :=
      Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_le inf_le_left)
    rcases hCapodd with ⟨a, ha⟩
    let xC : Cap := ⟨x, hx⟩
    let yC : Cap := xC ^ (a + 1)
    have hxpowC : xC ^ Nat.card Cap = 1 := pow_card_eq_one'
    have hy2C : yC ^ 2 = xC := by
      dsimp [yC]
      calc
        (xC ^ (a + 1)) ^ 2 = xC ^ ((a + 1) * 2) := by rw [pow_mul]
        _ = xC ^ (Nat.card Cap + 1) := by congr 1; omega
        _ = xC ^ Nat.card Cap * xC := by rw [pow_succ]
        _ = xC := by rw [hxpowC]; simp
    have hy2 : (yC : G) ^ 2 = x := by
      exact congrArg Subtype.val hy2C
    have hyR : (yC : G) ∈ R := yC.2.1
    have hyL : (yC : G) ∈ L := yC.2.2
    have hcommmem : ⁅rG, (yC : G)⁆ ∈ J :=
      hcomm_R_L (Subgroup.commutator_mem_commutator
        (Subgroup.mem_zpowers rG) hyL)
    have hcommEq : ⁅rG, (yC : G)⁆ = x⁻¹ := by
      rw [commutatorElement_def, hRinv (yC : G) hyR]
      rw [← mul_inv_rev, ← pow_two, hy2]
    have hxinvJ : x⁻¹ ∈ J := by rwa [← hcommEq]
    exact J.inv_mem_iff.mp hxinvJ
  rw [show od.B ⊔ od.K ⊔ c.FU = L by rfl]
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  have hxJ : x ∈ J := hcap_le_J ⟨hx.2, hx.1⟩
  have hxJR : x ∈ J ⊓ R := ⟨hxJ, hx.2⟩
  rw [hJRdisj.eq_bot] at hxJR
  exact hxJR

end CFSG.GorensteinWalter
