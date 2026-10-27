module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-seven structural conclusion in the order-four branch

This module packages the reusable endpoint of Bender's second order-four
case.  Once an order-three subgroup is self-centralizing and has its usual
dihedral normalizer, the ambient order `168` forces the `q = 7`
Brauer--Suzuki--Wall conclusion.  No low-order recognition theorem is used.
-/

namespace CFSG.GorensteinWalter

open BenderSuzuki.External

universe u

/-- In the `|K| = 4`, `|G| = 168` branch, a self-centralizing subgroup `D`
of order three with an inverting normalizer complement supplies the
`q = 7` Brauer--Suzuki--Wall structural conclusion.

The Klein four subgroup rules out a normal Sylow-seven subgroup: its
conjugation action on a normal subgroup of order seven would be fixed-point
free away from the identity, contradicting `4 ∤ 6`.  The order-three group
then fixes a Sylow-seven subgroup `Q`; Sylow counting gives
`N_G(Q) = Q ⊔ D`. -/
public theorem
    BrauerSuzukiWallHypotheses.conclusion_nonempty_of_card_K_eq_four_of_card_G_eq_168_of_order_three_complement
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V D : Subgroup G)
    (hV : IsKleinFour V)
    (hDcard : Nat.card D = 3)
    (hDcent : ∀ d : G, d ∈ D → d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) = D)
    (u : G) (hu : IsInvolution u)
    (hNormD : Subgroup.normalizer (D : Set G) =
      D ⊔ Subgroup.zpowers u)
    (huinv : ∀ d : G, d ∈ D → u * d * u⁻¹ = d⁻¹)
    (hGcard : Nat.card G = 168) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q0, hQ0card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := G) 7 (n := 1) (by
      rw [hGcard]
      norm_num)
  have hQ0p : IsPGroup 7 Q0 := by
    apply IsPGroup.of_card (n := 1)
    simpa using hQ0card
  have hQ0index : Q0.index = 24 := by
    have hmul := Q0.card_mul_index
    rw [hQ0card, hGcard] at hmul
    norm_num at hmul ⊢
    omega
  have hsevenNotIndex : ¬ 7 ∣ Q0.index := by
    rw [hQ0index]
    norm_num
  let P0 : Sylow 7 G := hQ0p.toSylow hsevenNotIndex
  have hP0coe : (P0 : Subgroup G) = Q0 :=
    IsPGroup.toSylow_coe hQ0p hsevenNotIndex
  have hSylowDvd : Nat.card (Sylow 7 G) ∣ 24 := by
    simpa [P0, hP0coe, hQ0index] using P0.card_dvd_index
  have hSylowMod : Nat.card (Sylow 7 G) % 7 = 1 := by
    have hm := (card_sylow_modEq_one 7 G :
      Nat.card (Sylow 7 G) ≡ 1 [MOD 7])
    change Nat.card (Sylow 7 G) % 7 = 1 % 7 at hm
    norm_num at hm
    exact hm
  have hSylowPos : 0 < Nat.card (Sylow 7 G) := Nat.card_pos
  have hSylowCases : Nat.card (Sylow 7 G) = 1 ∨
      Nat.card (Sylow 7 G) = 8 := by
    have hle : Nat.card (Sylow 7 G) ≤ 24 :=
      Nat.le_of_dvd (by norm_num) hSylowDvd
    have hmodCases : Nat.card (Sylow 7 G) = 1 ∨
        Nat.card (Sylow 7 G) = 8 ∨
        Nat.card (Sylow 7 G) = 15 ∨
        Nat.card (Sylow 7 G) = 22 := by
      omega
    rcases hmodCases with hone | height | hfifteen | htwentyTwo
    · exact Or.inl hone
    · exact Or.inr height
    · rw [hfifteen] at hSylowDvd
      norm_num at hSylowDvd
    · rw [htwentyTwo] at hSylowDvd
      norm_num at hSylowDvd
  have hSylowCard : Nat.card (Sylow 7 G) = 8 := by
    rcases hSylowCases with hone | height
    · exfalso
      let : Subsingleton (Sylow 7 G) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      have hP0normal : (P0 : Subgroup G).Normal :=
        Sylow.normal_of_subsingleton P0
      have hVleNorm : V ≤
          Subgroup.normalizer ((P0 : Subgroup G) : Set G) := by
        rw [Subgroup.normalizer_eq_top (P0 : Subgroup G)]
        exact le_top
      let : IsKleinFour V := hV
      let : MulDistribMulAction V (P0 : Subgroup G) :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer
          V (P0 : Subgroup G) hVleNorm
      have hfree : ∀ a : V, a ≠ 1 → ∀ z : (P0 : Subgroup G),
          a • z = z → z = 1 := by
        intro a hane z hfix
        have haI : IsInvolution (a : G) := by
          constructor
          · intro haone
            exact hane (Subtype.ext haone)
          · simpa [pow_two] using
              congrArg Subtype.val (IsKleinFour.mul_self a)
        have hconj : (a : G) * (z : G) * (a : G)⁻¹ = (z : G) := by
          rw [← Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
            V (P0 : Subgroup G) hVleNorm a z]
          exact congrArg Subtype.val hfix
        have hzCent : (z : G) ∈
            Subgroup.centralizer ({(a : G)} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
        have hCentCard : Nat.card
            (Subgroup.centralizer ({(a : G)} : Set G)) = 8 := by
          calc
            Nat.card (Subgroup.centralizer ({(a : G)} : Set G)) =
                Nat.card h.H := centralizer_involution_card_eq_card_H h haI
            _ = 8 := by rw [h.card_H, hk]
        have hdisj : Disjoint (P0 : Subgroup G)
            (Subgroup.centralizer ({(a : G)} : Set G)) := by
          apply Subgroup.disjoint_of_coprime_natCard
          rw [hP0coe, hQ0card, hCentCard]
          norm_num
        have hzbot : (z : G) ∈ (⊥ : Subgroup G) :=
          hdisj.le_bot ⟨z.property, hzCent⟩
        apply Subtype.ext
        simpa using hzbot
      have hdvd := natCard_dvd_card_sub_one_of_fixedPointFree_action hfree
      rw [hV.card_four, hP0coe, hQ0card] at hdvd
      norm_num at hdvd
    · exact height
  have hDp : IsPGroup 3 D := by
    apply IsPGroup.of_card (n := 1)
    simpa using hDcard
  obtain ⟨P, hPfix⟩ :=
    hDp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 7 G) (by
      rw [hSylowCard]
      norm_num)
  let Q : Subgroup G := (P : Subgroup G)
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hDleN : D ≤ N := by
    simpa [Q, N] using (Subgroup.sylow_mem_fixedPoints_iff D).mp hPfix
  have hQcard : Nat.card Q = 7 := by
    calc
      Nat.card Q = Nat.card (P : Subgroup G) := rfl
      _ = Nat.card (P0 : Subgroup G) :=
        Nat.card_congr (Sylow.equiv P P0).toEquiv
      _ = Nat.card Q0 := by rw [hP0coe]
      _ = 7 := by simpa using hQ0card
  have hNindex : N.index = 8 := by
    simpa [N, Q] using (P.card_eq_index_normalizer.symm.trans hSylowCard)
  have hNcard : Nat.card N = 21 := by
    have hmul := N.card_mul_index
    rw [hNindex, hGcard] at hmul
    omega
  have hQD : Disjoint Q D := by
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hQcard, hDcard]
    norm_num
  have hQleN : Q ≤ N := by
    simpa [N] using (Subgroup.le_normalizer (H := Q))
  have hNormQ : N = Q ⊔ D := by
    let QN : Subgroup N := Q.subgroupOf N
    let DN : Subgroup N := D.subgroupOf N
    have hQNcard : Nat.card QN = 7 := by
      rw [natCard_subgroupOf_eq Q N hQleN, hQcard]
    have hDNcard : Nat.card DN = 3 := by
      rw [natCard_subgroupOf_eq D N hDleN, hDcard]
    have hQNDN : Disjoint QN DN := by
      rw [Subgroup.disjoint_def]
      intro z hzQ hzD
      apply Subtype.ext
      exact hQD.le_bot ⟨hzQ, hzD⟩
    have hcomp : QN.IsComplement' DN :=
      Subgroup.isComplement'_of_card_mul_and_disjoint (by
        rw [hQNcard, hDNcard, hNcard]) hQNDN
    apply le_antisymm
    · have hsub : (Q ⊔ D).subgroupOf N = ⊤ := by
        rw [Subgroup.subgroupOf_sup hQleN hDleN]
        exact hcomp.sup_eq_top
      exact Subgroup.subgroupOf_eq_top.mp hsub
    · exact sup_le hQleN hDleN
  have hQcomm : IsMulCommutative Q := by
    let : IsCyclic Q := isCyclic_of_prime_card hQcard
    exact IsCyclic.isMulCommutative
  have hQcent : ∀ x : G, x ∈ Q → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Q := by
    intro x hxQ hxne
    let xQ : Q := ⟨x, hxQ⟩
    have hxQne : xQ ≠ 1 := by
      intro hxone
      exact hxne (congrArg Subtype.val hxone)
    have hzpTop : Subgroup.zpowers xQ = ⊤ := by
      exact zpowers_eq_top_of_prime_card hQcard hxQne
    have hzpQ : Subgroup.zpowers x = Q := by
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr hxQ
      · intro y hyQ
        let yQ : Q := ⟨y, hyQ⟩
        have hyPow : yQ ∈ Subgroup.zpowers xQ := by
          rw [hzpTop]
          exact Subgroup.mem_top yQ
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hyPow
        exact Subgroup.mem_zpowers_iff.mpr
          ⟨n, congrArg Subtype.val hn⟩
    let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
    have hQleC : Q ≤ C := by
      intro y hyQ
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := Q)).comm
          ⟨y, hyQ⟩ ⟨x, hxQ⟩)
    have hCleN : C ≤ N := by
      intro g hgC
      have hgCQ : g ∈ Subgroup.centralizer (Q : Set G) := by
        rw [← hzpQ, Subgroup.zpowers_eq_closure,
          Subgroup.centralizer_closure]
        exact hgC
      exact Subgroup.centralizer_le_normalizer (Q : Set G) hgCQ
    have hQdvdC : 7 ∣ Nat.card C := by
      rw [← hQcard]
      exact Subgroup.card_dvd_of_le hQleC
    have hCdvdN : Nat.card C ∣ 21 := by
      rw [← hNcard]
      exact Subgroup.card_dvd_of_le hCleN
    have hCcases : Nat.card C = 7 ∨ Nat.card C = 21 := by
      have hCpos : 0 < Nat.card C := Nat.card_pos
      have hCle : Nat.card C ≤ 21 :=
        Nat.le_of_dvd (by norm_num) hCdvdN
      rcases hQdvdC with ⟨m, hm⟩
      have hmPos : 0 < m := by omega
      have hmLe : m ≤ 3 := by omega
      have hmCases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
      rcases hmCases with hmOne | hmTwo | hmThree
      · left
        omega
      · rw [hmTwo] at hm
        have : Nat.card C = 14 := by omega
        rw [this] at hCdvdN
        norm_num at hCdvdN
      · right
        omega
    rcases hCcases with hCseven | hCtwentyOne
    · exact (Subgroup.eq_of_le_of_card_ge hQleC (by
        rw [hQcard, hCseven])).symm
    · exfalso
      have hCN : C = N :=
        Subgroup.eq_of_le_of_card_ge hCleN (by
          rw [hCtwentyOne, hNcard])
      obtain ⟨dD, hdOrder⟩ :=
        exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hDcard])
      let d : G := dD
      have hdOrderG : orderOf d = 3 := by
        simpa [d] using (Subgroup.orderOf_coe dD).trans hdOrder
      have hdne : d ≠ 1 := by
        intro hdone
        rw [hdone, orderOf_one] at hdOrderG
        omega
      have hdC : d ∈ C := by
        rw [hCN]
        exact hDleN dD.property
      have hxCentD : x ∈ Subgroup.centralizer ({d} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hdC).symm
      have hxD : x ∈ D := by
        rw [← hDcent d dD.property hdne]
        exact hxCentD
      have hxbot : x ∈ (⊥ : Subgroup G) := hQD.le_bot ⟨hxQ, hxD⟩
      exact hxne (by simpa using hxbot)
  have hDcomm : IsMulCommutative D := by
    let : IsCyclic D := isCyclic_of_prime_card hDcard
    exact IsCyclic.isMulCommutative
  obtain ⟨dD, hdOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 3 (by rw [hDcard])
  let d : G := dD
  have hdOrderG : orderOf d = 3 := by
    simpa [d] using (Subgroup.orderOf_coe dD).trans hdOrder
  have hdne : d ≠ 1 := by
    intro hdone
    rw [hdone, orderOf_one] at hdOrderG
    omega
  have hCd : Subgroup.centralizer ({d} : Set G) = D :=
    hDcent d dD.property hdne
  have hDTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (D : Set G)) (D : Set G) := by
    have hCcomm : IsMulCommutative
        (Subgroup.centralizer ({d} : Set G)) := by
      rw [hCd]
      exact hDcomm
    have hCCent : ∀ a : G,
        a ∈ Subgroup.centralizer ({d} : Set G) → a ≠ 1 →
          Subgroup.centralizer ({a} : Set G) =
            Subgroup.centralizer ({d} : Set G) := by
      intro a ha hane
      rw [hCd] at ha ⊢
      exact hDcent a ha hane
    simpa [hCd] using
      selected_centralizer_isTISubsetRelative hdne hCcomm hCCent
  have huD : u ∉ D := by
    intro huD
    have huOrder : orderOf u = 2 :=
      orderOf_eq_prime hu.2 hu.1
    have hdvd : 2 ∣ Nat.card D := by
      rw [← huOrder]
      exact Subgroup.orderOf_dvd_natCard D huD
    rw [hDcard] at hdvd
    norm_num at hdvd
  have hGformula : Nat.card G = 7 * (7 + 1) * (7 - 1) / 2 := by
    norm_num
    exact hGcard
  exact conclusion_nonempty_of_structural_data
    7 Q D (by norm_num) hQcard hGformula hQcent hDcomm hQD
      (Subgroup.normalizer (D : Set G)) hDTI u hu huD hNormD huinv
      (by simpa [N] using hNormQ) (by norm_num [hDcard])

end CFSG.GorensteinWalter
