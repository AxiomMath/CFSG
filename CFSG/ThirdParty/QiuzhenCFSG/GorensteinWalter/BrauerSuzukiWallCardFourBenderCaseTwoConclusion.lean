module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourOrderSevenConclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardFourNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CyclicOrderThreeAutomorphism
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer

import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallStructure
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The structural conclusion in Bender's second order-four case

Once Bender's Case-2 incidence count gives ambient order 168, the standard
order-three subgroup in the Klein-four normalizer supplies the q = 7
Brauer--Suzuki--Wall conclusion.  The proof constructs its self-centralizing
dihedral normalizer directly, without low-order group recognition.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In Bender's containment branch for |K| = 4, ambient order 168 forces
the full Brauer--Suzuki--Wall structural conclusion with parameter q = 7. -/
public theorem
    BrauerSuzukiWallHypotheses.conclusion_nonempty_of_card_K_eq_four_of_bender_case_two_of_card_eq_168
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 4)
    (V X : Subgroup G)
    (hV : IsKleinFour V)
    (hCentV : Subgroup.centralizer (V : Set G) = V)
    (hNcard : Nat.card (Subgroup.normalizer (V : Set G)) = 24)
    (hXle : X ≤ Subgroup.normalizer (V : Set G))
    (hXcard : Nat.card X = 3)
    (hcase : Subgroup.centralizer (X : Set G) ≤
      Subgroup.normalizer (V : Set G))
    (hGcard : Nat.card G = 168) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (V : Set G)
  have hNcard' : Nat.card N = 24 := by simpa [N] using hNcard
  let XN : Subgroup N := X.subgroupOf N
  have hXNcard : Nat.card XN = 3 := by
    calc
      Nat.card XN = Nat.card X :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv
      _ = 3 := hXcard
  have hXNindex : XN.index = 8 := by
    have hmul := XN.card_mul_index
    rw [hXNcard, hNcard'] at hmul
    omega
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXNp : IsPGroup 3 XN := by
    apply IsPGroup.of_card (n := 1)
    simpa [hXNcard]
  have hthreeNotIndex : ¬ 3 ∣ XN.index := by
    rw [hXNindex]
    norm_num
  let P : Sylow 3 N := hXNp.toSylow hthreeNotIndex
  have hSylowDvd : Nat.card (Sylow 3 N) ∣ 8 := by
    simpa [P, hXNindex] using P.card_dvd_index
  have hSylowCard : Nat.card (Sylow 3 N) = 4 := by
    have hle : Nat.card (Sylow 3 N) ≤ 8 :=
      Nat.le_of_dvd (by norm_num) hSylowDvd
    have hmod : Nat.card (Sylow 3 N) % 3 = 1 := by
      have hm := (card_sylow_modEq_one 3 N :
        Nat.card (Sylow 3 N) ≡ 1 [MOD 3])
      change Nat.card (Sylow 3 N) % 3 = 1 % 3 at hm
      norm_num at hm
      exact hm
    have hpos : 0 < Nat.card (Sylow 3 N) := Nat.card_pos
    have hcases : Nat.card (Sylow 3 N) = 1 ∨
        Nat.card (Sylow 3 N) = 4 := by
      rcases (Nat.dvd_prime_pow Nat.prime_two
          (m := 3) (i := Nat.card (Sylow 3 N))).mp (by
            simpa using hSylowDvd) with ⟨i, hi, hcard⟩
      interval_cases i
      · exact Or.inl (by simpa using hcard)
      · simp only [pow_one] at hcard
        norm_num [hcard] at hmod
      · exact Or.inr (by norm_num at hcard ⊢; exact hcard)
      · norm_num at hcard
        norm_num [hcard] at hmod
    rcases hcases with hone | hfour
    · exfalso
      let : Subsingleton (Sylow 3 N) :=
        (Nat.card_eq_one_iff_unique.mp hone).1
      have hXNnormal : XN.Normal := by
        simpa [P] using Sylow.normal_of_subsingleton P
      have hVleN : V ≤ N := by
        simpa [N] using (Subgroup.le_normalizer (H := V))
      let VN : Subgroup N := V.subgroupOf N
      have hVNnormal : VN.Normal := by
        apply (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr
        exact le_rfl
      have hdisjoint : Disjoint VN XN := by
        apply Subgroup.disjoint_of_coprime_natCard
        rw [natCard_subgroupOf_eq V N hVleN, hV.card_four, hXNcard]
        norm_num
      have hXleCentV : X ≤ Subgroup.centralizer (V : Set G) := by
        intro x hxX
        rw [Subgroup.mem_centralizer_iff]
        intro v hvV
        let xN : N := ⟨x, hXle hxX⟩
        let vN : N := ⟨v, hVleN hvV⟩
        have hcommN := Subgroup.commute_of_normal_of_disjoint
          VN XN hVNnormal hXNnormal hdisjoint vN xN hvV hxX
        exact congrArg Subtype.val hcommN.eq
      have hXleV : X ≤ V := by simpa [hCentV] using hXleCentV
      have hdvd : 3 ∣ Nat.card V := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXleV
      rw [hV.card_four] at hdvd
      norm_num at hdvd
    · exact hfour
  have hPcoe : (P : Subgroup N) = XN :=
    IsPGroup.toSylow_coe hXNp hthreeNotIndex
  let R : Subgroup N := Subgroup.normalizer (XN : Set N)
  have hRindex : R.index = 4 := by
    have hnormEq :
        Subgroup.normalizer ((P : Subgroup N) : Set N) =
          Subgroup.normalizer (XN : Set N) :=
      congrArg (fun Q : Subgroup N => Subgroup.normalizer (Q : Set N)) hPcoe
    calc
      R.index = Nat.card (Sylow 3 N) := by
        change (Subgroup.normalizer (XN : Set N)).index = _
        rw [← hnormEq]
        exact P.card_eq_index_normalizer.symm
      _ = 4 := hSylowCard
  have hRcard : Nat.card R = 6 := by
    have hmul := R.card_mul_index
    rw [hRindex, hNcard'] at hmul
    omega
  obtain ⟨uR, huOrderR⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) 2 (by rw [hRcard]; norm_num)
  let uN : N := (uR : N)
  let u : G := (uN : G)
  have huOrderN : orderOf uN = 2 := by
    simpa [uN] using (Subgroup.orderOf_coe uR).trans huOrderR
  have huOrder : orderOf u = 2 := by
    simpa [u] using (Subgroup.orderOf_coe uN).trans huOrderN
  have hu : IsInvolution u := by
    constructor
    · intro huone
      rw [huone, orderOf_one] at huOrder
      omega
    · rw [← huOrder]
      exact pow_orderOf_eq_one u
  have hXNcomm : IsMulCommutative XN := by
    let : IsCyclic XN := isCyclic_of_prime_card hXNcard
    exact IsCyclic.isMulCommutative
  let CN : Subgroup N := Subgroup.centralizer (XN : Set N)
  have hXNleCN : XN ≤ CN := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (hXNcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hCNleR : CN ≤ R :=
    Subgroup.centralizer_le_normalizer (XN : Set N)
  have hCNcard : Nat.card CN = 3 := by
    have hthreeDvd : 3 ∣ Nat.card CN := by
      rw [← hXNcard]
      exact Subgroup.card_dvd_of_le hXNleCN
    have hdvdSix : Nat.card CN ∣ 6 := by
      rw [← hRcard]
      exact Subgroup.card_dvd_of_le hCNleR
    have hcases : Nat.card CN = 3 ∨ Nat.card CN = 6 := by
      have hpos : 0 < Nat.card CN := Nat.card_pos
      have hle : Nat.card CN ≤ 6 := Nat.le_of_dvd (by norm_num) hdvdSix
      rcases hthreeDvd with ⟨m, hm⟩
      have hmPos : 0 < m := by omega
      have hmLe : m ≤ 2 := by omega
      have hmCases : m = 1 ∨ m = 2 := by omega
      rcases hmCases with hmOne | hmTwo
      · left
        omega
      · right
        omega
    rcases hcases with hthree | hsix
    · exact hthree
    · exfalso
      have hCNR : CN = R :=
        Subgroup.eq_of_le_of_card_ge hCNleR (by rw [hsix, hRcard])
      have huCN : uN ∈ CN := by
        rw [hCNR]
        exact uR.property
      have hXleCentU : X ≤ Subgroup.centralizer ({u} : Set G) := by
        intro x hxX
        rw [Subgroup.mem_centralizer_singleton_iff]
        let xN : N := ⟨x, hXle hxX⟩
        have hcommN := Subgroup.mem_centralizer_iff.mp huCN xN hxX
        exact congrArg Subtype.val hcommN
      have hdvd : 3 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) := by
        rw [← hXcard]
        exact Subgroup.card_dvd_of_le hXleCentU
      have hHcard : Nat.card h.H = 8 := by rw [h.card_H, hk]
      rw [centralizer_involution_card_eq_card_H h hu, hHcard] at hdvd
      norm_num at hdvd
  have hCN : CN = XN :=
    (Subgroup.eq_of_le_of_card_ge hXNleCN (by rw [hCNcard, hXNcard])).symm
  have hXcomm : IsMulCommutative X := by
    let : IsCyclic X := isCyclic_of_prime_card hXcard
    exact IsCyclic.isMulCommutative
  let CX : Subgroup G := Subgroup.centralizer (X : Set G)
  have hXleCX : X ≤ CX := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val
      (hXcomm.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hCX : CX = X := by
    apply le_antisymm
    · intro g hg
      have hgN : g ∈ N := hcase hg
      let gN : N := ⟨g, hgN⟩
      have hgCN : gN ∈ CN := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hxXN
        have hcommG := Subgroup.mem_centralizer_iff.mp hg (x : G) hxXN
        exact Subtype.ext hcommG
      rw [hCN] at hgCN
      exact hgCN
    · exact hXleCX
  have hCX' : Subgroup.centralizer (X : Set G) = X := by
    simpa [CX] using hCX
  have hDcent : ∀ d : G, d ∈ X → d ≠ 1 →
      Subgroup.centralizer ({d} : Set G) = X := by
    intro d hdX hdne
    let dX : X := ⟨d, hdX⟩
    have hdXne : dX ≠ 1 := by
      intro hone
      exact hdne (congrArg Subtype.val hone)
    have hzpTop : Subgroup.zpowers dX = ⊤ :=
      zpowers_eq_top_of_prime_card hXcard hdXne
    have hzpX : Subgroup.zpowers d = X := by
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr hdX
      · intro x hxX
        let xX : X := ⟨x, hxX⟩
        have hxPow : xX ∈ Subgroup.zpowers dX := by
          rw [hzpTop]
          trivial
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxPow
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    calc
      Subgroup.centralizer ({d} : Set G) =
          Subgroup.centralizer (Subgroup.zpowers d : Set G) := by
        rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      _ = Subgroup.centralizer (X : Set G) := by rw [hzpX]
      _ = X := hCX'
  have huNormXN : uN ∈ R := uR.property
  have huN : u ∈ N := uN.property
  have huNormX : u ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at huNormXN ⊢
    intro y
    constructor
    · intro hyX
      let yN : N := ⟨y, hXle hyX⟩
      have hyXN : yN ∈ XN := hyX
      have hconj := (huNormXN yN).mp hyXN
      exact hconj
    · intro hyX
      have hyN : y ∈ N := by
        have hconjN : u * y * u⁻¹ ∈ N := hXle hyX
        have hrecover : u⁻¹ * (u * y * u⁻¹) * u ∈ N :=
          N.mul_mem (N.mul_mem (N.inv_mem huN) hconjN) huN
        simpa [mul_assoc] using hrecover
      let yN : N := ⟨y, hyN⟩
      have hconj : uN * yN * uN⁻¹ ∈ XN := hyX
      exact (huNormXN yN).mpr hconj
  have huX : u ∉ X := by
    intro huX
    have hdvd : 2 ∣ Nat.card X := by
      rw [← huOrder]
      exact Subgroup.orderOf_dvd_natCard X huX
    rw [hXcard] at hdvd
    norm_num at hdvd
  let uNorm : Subgroup.normalizer (X : Set G) := ⟨u, huNormX⟩
  let alpha : MulAut X := Subgroup.normalizerMonoidHom X uNorm
  have huinv : ∀ d : G, d ∈ X → u * d * u⁻¹ = d⁻¹ := by
    rcases mulAut_eq_one_or_apply_eq_inv_of_card_eq_three hXcard alpha with
      halpha | halpha
    · exfalso
      apply huX
      rw [← hCX']
      rw [Subgroup.mem_centralizer_iff]
      intro d hdX
      let dX : X := ⟨d, hdX⟩
      have hfix : alpha dX = dX := by rw [halpha]; rfl
      have hconj : u * d * u⁻¹ = d := by
        simpa [alpha, uNorm,
          Subgroup.normalizerMonoidHom_apply_apply_coe] using
            congrArg Subtype.val hfix
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    · intro d hdX
      let dX : X := ⟨d, hdX⟩
      simpa [alpha, uNorm,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val (halpha dX)
  have hNormX : Subgroup.normalizer (X : Set G) =
      X ⊔ Subgroup.zpowers u := by
    calc
      Subgroup.normalizer (X : Set G) =
          Subgroup.centralizer (X : Set G) ⊔ Subgroup.zpowers u :=
        normalizer_eq_centralizer_sup_zpowers_of_card_eq_three
          X hXcard hu.2 huNormX huinv
      _ = X ⊔ Subgroup.zpowers u := by rw [hCX']
  exact h.conclusion_nonempty_of_card_K_eq_four_of_card_G_eq_168_of_order_three_complement
    hk V X hV hXcard hDcent u hu hNormX huinv hGcard

end CFSG.GorensteinWalter

