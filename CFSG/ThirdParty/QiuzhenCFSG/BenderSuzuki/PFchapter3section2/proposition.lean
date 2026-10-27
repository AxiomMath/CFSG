module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open PFchapter3section1

set_option maxHeartbeats 800000

/-!
# Peterfalvi, Part II, Chapter III, Section 2 Proposition
-/

public theorem proposition
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hch : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    HypothesisC1 G V ∧
      IsSuzukiTwoTypeA S ∧
        orderOf (s * t) = 5 ∧
          W = ⊥)
    (hSQ : S = Q) :
    ∃ L : Subgroup G, (L : Set G) = (({x : G | ∃ a : G, a ∈ S ∧ ∃ b : G, b ∈ K ∧ x = a * b} : Set G) ∪ {x : G | ∃ s₁ : G, s₁ ∈ S ∧ ∃ k : G, k ∈ K ∧ ∃ s₂ : G, s₂ ∈ S ∧ x = s₁ * k * t * s₂}) := by
  let SK : Set G := {x | ∃ a, a ∈ S ∧ ∃ b, b ∈ K ∧ x = a * b}
  let SKtS : Set G :=
    {x | ∃ s1, s1 ∈ S ∧ ∃ k, k ∈ K ∧ ∃ s2, s2 ∈ S ∧
      x = s1 * k * t * s2}
  have ht : t * t = 1 := by
    simpa [pow_two] using hch.1.section2.hA.A1.involution_t.sq_eq_one
  have htInv : t⁻¹ = t := hch.1.section2.hA.A1.involution_t.inv_eq_self
  have hKnormS : ∀ k : G, k ∈ K → ∀ x : G, x ∈ S →
      k * x * k⁻¹ ∈ S := by
    intro k hk x hx
    have hkH : k ∈ H :=
      hch.1.section2.hA.A1.D_le_H (hch.1.section2.K_le_D hk)
    have hxQ : x ∈ Q := by simpa [hSQ] using hx
    let xH : H := ⟨x, hch.1.section2.hA.A1.Q_le_H hxQ⟩
    let kH : H := ⟨k, hkH⟩
    have hmem := hch.1.section2.hA.A1.Q_normal_in_H.conj_mem xH (by
      simpa [xH, Subgroup.mem_subgroupOf] using hxQ) kH
    simpa [xH, kH, hSQ, Subgroup.mem_subgroupOf] using hmem
  have hSuzuki : IsSuzukiTwoGroup S := by
    have hnoncomm : ¬ IsMulCommutative S := by
      intro hcomm
      rcases hch.2.2.1 with
        ⟨n, hn, theta, pairLift, cocycle, _hperiod, htheta,
          haddLeft, haddRight, hdiag, hmem, _hone, _hsurj, hinj, hmul⟩
      rcases htheta with ⟨a, ha⟩
      have hsum_ne : a + theta a ≠ 0 := by
        intro hzero
        apply ha
        have hzero' : theta a + a = 0 := by simpa [add_comm] using hzero
        have hneg : theta a = -a := eq_neg_of_add_eq_zero_left hzero'
        simpa only [CharTwo.neg_eq] using hneg
      have hcoc_ne : cocycle a 1 ≠ cocycle 1 a := by
        intro hcoc
        have hcalc :
            (a + 1) * theta (a + 1) =
              a * theta a + cocycle a 1 + cocycle 1 a + 1 := by
          calc
            (a + 1) * theta (a + 1) = cocycle (a + 1) (a + 1) :=
              (hdiag (a + 1)).symm
            _ = cocycle a (a + 1) + cocycle 1 (a + 1) := by
              rw [haddLeft]
            _ = (cocycle a a + cocycle a 1) +
                (cocycle 1 a + cocycle 1 1) := by rw [haddRight, haddRight]
            _ = a * theta a + cocycle a 1 + cocycle 1 a + 1 := by
              rw [hdiag, hdiag]
              simp only [map_one, mul_one]
              ring
        rw [map_add, map_one] at hcalc
        rw [hcoc] at hcalc
        have hcalc' :
            (a + 1) * (theta a + 1) = a * theta a + 1 := by
          calc
            (a + 1) * (theta a + 1) =
                a * theta a + cocycle 1 a + cocycle 1 a + 1 := hcalc
            _ = a * theta a + (cocycle 1 a + cocycle 1 a) + 1 := by ring
            _ = a * theta a + 1 := by
              rw [CharTwo.add_self_eq_zero]
              simp
        have hcalc'' :
            a * theta a + a + theta a + 1 = a * theta a + 1 := by
          calc
            a * theta a + a + theta a + 1 =
                (a + 1) * (theta a + 1) := by ring
            _ = a * theta a + 1 := hcalc'
        have : a + theta a = 0 := by
          linear_combination hcalc''
        exact hsum_ne this
      let pa : S := ⟨pairLift a 0, hmem a 0⟩
      let p1 : S := ⟨pairLift 1 0, hmem 1 0⟩
      have hcommEq : pairLift a 0 * pairLift 1 0 =
          pairLift 1 0 * pairLift a 0 := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm pa p1)
      rw [hmul, hmul] at hcommEq
      have hcommEq' : pairLift (a + 1) (cocycle a 1) =
          pairLift (a + 1) (cocycle 1 a) := by
        simpa [add_comm] using hcommEq
      exact hcoc_ne
        (hinj (a + 1) (cocycle a 1) (a + 1) (cocycle 1 a) hcommEq').2
    rcases PFchapter1section2.corollary
        H D Q K V W Q0 S Q1 t hch.1.section2 with hcomm | hSuzuki
    · exact False.elim (hnoncomm hcomm)
    · exact hSuzuki
  have hSexpFour : ∀ x : G, x ∈ S → x ^ 4 = 1 := by
    intro x hxS
    have hpow :=
      (higmanTheorem_center_quotient_orders_and_exponent hSuzuki).2.2.2.2
        (⟨x, hxS⟩ : S)
    exact congrArg Subtype.val hpow
  have hsS : s ∈ S := by
    have hsQ0 : s ∈ Q0 :=
      (hch.1.section2.Q0_def s).2
        (Or.inr ⟨hch.1.s_mem_H, hch.1.s_involution⟩)
    have hsQ : s ∈ Q := hch.1.section2.Q0_le_Q hsQ0
    simpa [hSQ] using hsQ
  have hsCenter : (⟨s, hsS⟩ : S) ∈ Subgroup.center S := by
    have hsSubI : IsInvolution (⟨s, hsS⟩ : S) := by
      constructor
      · intro hsOne
        exact hch.1.s_involution.ne_one (congrArg Subtype.val hsOne)
      · apply Subtype.ext
        exact hch.1.s_involution.sq_eq_one
    have hmem : (⟨s, hsS⟩ : S) ∈ involutions S := hsSubI
    rw [(higmanTheorem_involutions_center hSuzuki).1] at hmem
    exact hmem.1
  have hstructure : ∃ r : G, r ∈ S ∧ orderOf r = 4 ∧
      t * s * t = r⁻¹ * t * r := by
    rcases hch.1.s_conjugate with ⟨r, hrQ, hstruct⟩
    have hrS : r ∈ S := by simpa [hSQ] using hrQ
    have hsr : s * r = r * s := by
      exact (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hsCenter (⟨r, hrS⟩ : S))).symm
    have huSquare : (s * t) ^ 2 = r⁻¹ * (s * t) * r := by
      rw [pow_two]
      calc
        s * t * (s * t) = s * (t * s * t) := by group
        _ = s * (r⁻¹ * t * r) := by rw [hstruct]
        _ = r⁻¹ * (s * t) * r := by
          have hsrInv : s * r⁻¹ = r⁻¹ * s := by
            have hcomm : Commute s r := hsr
            exact hcomm.inv_right.eq
          calc
            s * (r⁻¹ * t * r) = (s * r⁻¹) * t * r := by group
            _ = (r⁻¹ * s) * t * r := by rw [hsrInv]
            _ = r⁻¹ * (s * t) * r := by group
    have hrSqNe : r ^ 2 ≠ 1 := by
      intro hrSq
      have huFour : (s * t) ^ 4 = s * t := by
        calc
          (s * t) ^ 4 = ((s * t) ^ 2) ^ 2 := by group
          _ = (r⁻¹ * (s * t) * r) ^ 2 := by rw [huSquare]
          _ = r⁻¹ * ((s * t) ^ 2) * r := by
            simp only [pow_two]
            group
          _ = r⁻¹ * (r⁻¹ * (s * t) * r) * r := by rw [huSquare]
          _ = (r ^ 2)⁻¹ * (s * t) * r ^ 2 := by
            simp only [pow_two]
            group
          _ = s * t := by rw [hrSq]; simp
      have hpows : (s * t) ^ 4 = (s * t) ^ 1 := by simpa using huFour
      have hmod : 4 ≡ 1 [MOD orderOf (s * t)] :=
        (pow_eq_pow_iff_modEq).mp hpows
      rw [hch.2.2.2.1] at hmod
      norm_num [Nat.ModEq] at hmod
    have hrFour : r ^ 4 = 1 := hSexpFour r hrS
    have hrOrder : orderOf r = 4 := by
      have horder := orderOf_eq_prime_pow (p := 2) (n := 1) (x := r)
        (by simpa using hrSqNe) (by norm_num; simpa using hrFour)
      norm_num at horder ⊢
      exact horder
    exact ⟨r, hrS, hrOrder, hstruct⟩
  obtain ⟨r, hrS, hrOrder, hstruct⟩ := hstructure
  have hrNe : r ≠ 1 := by
    intro hrOne
    have : orderOf r = 1 := orderOf_eq_one_iff.mpr hrOne
    omega
  have hrInvS : r⁻¹ ∈ S := S.inv_mem hrS
  have hrInvNe : r⁻¹ ≠ 1 := (inv_ne_one).2 hrNe
  have htrt : t * r * t = r * t * s := by
    have haux : r * (t * s * t) = t * r := by
      rw [hstruct]
      group
    calc
      t * r * t = r * (t * s * t) * t := by rw [haux]
      _ = r * t * s * (t * t) := by group
      _ = r * t * s := by rw [ht]; simp
  have htrInvt : t * r⁻¹ * t = s * t * r⁻¹ := by
    have hinv := congrArg Inv.inv htrt
    simpa only [mul_inv_rev, htInv, hch.1.s_involution.inv_eq_self,
      inv_inv, mul_assoc] using hinv
  let IsRepresentative : G → Prop := fun y =>
    y = s ∨ y = r ∨ y = r⁻¹ ∨
      ∃ k : G, k ∈ K ∧ k ≠ 1 ∧ y = r * rightConjugateElem r⁻¹ k
  have htK : ∀ k : G, k ∈ K → t * k * t ∈ K := by
    intro k hk
    have htk : t * k * t = k⁻¹ := by
      have hkanti := ((hch.1.section2.K_def k).mp hk).2
      simpa [rightConjugateElem, htInv] using hkanti
    simpa [htk] using K.inv_mem hk
  have htxtNotH : ∀ x : G, x ∈ S → x ≠ 1 → t * x * t ∉ H := by
    intro x hxS hxne htxtH
    have hxQ : x ∈ Q := by simpa [hSQ] using hxS
    have hxH : x ∈ H := hch.1.section2.hA.A1.Q_le_H hxQ
    have hxRight : x ∈ rightConjugate H t := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨t * x * t, htxtH, ?_⟩
      calc
        (MulAut.conj t⁻¹) (t * x * t) = t * (t * x * t) * t := by
          simp [MulAut.conj, htInv]
        _ = x := by
          calc
            t * (t * x * t) * t = (t * t) * x * (t * t) := by group
            _ = x := by rw [ht]; simp
    have hxD : x ∈ D := by
      rw [hch.1.section2.hA.A1.D_eq]
      exact ⟨hxH, hxRight⟩
    have hxInf : x ∈ Q ⊓ D := ⟨hxQ, hxD⟩
    have hxOne : x = 1 := by
      have := hch.1.section2.hA.A1.Q_disjoint_D.le_bot hxInf
      simpa using this
    exact hxne hxOne
  have hcanonical : ∀ x : G, x ∈ S → x ≠ 1 →
      ∃ g : G, g ∈ S ∧ ∃ d : G, d ∈ D ∧ ∃ f : G, f ∈ S ∧
        t * x * t = g * d * t * f := by
    intro x hxS hxne
    rcases proposition_4_a H D Q t hch.1.section2.hA.A1
        (t * x * t) (htxtNotH x hxS hxne) with ⟨p, hp, _huniq⟩
    let QH : Subgroup H := Q.subgroupOf H
    let DH : Subgroup H := D.subgroupOf H
    haveI : QH.Normal := by
      simpa [QH] using hch.1.section2.hA.A1.Q_normal_in_H
    have hsupH : QH ⊔ DH = ⊤ := by
      rw [← Subgroup.subgroupOf_sup
        hch.1.section2.hA.A1.Q_le_H hch.1.section2.hA.A1.D_le_H]
      rw [hch.1.section2.hA.A1.Q_sup_D, Subgroup.subgroupOf_self]
    have hp1sup : p.1 ∈ QH ⊔ DH := by
      rw [hsupH]
      trivial
    rcases (Subgroup.mem_sup_of_normal_left
        (s := QH) (t := DH) (x := p.1)).1 hp1sup with
      ⟨qH, hqH, dH, hdH, hqd⟩
    have hqQ : (qH : G) ∈ Q := by simpa [QH, Subgroup.mem_subgroupOf] using hqH
    have hdD : (dH : G) ∈ D := by simpa [DH, Subgroup.mem_subgroupOf] using hdH
    refine ⟨qH, ?_, dH, hdD, p.2, ?_, ?_⟩
    · simpa [hSQ] using hqQ
    · simp [hSQ]
    · have hqdG : (qH : G) * (dH : G) = (p.1 : G) :=
        congrArg Subtype.val hqd
      calc
        t * x * t = (p.1 : G) * t * (p.2 : G) := hp
        _ = (qH : G) * (dH : G) * t * (p.2 : G) := by rw [hqdG]
  have hQDunique : ∀ q1 : G, q1 ∈ Q → ∀ d1 : G, d1 ∈ D →
      ∀ q2 : G, q2 ∈ Q → ∀ d2 : G, d2 ∈ D →
        q1 * d1 = q2 * d2 → d1 = d2 := by
    intro q1 hq1 d1 hd1 q2 hq2 d2 hd2 heq
    have hrel : q2⁻¹ * q1 = d2 * d1⁻¹ := by
      calc
        q2⁻¹ * q1 = q2⁻¹ * (q1 * d1) * d1⁻¹ := by group
        _ = q2⁻¹ * (q2 * d2) * d1⁻¹ := by rw [heq]
        _ = d2 * d1⁻¹ := by group
    have hzInf : q2⁻¹ * q1 ∈ Q ⊓ D := by
      exact ⟨Q.mul_mem (Q.inv_mem hq2) hq1,
        hrel.symm ▸ D.mul_mem hd2 (D.inv_mem hd1)⟩
    have hzOne : q2⁻¹ * q1 = 1 := by
      have := hch.1.section2.hA.A1.Q_disjoint_D.le_bot hzInf
      simpa using this
    have hqeq : q1 = q2 := (inv_mul_eq_one.mp hzOne).symm
    apply mul_left_cancel (a := q1)
    simpa [hqeq] using heq
  have hDcoefficientCovariant :
      ∀ x : G, x ∈ S → x ≠ 1 →
        ∀ g : G, g ∈ S → ∀ d : G, d ∈ D → ∀ f : G, f ∈ S →
          t * x * t = g * d * t * f →
            ∀ a : G, a ∈ K →
              ∀ g' : G, g' ∈ S → ∀ d' : G, d' ∈ D → ∀ f' : G, f' ∈ S →
                t * (a⁻¹ * x * a) * t = g' * d' * t * f' →
                  d' = a * d * a := by
    intro x hxS hxne g hgS d hdD f hfS htxt a haK
      g' hg'S d' hd'D f' hf'S htxt'
    have hta : t * a * t = a⁻¹ := by
      have haanti := ((hch.1.section2.K_def a).mp haK).2
      simpa [rightConjugateElem, htInv] using haanti
    have htaInv : t * a⁻¹ * t = a := by
      have haanti :=
        ((hch.1.section2.K_def a⁻¹).mp (K.inv_mem haK)).2
      simpa [rightConjugateElem, htInv] using haanti
    have hat : a * t * a = t := by
      calc
        a * t * a = (a * (t * a * t)) * t⁻¹ := by group
        _ = (a * a⁻¹) * t⁻¹ := by rw [hta]
        _ = t := by simp [htInv]
    let y : G := a⁻¹ * x * a
    have hyS : y ∈ S := by
      simpa [y] using hKnormS a⁻¹ (K.inv_mem haK) x hxS
    have hyne : y ≠ 1 := by
      intro hyOne
      apply hxne
      calc
        x = a * y * a⁻¹ := by dsimp [y]; group
        _ = 1 := by rw [hyOne]; simp
    let gc : G := a * g * a⁻¹
    let dc : G := a * d * a
    let fc : G := a * f * a⁻¹
    have hgcS : gc ∈ S := hKnormS a haK g hgS
    have hdcD : dc ∈ D :=
      D.mul_mem (D.mul_mem (hch.1.section2.K_le_D haK) hdD)
        (hch.1.section2.K_le_D haK)
    have hfcS : fc ∈ S := hKnormS a haK f hfS
    have hcandidate : t * y * t = gc * dc * t * fc := by
      calc
        t * y * t = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by
          dsimp [y]
          calc
            t * (a⁻¹ * x * a) * t =
                t * a⁻¹ * (t * t) * x * (t * t) * a * t := by
              rw [ht]
              group
            _ = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by group
        _ = a * (g * d * t * f) * a⁻¹ := by rw [htaInv, hta, htxt]
        _ = gc * dc * t * fc := by
          calc
            a * (g * d * t * f) * a⁻¹ = a * g * d * t * f * a⁻¹ := by
              simp [mul_assoc]
            _ = a * g * d * (a * t * a) * f * a⁻¹ := by rw [hat]
            _ = gc * dc * t * fc := by
              dsimp [gc, dc, fc]
              simp [mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left]
    have hgcQ : gc ∈ Q := by simpa [hSQ] using hgcS
    have hg'Q : g' ∈ Q := by simpa [hSQ] using hg'S
    have hgcH : gc ∈ H := hch.1.section2.hA.A1.Q_le_H hgcQ
    have hg'H : g' ∈ H := hch.1.section2.hA.A1.Q_le_H hg'Q
    have hdcH : dc ∈ H := hch.1.section2.hA.A1.D_le_H hdcD
    have hd'H : d' ∈ H := hch.1.section2.hA.A1.D_le_H hd'D
    have hfcQ : fc ∈ Q := by simpa [hSQ] using hfcS
    have hf'Q : f' ∈ Q := by simpa [hSQ] using hf'S
    let pc : H × Q :=
      (⟨gc * dc, H.mul_mem hgcH hdcH⟩, ⟨fc, hfcQ⟩)
    let p' : H × Q :=
      (⟨g' * d', H.mul_mem hg'H hd'H⟩, ⟨f', hf'Q⟩)
    rcases proposition_4_a H D Q t hch.1.section2.hA.A1
        (t * y * t) (htxtNotH y hyS hyne) with ⟨p, hp, huniq⟩
    have hpc : t * y * t = (pc.1 : G) * t * (pc.2 : G) := by
      simpa [pc] using hcandidate
    have hp' : t * y * t = (p'.1 : G) * t * (p'.2 : G) := by
      simpa [p'] using htxt'
    have hpair : pc = p' := (huniq pc hpc).trans (huniq p' hp').symm
    have hleft : gc * dc = g' * d' := by
      exact congrArg (fun z : H × Q => ((z.1 : H) : G)) hpair
    exact (hQDunique gc hgcQ dc hdcD g' hg'Q d' hd'D hleft).symm
  have hcanonicalTransport :
      ∀ x g d f a : G,
        t * x * t = g * d * t * f → a ∈ K →
          t * (a⁻¹ * x * a) * t =
            (a * g * a⁻¹) * (a * d * a) * t * (a * f * a⁻¹) := by
    intro x g d f a hdecomp haK
    have hta : t * a * t = a⁻¹ := by
      have haanti := ((hch.1.section2.K_def a).mp haK).2
      simpa [rightConjugateElem, htInv] using haanti
    have htaInv : t * a⁻¹ * t = a := by
      have haanti :=
        ((hch.1.section2.K_def a⁻¹).mp (K.inv_mem haK)).2
      simpa [rightConjugateElem, htInv] using haanti
    have hat : a * t * a = t := by
      calc
        a * t * a = (a * (t * a * t)) * t⁻¹ := by group
        _ = (a * a⁻¹) * t⁻¹ := by rw [hta]
        _ = t := by simp [htInv]
    calc
      t * (a⁻¹ * x * a) * t =
          (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by
        calc
          t * (a⁻¹ * x * a) * t =
              t * a⁻¹ * (t * t) * x * (t * t) * a * t := by
            rw [ht]
            group
          _ = (t * a⁻¹ * t) * (t * x * t) * (t * a * t) := by group
      _ = a * (g * d * t * f) * a⁻¹ := by rw [htaInv, hta, hdecomp]
      _ = (a * g * a⁻¹) * (a * d * a) * t * (a * f * a⁻¹) := by
        calc
          a * (g * d * t * f) * a⁻¹ = a * g * d * t * f * a⁻¹ := by
              simp [mul_assoc]
            _ = a * g * d * (a * t * a) * f * a⁻¹ := by rw [hat]
            _ = (a * g * a⁻¹) * (a * d * a) * t * (a * f * a⁻¹) := by
              simp [mul_assoc, mul_inv_cancel_right, inv_mul_cancel_left]
  have hcanonicalUnique :
      ∀ x : G, x ∈ S → x ≠ 1 →
        ∀ g₁ : G, g₁ ∈ S → ∀ d₁ : G, d₁ ∈ D → ∀ f₁ : G, f₁ ∈ S →
          t * x * t = g₁ * d₁ * t * f₁ →
            ∀ g₂ : G, g₂ ∈ S → ∀ d₂ : G, d₂ ∈ D → ∀ f₂ : G, f₂ ∈ S →
              t * x * t = g₂ * d₂ * t * f₂ →
                g₁ = g₂ ∧ d₁ = d₂ ∧ f₁ = f₂ := by
    intro x hxS hxNe g₁ hg₁S d₁ hd₁D f₁ hf₁S h₁
      g₂ hg₂S d₂ hd₂D f₂ hf₂S h₂
    have hg₁Q : g₁ ∈ Q := by simpa [hSQ] using hg₁S
    have hg₂Q : g₂ ∈ Q := by simpa [hSQ] using hg₂S
    have hf₁Q : f₁ ∈ Q := by simpa [hSQ] using hf₁S
    have hf₂Q : f₂ ∈ Q := by simpa [hSQ] using hf₂S
    let p₁ : H × Q :=
      (⟨g₁ * d₁, H.mul_mem (hch.1.section2.hA.A1.Q_le_H hg₁Q)
        (hch.1.section2.hA.A1.D_le_H hd₁D)⟩, ⟨f₁, hf₁Q⟩)
    let p₂ : H × Q :=
      (⟨g₂ * d₂, H.mul_mem (hch.1.section2.hA.A1.Q_le_H hg₂Q)
        (hch.1.section2.hA.A1.D_le_H hd₂D)⟩, ⟨f₂, hf₂Q⟩)
    rcases proposition_4_a H D Q t hch.1.section2.hA.A1
        (t * x * t) (htxtNotH x hxS hxNe) with ⟨p, hp, huniq⟩
    have hp₁ : t * x * t = (p₁.1 : G) * t * (p₁.2 : G) := by
      simpa [p₁] using h₁
    have hp₂ : t * x * t = (p₂.1 : G) * t * (p₂.2 : G) := by
      simpa [p₂] using h₂
    have hpEq : p₁ = p₂ := (huniq p₁ hp₁).trans (huniq p₂ hp₂).symm
    have hleft : g₁ * d₁ = g₂ * d₂ :=
      congrArg (fun z : H × Q => ((z.1 : H) : G)) hpEq
    have hdEq : d₁ = d₂ := hQDunique g₁ hg₁Q d₁ hd₁D g₂ hg₂Q d₂ hd₂D hleft
    have hgEq : g₁ = g₂ := by
      apply mul_right_cancel (b := d₂)
      simpa [hdEq] using hleft
    have hfEq : f₁ = f₂ :=
      congrArg (fun z : H × Q => ((z.2 : Q) : G)) hpEq
    exact ⟨hgEq, hdEq, hfEq⟩
  have hKcyclic : IsCyclic K :=
    (PFchapter1section2.proposition_2
      H D Q K V W Q0 S Q1 t hch.1.section2).1
  letI : IsCyclic K := hKcyclic
  have hKcomm : ∀ a : G, a ∈ K → ∀ b : G, b ∈ K → a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := K)).comm
        (⟨a, ha⟩ : K) (⟨b, hb⟩ : K))
  have hrrCanonicalData : ∀ k : G, k ∈ K → k ≠ 1 →
      ∀ g : G, g ∈ S → ∀ d : G, d ∈ D → ∀ f : G, f ∈ S →
        t * (r * rightConjugateElem r⁻¹ k) * t = g * d * t * f →
          ∃ ell : G, ell ∈ K ∧
            rightConjugateElem s ell = s * (k * s * k⁻¹) ∧
            ell ≠ 1 ∧ k * ell ≠ 1 ∧
            ∃ g0 : G, g0 = r * rightConjugateElem r⁻¹ ell⁻¹ ∧
              ∃ d0 : G, d0 = ell ^ 2 * k ^ 2 ∧
                ∃ f0 : G,
                  f0 = rightConjugateElem r (ell⁻¹ * (k ^ 2)⁻¹) *
                    rightConjugateElem r⁻¹ k⁻¹ ∧
                  g = g0 ∧ d = d0 ∧ f = f0 := by
    intro k hkK hkNe g hgS d hdD f hfS hdecomp
    let sk : G := k * s * k⁻¹
    have hskS : sk ∈ S := hKnormS k hkK s hsS
    have hsksq : sk ^ 2 = 1 := by
      dsimp [sk]
      calc
        (k * s * k⁻¹) ^ 2 = k * (s ^ 2) * k⁻¹ := by
          simp only [pow_two]
          group
        _ = 1 := by rw [hch.1.s_involution.sq_eq_one]; simp
    have hskne : sk ≠ 1 := by
      intro hskOne
      apply hch.1.s_involution.ne_one
      calc
        s = k⁻¹ * sk * k := by dsimp [sk]; group
        _ = 1 := by rw [hskOne]; simp
    have hskI : IsInvolution sk := ⟨hskne, hsksq⟩
    have hcomm : Commute s sk := by
      exact (congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hsCenter (⟨sk, hskS⟩ : S))).symm
    have hsk_ne_s : sk ≠ s := by
      intro hskeq
      have hks : k * s = s * k := by
        calc
          k * s = sk * k := by dsimp [sk]; group
          _ = s * k := by rw [hskeq]
      have hsCentral : s ∈ Subgroup.centralizer ({k} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hks
      have hsQ : s ∈ Q := by simpa [hSQ] using hsS
      have hsInf : s ∈ Subgroup.centralizer ({k} : Set G) ⊓ Q :=
        ⟨hsCentral, hsQ⟩
      have hsBot : s ∈ (⊥ : Subgroup G) := by
        simpa [PFchapter1section2.proposition_1_a
          H D Q K V W Q0 S Q1 t hch.1.section2 k hkK hkNe] using hsInf
      exact hch.1.s_involution.ne_one (by simpa using hsBot)
    let y : G := s * sk
    have hyS : y ∈ S := S.mul_mem hsS hskS
    have hyne : y ≠ 1 := by
      intro hyOne
      have hskeq : sk = s := by
        calc
          sk = s⁻¹ := by
            have := congrArg (fun z : G => s⁻¹ * z) hyOne
            simpa [y] using this
          _ = s := hch.1.s_involution.inv_eq_self
      exact hsk_ne_s hskeq
    have hysq : y ^ 2 = 1 := by
      calc
        y ^ 2 = s ^ 2 * sk ^ 2 := by
          dsimp [y]
          exact hcomm.mul_pow 2
        _ = 1 := by rw [hch.1.s_involution.sq_eq_one, hsksq]; simp
    have hyI : IsInvolution y := ⟨hyne, hysq⟩
    have hyH : y ∈ H :=
      hch.1.section2.hA.A1.Q_le_H (by simpa [hSQ] using hyS)
    rcases ((PFchapter1section1.proposition_3 H D Q t
        hch.1.section2.hA.A1).2 s hch.1.s_mem_H hch.1.s_involution y).1
        ⟨hyH, hyI⟩ with ⟨ell, hellSet, hell⟩
    have hellK : ell ∈ K :=
      (hch.1.section2.K_def ell).2 hellSet
    let rr : G := r * rightConjugateElem r⁻¹ k
    have hrConjS : rightConjugateElem r⁻¹ k ∈ S := by
      simpa [rightConjugateElem] using
        hKnormS k⁻¹ (K.inv_mem hkK) r⁻¹ hrInvS
    have hrrS : rr ∈ S := S.mul_mem hrS hrConjS
    have hrrNe : rr ≠ 1 := by
      intro hrrOne
      have hrConj : rightConjugateElem r⁻¹ k = r⁻¹ := by
        have := congrArg (fun z : G => r⁻¹ * z) hrrOne
        simpa [rr] using this
      have hrk : r * k = k * r := by
        dsimp [rightConjugateElem] at hrConj
        have hconjR : k⁻¹ * r * k = r := by
          have hinv := congrArg Inv.inv hrConj
          simpa [mul_assoc] using hinv
        calc
          r * k = k * (k⁻¹ * r * k) := by group
          _ = k * r := by rw [hconjR]
      have hrCentral : r ∈ Subgroup.centralizer ({k} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact hrk.symm
      have hrQ : r ∈ Q := by simpa [hSQ] using hrS
      have hrInf : r ∈ Subgroup.centralizer ({k} : Set G) ⊓ Q :=
        ⟨hrCentral, hrQ⟩
      have hrBot : r ∈ (⊥ : Subgroup G) := by
        simpa [PFchapter1section2.proposition_1_a
          H D Q K V W Q0 S Q1 t hch.1.section2 k hkK hkNe] using hrInf
      exact hrNe (by simpa using hrBot)
    let d0 : G := ell ^ 2 * k ^ 2
    have hd0K : d0 ∈ K := K.mul_mem (K.pow_mem hellK 2) (K.pow_mem hkK 2)
    let a0 : G := ell⁻¹ * (k ^ 2)⁻¹
    let g0 : G := r * rightConjugateElem r⁻¹ ell⁻¹
    let f0 : G :=
      rightConjugateElem r a0 * rightConjugateElem r⁻¹ k⁻¹
    have hdisplayed : g0 ∈ S ∧ f0 ∈ S ∧
        t * rr * t = g0 * d0 * t * f0 := by
      have ha0K : a0 ∈ K :=
        K.mul_mem (K.inv_mem hellK) (K.inv_mem (K.pow_mem hkK 2))
      have hrightConjS : ∀ z : G, z ∈ S → ∀ a : G, a ∈ K →
          rightConjugateElem z a ∈ S := by
        intro z hz a ha
        simpa [rightConjugateElem] using
          hKnormS a⁻¹ (K.inv_mem ha) z hz
      have hg0S : g0 ∈ S := by
        exact S.mul_mem hrS
          (hrightConjS r⁻¹ hrInvS ell⁻¹ (K.inv_mem hellK))
      have hf0S : f0 ∈ S := by
        exact S.mul_mem
          (hrightConjS r hrS a0 ha0K)
          (hrightConjS r⁻¹ hrInvS k⁻¹ (K.inv_mem hkK))
      have htk : t * k * t = k⁻¹ := by
        have hkanti := ((hch.1.section2.K_def k).mp hkK).2
        simpa [rightConjugateElem, htInv] using hkanti
      have htkInv : t * k⁻¹ * t = k := by
        have hkanti :=
          ((hch.1.section2.K_def k⁻¹).mp (K.inv_mem hkK)).2
        simpa [rightConjugateElem, htInv] using hkanti
      have htEllInv : t * ell⁻¹ * t = ell := by
        have hanti :=
          ((hch.1.section2.K_def ell⁻¹).mp (K.inv_mem hellK)).2
        simpa [rightConjugateElem, htInv] using hanti
      have hta0 : t * a0 * t = a0⁻¹ := by
        have hanti := ((hch.1.section2.K_def a0).mp ha0K).2
        simpa [rightConjugateElem, htInv] using hanti
      have htrConjInvt :
          t * rightConjugateElem r⁻¹ k * t =
            k * (s * t * r⁻¹) * k⁻¹ := by
        calc
          t * rightConjugateElem r⁻¹ k * t =
              t * k⁻¹ * (t * t) * r⁻¹ * (t * t) * k * t := by
            rw [rightConjugateElem, ht]
            group
          _ = (t * k⁻¹ * t) * (t * r⁻¹ * t) * (t * k * t) := by
            group
          _ = k * (s * t * r⁻¹) * k⁻¹ := by
            rw [htkInv, htrInvt, htk]
      have hskFactor : s * k * s = ell⁻¹ * s * ell * k := by
        have hskell : s * k * s * k⁻¹ = ell⁻¹ * s * ell := by
          calc
            s * k * s * k⁻¹ = y := by
              dsimp [y, sk]
              group
            _ = rightConjugateElem s ell := hell.symm
            _ = ell⁻¹ * s * ell := by rfl
        calc
          s * k * s = (s * k * s * k⁻¹) * k := by group
          _ = (ell⁻¹ * s * ell) * k := by rw [hskell]
          _ = ell⁻¹ * s * ell * k := by group
      have hellkInv : (ell * k)⁻¹ = ell⁻¹ * k⁻¹ := by
        rw [mul_inv_rev]
        exact hKcomm k⁻¹ (K.inv_mem hkK) ell⁻¹ (K.inv_mem hellK)
      have hsourceTail :
          (ell * k)⁻¹ * r⁻¹ * k⁻¹ =
            a0 * rightConjugateElem r⁻¹ k⁻¹ := by
        rw [hellkInv]
        dsimp [a0]
        simp only [rightConjugateElem, inv_inv]
        group
      have hcoeff : ell * a0⁻¹ = d0 := by
        have hcommPow : ell * k ^ 2 = k ^ 2 * ell :=
          hKcomm ell hellK (k ^ 2) (K.pow_mem hkK 2)
        dsimp [a0, d0]
        rw [mul_inv_rev, inv_inv, inv_inv]
        calc
          ell * (k ^ 2 * ell) = ell * (ell * k ^ 2) := by rw [hcommPow]
          _ = ell ^ 2 * k ^ 2 := by simp only [pow_two]; group
      have ha0InvT : a0⁻¹ * t * a0⁻¹ = t := by
        calc
          a0⁻¹ * t * a0⁻¹ = (t * a0 * t) * t * a0⁻¹ := by rw [hta0]
          _ = t * a0 * (t * t) * a0⁻¹ := by group
          _ = t := by rw [ht]; group
      have hfinalFactor :
          r * ell * r⁻¹ * t * r * a0 * rightConjugateElem r⁻¹ k⁻¹ =
            g0 * (ell * a0⁻¹) * t * f0 := by
        symm
        dsimp [g0, f0]
        simp only [rightConjugateElem, inv_inv]
        calc
          r * (ell * r⁻¹ * ell⁻¹) * (ell * a0⁻¹) * t *
                (a0⁻¹ * r * a0 * (k * r⁻¹ * k⁻¹)) =
              r * (ell * r⁻¹ * ell⁻¹) * ell *
                (a0⁻¹ * t * a0⁻¹) * r * a0 *
                  (k * r⁻¹ * k⁻¹) := by group
          _ = r * (ell * r⁻¹ * ell⁻¹) * ell * t * r * a0 *
                (k * r⁻¹ * k⁻¹) := by rw [ha0InvT]
          _ = r * ell * r⁻¹ * t * r * a0 * (k * r⁻¹ * k⁻¹) := by
            group
      refine ⟨hg0S, hf0S, ?_⟩
      calc
        t * rr * t = (t * r * t) *
            (t * rightConjugateElem r⁻¹ k * t) := by
          dsimp [rr]
          calc
            t * (r * rightConjugateElem r⁻¹ k) * t =
                t * r * (t * t) * rightConjugateElem r⁻¹ k * t := by
              rw [ht]
              group
            _ = (t * r * t) * (t * rightConjugateElem r⁻¹ k * t) := by
              group
        _ = r * t * s * k * (s * t * r⁻¹) * k⁻¹ := by
          rw [htrt, htrConjInvt]
          group
        _ = r * t * (ell⁻¹ * s * ell * k) * t * r⁻¹ * k⁻¹ := by
          rw [← hskFactor]
          group
        _ = r * ell * (t * s * t) * (t * (ell * k) * t) * r⁻¹ * k⁻¹ := by
          calc
            r * t * (ell⁻¹ * s * ell * k) * t * r⁻¹ * k⁻¹ =
                r * t * ell⁻¹ * (t * t) * s * (t * t) *
                  (ell * k) * t * r⁻¹ * k⁻¹ := by
              rw [ht]
              group
            _ = r * (t * ell⁻¹ * t) * (t * s * t) *
                  (t * (ell * k) * t) * r⁻¹ * k⁻¹ := by group
            _ = r * ell * (t * s * t) * (t * (ell * k) * t) *
                  r⁻¹ * k⁻¹ := by rw [htEllInv]
        _ = r * ell * (r⁻¹ * t * r) * (ell * k)⁻¹ * r⁻¹ * k⁻¹ := by
          rw [hstruct]
          have hanti :=
            ((hch.1.section2.K_def (ell * k)).mp
              (K.mul_mem hellK hkK)).2
          rw [show t * (ell * k) * t = (ell * k)⁻¹ by
            simpa [rightConjugateElem, htInv] using hanti]
        _ = r * ell * r⁻¹ * t * r * a0 *
            rightConjugateElem r⁻¹ k⁻¹ := by
          calc
            r * ell * (r⁻¹ * t * r) * (ell * k)⁻¹ * r⁻¹ * k⁻¹ =
                r * ell * (r⁻¹ * t * r) *
                  ((ell * k)⁻¹ * r⁻¹ * k⁻¹) := by group
            _ = r * ell * (r⁻¹ * t * r) *
                  (a0 * rightConjugateElem r⁻¹ k⁻¹) := by rw [hsourceTail]
            _ = r * ell * r⁻¹ * t * r * a0 *
                  rightConjugateElem r⁻¹ k⁻¹ := by group
        _ = g0 * (ell * a0⁻¹) * t * f0 := by
          exact hfinalFactor
        _ = g0 * d0 * t * f0 := by rw [hcoeff]
    rcases hdisplayed with ⟨hg0S, hf0S, hdisplayed⟩
    have hdEq := hDcoefficientCovariant rr hrrS hrrNe
      g0 hg0S d0 (hch.1.section2.K_le_D hd0K) f0 hf0S hdisplayed
      1 K.one_mem g hgS d hdD f hfS (by simpa [rr] using hdecomp)
    have hdEq' : d = d0 := by simpa using hdEq
    have hellNe : ell ≠ 1 := by
      intro hellOne
      have hsy : s = y := by simpa [hellOne, rightConjugateElem] using hell
      apply hskne
      have := congrArg (fun z : G => s⁻¹ * z) hsy
      simpa [y] using this.symm
    have hkellNe : k * ell ≠ 1 := by
      intro hkellOne
      have hellEq : ell = k⁻¹ := by
        calc
          ell = k⁻¹ * (k * ell) := by group
          _ = k⁻¹ := by rw [hkellOne]; simp
      have hsky : sk = y := by
        calc
          sk = rightConjugateElem s ell := by
            simp [sk, hellEq, rightConjugateElem, mul_assoc]
          _ = y := hell
      apply hch.1.s_involution.ne_one
      have := congrArg (fun z : G => z * sk⁻¹) hsky
      simpa [y] using this.symm
    have hg0Q : g0 ∈ Q := by simpa [hSQ] using hg0S
    have hgQ : g ∈ Q := by simpa [hSQ] using hgS
    have hg0H : g0 ∈ H := hch.1.section2.hA.A1.Q_le_H hg0Q
    have hgH : g ∈ H := hch.1.section2.hA.A1.Q_le_H hgQ
    have hd0D : d0 ∈ D := hch.1.section2.K_le_D hd0K
    have hd0H : d0 ∈ H := hch.1.section2.hA.A1.D_le_H hd0D
    have hdH : d ∈ H := hch.1.section2.hA.A1.D_le_H hdD
    have hf0Q : f0 ∈ Q := by simpa [hSQ] using hf0S
    have hfQ : f ∈ Q := by simpa [hSQ] using hfS
    let p0 : H × Q :=
      (⟨g0 * d0, H.mul_mem hg0H hd0H⟩, ⟨f0, hf0Q⟩)
    let p1 : H × Q :=
      (⟨g * d, H.mul_mem hgH hdH⟩, ⟨f, hfQ⟩)
    rcases proposition_4_a H D Q t hch.1.section2.hA.A1
        (t * rr * t) (htxtNotH rr hrrS hrrNe) with ⟨p, hp, huniq⟩
    have hp0 : t * rr * t = (p0.1 : G) * t * (p0.2 : G) := by
      simpa [p0] using hdisplayed
    have hp1 : t * rr * t = (p1.1 : G) * t * (p1.2 : G) := by
      simpa [p1, rr] using hdecomp
    have hpEq : p0 = p1 := (huniq p0 hp0).trans (huniq p1 hp1).symm
    have hleft : g0 * d0 = g * d :=
      congrArg (fun z : H × Q => ((z.1 : H) : G)) hpEq
    have hfEq : f = f0 := by
      exact (congrArg (fun z : H × Q => ((z.2 : Q) : G)) hpEq).symm
    have hgEq : g = g0 := by
      have hleft' : g0 * d0 = g * d0 := by simpa [hdEq'] using hleft
      exact (mul_right_cancel hleft').symm
    exact ⟨ell, hellK, by simpa [y, sk] using hell, hellNe, hkellNe,
      g0, rfl, d0, rfl, f0, rfl, hgEq, hdEq', hfEq⟩
  have hrrCoefficient : ∀ k : G, k ∈ K → k ≠ 1 →
      ∀ g : G, g ∈ S → ∀ d : G, d ∈ D → ∀ f : G, f ∈ S →
        t * (r * rightConjugateElem r⁻¹ k) * t = g * d * t * f →
          d ∈ K := by
    intro k hkK hkNe g hgS d hdD f hfS hdecomp
    rcases hrrCanonicalData k hkK hkNe g hgS d hdD f hfS hdecomp with
      ⟨ell, hellK, _hellDef, _hellNe, _hkellNe,
        g0, _hg0, d0, hd0, f0, _hf0, _hgEq, hdEq, _hfEq⟩
    rw [hdEq, hd0]
    exact K.mul_mem (K.pow_mem hellK 2) (K.pow_mem hkK 2)
  have horbitRepresentatives : ∀ x : G, x ∈ S → x ≠ 1 →
      ∃ a : G, a ∈ K ∧ IsRepresentative (a⁻¹ * x * a) := by
    let RepParam := Fin 3 ⊕ {k : K // (k : G) ≠ 1}
    let SSharp := {x : G // x ∈ S ∧ x ≠ 1}
    let representative : RepParam → G := fun i =>
      match i with
      | Sum.inl j => if j = 0 then s else if j = 1 then r else r⁻¹
      | Sum.inr k => r * rightConjugateElem r⁻¹ (k : G)
    have hrightConjS : ∀ z : G, z ∈ S → ∀ a : G, a ∈ K →
        rightConjugateElem z a ∈ S := by
      intro z hz a ha
      simpa [rightConjugateElem] using
        hKnormS a⁻¹ (K.inv_mem ha) z hz
    have hrightConjNe : ∀ z : G, z ≠ 1 → ∀ a : G,
        rightConjugateElem z a ≠ 1 := by
      intro z hz a hza
      apply hz
      calc
        z = a * rightConjugateElem z a * a⁻¹ := by
          simp [rightConjugateElem, mul_assoc]
        _ = 1 := by rw [hza]; simp
    have hKfreeOnSSharp : ∀ z : G, z ∈ S → z ≠ 1 →
        ∀ a : G, a ∈ K → rightConjugateElem z a = z → a = 1 := by
      intro z hzS hzNe a haK hfix
      by_contra haNe
      have hza : z * a = a * z := by
        calc
          z * a = a * (a⁻¹ * z * a) := by group
          _ = a * z := by simpa [rightConjugateElem] using congrArg (a * ·) hfix
      have hzCentral : z ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff.mp hb]
        exact hza.symm
      have hzQ : z ∈ Q := by simpa [hSQ] using hzS
      have hzBot : z ∈ (⊥ : Subgroup G) := by
        simpa [PFchapter1section2.proposition_1_a
          H D Q K V W Q0 S Q1 t hch.1.section2 a haK haNe] using
            (show z ∈ Subgroup.centralizer ({a} : Set G) ⊓ Q from
              ⟨hzCentral, hzQ⟩)
      exact hzNe (by simpa using hzBot)
    have hrepresentativeMem : ∀ i : RepParam, representative i ∈ S := by
      intro i
      rcases i with i | k
      · fin_cases i <;> simp [representative, hsS, hrS, hrInvS]
      · exact S.mul_mem hrS
          (hrightConjS r⁻¹ hrInvS (k : G) k.1.property)
    have hrepresentativeNe : ∀ i : RepParam, representative i ≠ 1 := by
      intro i
      rcases i with i | k
      · fin_cases i
        · simpa [representative] using hch.1.s_involution.ne_one
        · simpa [representative] using hrNe
        · simpa [representative] using hrInvNe
      · intro hrrOne
        have hconjFix : rightConjugateElem r⁻¹ (k : G) = r⁻¹ := by
          have := congrArg (fun z : G => r⁻¹ * z) hrrOne
          simpa [representative] using this
        exact k.2 (hKfreeOnSSharp r⁻¹ hrInvS hrInvNe
          (k : G) k.1.property hconjFix)
    have hrepresentativeShape : ∀ i : RepParam,
        IsRepresentative (representative i) := by
      intro i
      rcases i with i | k
      · fin_cases i
        · exact Or.inl (by simp [representative])
        · exact Or.inr (Or.inl (by simp [representative]))
        · exact Or.inr (Or.inr (Or.inl (by simp [representative])))
      · exact Or.inr (Or.inr (Or.inr
          ⟨(k : G), k.1.property, k.2, by simp [representative]⟩))
    have hrepresentativeOrbitSeparate :
        ∀ i j : RepParam, ∀ a : G, a ∈ K →
          rightConjugateElem (representative i) a = representative j → i = j := by
      let KSharp := {k : K // (k : G) ≠ 1}
      let rrOf : KSharp → G := fun k =>
        r * rightConjugateElem r⁻¹ (k : G)
      let SameOrbit : G → G → Prop := fun x y =>
        ∃ a : G, a ∈ K ∧ rightConjugateElem x a = y
      have hsameOrbitSymm : ∀ x y : G, SameOrbit x y → SameOrbit y x := by
        intro x y hxy
        rcases hxy with ⟨a, haK, rfl⟩
        refine ⟨a⁻¹, K.inv_mem haK, ?_⟩
        rw [rightConjugateElem_comp]
        simp [rightConjugateElem]
      have horderRightConj : ∀ x a : G,
          orderOf (rightConjugateElem x a) = orderOf x := by
        intro x a
        simpa [rightConjugateElem, MulAut.conj_symm_apply] using
          (MulEquiv.orderOf_eq (MulAut.conj a).symm x)
      have hsOrder : orderOf s = 2 := by
        rw [orderOf_eq_prime hch.1.s_involution.sq_eq_one
          hch.1.s_involution.ne_one]
      have hbaseOrbitSeparate :
          ¬ SameOrbit s r ∧ ¬ SameOrbit s r⁻¹ ∧ ¬ SameOrbit r r⁻¹ := by
        constructor
        · rintro ⟨a, haK, ha⟩
          have hord := horderRightConj s a
          rw [ha, hsOrder, hrOrder] at hord
          omega
        constructor
        · rintro ⟨a, haK, ha⟩
          have hord := horderRightConj s a
          rw [ha, hsOrder, orderOf_inv, hrOrder] at hord
          omega
        · rintro ⟨a, haK, ha⟩
          have hfix : rightConjugateElem r (a * a) = r := by
            calc
              rightConjugateElem r (a * a) =
                  rightConjugateElem (rightConjugateElem r a) a :=
                (rightConjugateElem_comp r a a).symm
              _ = rightConjugateElem r⁻¹ a := by rw [ha]
              _ = (rightConjugateElem r a)⁻¹ := by
                simp [rightConjugateElem, mul_assoc]
              _ = r := by rw [ha]; simp
          have haa : a * a = 1 :=
            hKfreeOnSSharp r hrS hrNe (a * a) (K.mul_mem haK haK) hfix
          have haOne : a = 1 := by
            by_contra haNe
            exact PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
              D hch.1.section2.hA.A1.D_odd (hch.1.section2.K_le_D haK)
              ⟨haNe, by simpa [pow_two] using haa⟩
          have hrEq : r = r⁻¹ := by
            simpa [haOne, rightConjugateElem] using ha
          have hrSq : r ^ 2 = 1 := by
            simpa [pow_two] using congrArg (fun z : G => z * r) hrEq
          have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one hrSq
          rw [hrOrder] at hdvd
          norm_num at hdvd
      have hrrOrder : ∀ k : KSharp, orderOf (rrOf k) = 4 := by
        intro k
        have hrrS' : rrOf k ∈ S := by
          simpa [rrOf, representative] using
            hrepresentativeMem (Sum.inr k : RepParam)
        have hrrNe' : rrOf k ≠ 1 := by
          simpa [rrOf, representative] using
            hrepresentativeNe (Sum.inr k : RepParam)
        have hrSqNe' : r ^ 2 ≠ 1 := by
          intro hrSq
          have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one hrSq
          rw [hrOrder] at hdvd
          norm_num at hdvd
        have hrrSqNe : rrOf k ^ 2 ≠ 1 := by
          intro hrrSq
          have hrrI : IsInvolution (rrOf k) := ⟨hrrNe', hrrSq⟩
          have hrrSubI : IsInvolution (⟨rrOf k, hrrS'⟩ : S) := by
            constructor
            · intro hone
              exact hrrNe' (congrArg Subtype.val hone)
            · apply Subtype.ext
              exact hrrSq
          have hrrCenter :
              (⟨rrOf k, hrrS'⟩ : S) ∈ Subgroup.center S := by
            have hmem : (⟨rrOf k, hrrS'⟩ : S) ∈ involutions S := hrrSubI
            rw [(higmanTheorem_involutions_center hSuzuki).1] at hmem
            exact hmem.1
          have hcomm : Commute (rrOf k) r := by
            exact (congrArg Subtype.val
              (Subgroup.mem_center_iff.mp hrrCenter (⟨r, hrS⟩ : S))).symm
          have hxEq :
              rightConjugateElem r⁻¹ (k : G) = r⁻¹ * rrOf k := by
            dsimp [rrOf]
            group
          have hrConjEq : rightConjugateElem r (k : G) = rrOf k * r := by
            calc
              rightConjugateElem r (k : G) =
                  (rightConjugateElem r⁻¹ (k : G))⁻¹ := by
                simp [rightConjugateElem, mul_assoc]
              _ = (r⁻¹ * rrOf k)⁻¹ := by rw [hxEq]
              _ = rrOf k * r := by
                rw [mul_inv_rev, hrrI.inv_eq_self, inv_inv]
          have hfixR2 :
              rightConjugateElem (r ^ 2) (k : G) = r ^ 2 := by
            calc
              rightConjugateElem (r ^ 2) (k : G) =
                  rightConjugateElem r (k : G) ^ 2 := by
                simp [rightConjugateElem, pow_two, mul_assoc]
              _ = (rrOf k * r) ^ 2 := by rw [hrConjEq]
              _ = rrOf k ^ 2 * r ^ 2 := hcomm.mul_pow 2
              _ = r ^ 2 := by rw [hrrSq]; simp
          exact k.2 (hKfreeOnSSharp (r ^ 2) (S.pow_mem hrS 2) hrSqNe'
            (k : G) k.1.property hfixR2)
        have hrrFour : rrOf k ^ 4 = 1 := hSexpFour (rrOf k) hrrS'
        have horder := orderOf_eq_prime_pow (p := 2) (n := 1) (x := rrOf k)
          (by simpa using hrrSqNe) (by norm_num; simpa using hrrFour)
        norm_num at horder ⊢
        exact horder
      have hrrNotS : ∀ k : KSharp, ¬ SameOrbit (rrOf k) s := by
        intro k hks
        rcases hks with ⟨a, haK, ha⟩
        have hord := horderRightConj (rrOf k) a
        rw [ha, hrrOrder k, hsOrder] at hord
        omega
      have hrrNotRorInv : ∀ k : KSharp,
          ¬ SameOrbit (rrOf k) r ∧ ¬ SameOrbit (rrOf k) r⁻¹ := by
        intro k
        have hxS : rrOf k ∈ S := by
          simpa [rrOf, representative] using
            hrepresentativeMem (Sum.inr k : RepParam)
        have hxNe : rrOf k ≠ 1 := by
          simpa [rrOf, representative] using
            hrepresentativeNe (Sum.inr k : RepParam)
        rcases hcanonical (rrOf k) hxS hxNe with
          ⟨g, hgS, d, hdD, f, hfS, hdecomp⟩
        rcases hrrCanonicalData (k : G) k.1.property k.2
            g hgS d hdD f hfS (by simpa [rrOf] using hdecomp) with
          ⟨ell, hellK, _hellDef, hellNe, hkellNe,
            g0, hg0, d0, hd0, f0, hf0, hgEq, hdEq, hfEq⟩
        let ellSharp : KSharp :=
          ⟨⟨ell⁻¹, K.inv_mem hellK⟩, (inv_ne_one).2 hellNe⟩
        let kellSharp : KSharp :=
          ⟨⟨(k : G) * ell, K.mul_mem k.1.property hellK⟩, hkellNe⟩
        let a0 : G := ell⁻¹ * ((k : G) ^ 2)⁻¹
        have hgOrder : orderOf g = 4 := by
          rw [hgEq, hg0]
          simpa [rrOf, ellSharp] using hrrOrder ellSharp
        have hfAsConj : f0 = rightConjugateElem (rrOf kellSharp) a0 := by
          rw [hf0]
          dsimp [rrOf, kellSharp, a0]
          simp only [rightConjugateElem, mul_inv_rev, inv_inv]
          group
        have hfOrder : orderOf f = 4 := by
          calc
            orderOf f = orderOf f0 := congrArg orderOf hfEq
            _ = orderOf (rightConjugateElem (rrOf kellSharp) a0) := by
              rw [hfAsConj]
            _ = orderOf (rrOf kellSharp) := horderRightConj (rrOf kellSharp) a0
            _ = 4 := hrrOrder kellSharp
        have htransportData : ∀ a : G, a ∈ K →
            ∀ target : G, rightConjugateElem (rrOf k) a = target →
              let gc := a * g * a⁻¹
              let dc := a * d * a
              let fc := a * f * a⁻¹
              gc ∈ S ∧ dc ∈ D ∧ fc ∈ S ∧
                t * target * t = gc * dc * t * fc := by
          intro a haK target ha
          dsimp
          refine ⟨hKnormS a haK g hgS,
            D.mul_mem (D.mul_mem (hch.1.section2.K_le_D haK) hdD)
              (hch.1.section2.K_le_D haK),
            hKnormS a haK f hfS, ?_⟩
          rw [← ha]
          simpa [rightConjugateElem] using
            hcanonicalTransport (rrOf k) g d f a hdecomp haK
        constructor
        · rintro ⟨a, haK, ha⟩
          rcases htransportData a haK r ha with
            ⟨hgcS, hdcD, hfcS, htrans⟩
          let gc := a * g * a⁻¹
          let dc := a * d * a
          let fc := a * f * a⁻¹
          have huniq := hcanonicalUnique r hrS hrNe
            gc hgcS dc hdcD fc hfcS htrans
            r hrS 1 D.one_mem s hsS (by simpa using htrt)
          have hfcOrder : orderOf fc = 4 := by
            calc
              orderOf fc = orderOf (rightConjugateElem f a⁻¹) := by
                simp [fc, rightConjugateElem, mul_assoc]
              _ = orderOf f := horderRightConj f a⁻¹
              _ = 4 := hfOrder
          rw [huniq.2.2, hsOrder] at hfcOrder
          omega
        · rintro ⟨a, haK, ha⟩
          rcases htransportData a haK r⁻¹ ha with
            ⟨hgcS, hdcD, hfcS, htrans⟩
          let gc := a * g * a⁻¹
          let dc := a * d * a
          let fc := a * f * a⁻¹
          have huniq := hcanonicalUnique r⁻¹ hrInvS hrInvNe
            gc hgcS dc hdcD fc hfcS htrans
            s hsS 1 D.one_mem r⁻¹ hrInvS (by simpa using htrInvt)
          have hgcOrder : orderOf gc = 4 := by
            calc
              orderOf gc = orderOf (rightConjugateElem g a⁻¹) := by
                simp [gc, rightConjugateElem, mul_assoc]
              _ = orderOf g := horderRightConj g a⁻¹
              _ = 4 := hgOrder
          rw [huniq.1, hsOrder] at hgcOrder
          omega
      have hrrOrbitInjective : ∀ k₁ k₂ : KSharp,
          SameOrbit (rrOf k₁) (rrOf k₂) → k₁ = k₂ := by
        have hKleNormalizer : K ≤ Subgroup.normalizer (S : Set G) := by
          intro k hkK
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · exact hKnormS k hkK x
          · intro hx
            have hback := hKnormS k⁻¹ (K.inv_mem hkK)
              (k * x * k⁻¹) hx
            simpa [mul_assoc] using hback
        letI : Subgroup.Normalizes K S := ⟨hKleNormalizer⟩
        have hactualFaithful : FaithfulSMul K S := by
          rw [faithfulSMul_iff]
          intro k hkfix
          let rS : S := ⟨r, hrS⟩
          have hfixS : k • rS = rS := hkfix rS
          have hright :
              rightConjugateElem r ((k⁻¹ : K) : G) = r := by
            simpa [rightConjugateElem,
              Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
                congrArg Subtype.val hfixS
          have hkInvG : ((k⁻¹ : K) : G) = 1 :=
            hKfreeOnSSharp r hrS hrNe ((k⁻¹ : K) : G)
              (k⁻¹ : K).property hright
          have hkInv : k⁻¹ = (1 : K) := by
            apply Subtype.ext
            exact hkInvG
          simpa using congrArg Inv.inv hkInv
        have hactualRegular : ActionRegularOn K S (involutions S) := by
          have involutionCoe : ∀ x : S, IsInvolution x →
              IsInvolution (x : G) := by
            intro x hx
            constructor
            · intro hxOne
              exact hx.ne_one (Subtype.ext hxOne)
            · exact congrArg Subtype.val hx.sq_eq_one
          constructor
          · intro x hx k
            have hxI : IsInvolution (x : G) := involutionCoe x hx
            have hconjI := isInvolution_rightConjugateElem
              (g := ((k⁻¹ : K) : G)) hxI
            constructor
            · intro hone
              apply hconjI.ne_one
              simpa [rightConjugateElem,
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
                  congrArg Subtype.val hone
            · apply Subtype.ext
              simpa [rightConjugateElem,
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
                  hconjI.sq_eq_one
          · intro x hx y hy
            have hxI : IsInvolution (x : G) := involutionCoe x hx
            have hyI : IsInvolution (y : G) := involutionCoe y hy
            have hxQ : (x : G) ∈ Q := by simpa [hSQ] using x.property
            have hyQ : (y : G) ∈ Q := by simpa [hSQ] using y.property
            have hxH : (x : G) ∈ H := hch.1.section2.hA.A1.Q_le_H hxQ
            have hyH : (y : G) ∈ H := hch.1.section2.hA.A1.Q_le_H hyQ
            rcases ((PFchapter1section1.proposition_3 H D Q t
                hch.1.section2.hA.A1).2 s hch.1.s_mem_H
                  hch.1.s_involution (x : G)).1 ⟨hxH, hxI⟩ with
              ⟨ax, haxSet, hax⟩
            rcases ((PFchapter1section1.proposition_3 H D Q t
                hch.1.section2.hA.A1).2 s hch.1.s_mem_H
                  hch.1.s_involution (y : G)).1 ⟨hyH, hyI⟩ with
              ⟨ay, haySet, hay⟩
            have haxK : ax ∈ K := (hch.1.section2.K_def ax).2 haxSet
            have hayK : ay ∈ K := (hch.1.section2.K_def ay).2 haySet
            let k : K := ⟨ay⁻¹ * ax, K.mul_mem (K.inv_mem hayK) haxK⟩
            have hkxy : y = k • x := by
              apply Subtype.ext
              simp only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
              change (y : G) = (k : G) * (x : G) * (k : G)⁻¹
              rw [← hax, ← hay]
              dsimp [k, rightConjugateElem]
              group
            refine ⟨k, hkxy, ?_⟩
            intro b hb
            have hbval :
                (b : G) * (x : G) * (b : G)⁻¹ =
                  (k : G) * (x : G) * (k : G)⁻¹ := by
              exact congrArg Subtype.val (hb.symm.trans hkxy)
            have hfix :
                rightConjugateElem (x : G) ((b : G)⁻¹ * (k : G)) =
                  (x : G) := by
              dsimp [rightConjugateElem]
              calc
                ((b : G)⁻¹ * (k : G))⁻¹ * (x : G) *
                      ((b : G)⁻¹ * (k : G)) =
                    (k : G)⁻¹ * ((b : G) * (x : G) * (b : G)⁻¹) *
                      (k : G) := by group
                _ = (k : G)⁻¹ * ((k : G) * (x : G) * (k : G)⁻¹) * k := by
                  rw [hbval]
                _ = (x : G) := by group
            have hactorOne : (b : G)⁻¹ * (k : G) = 1 :=
              hKfreeOnSSharp (x : G) x.property hxI.ne_one
                ((b : G)⁻¹ * (k : G))
                (K.mul_mem (K.inv_mem b.property) k.property) hfix
            apply Subtype.ext
            exact inv_mul_eq_one.mp hactorOne
        have hcardCenter :
            Nat.card (Subgroup.center S) = Nat.card K + 1 := by
          let InvS := {x : S // IsInvolution x}
          let CenterSharp :=
            {z : Subgroup.center S // ((z : Subgroup.center S) : S) ≠ 1}
          let sS : S := ⟨s, hsS⟩
          have hsI : IsInvolution sS := by
            constructor
            · intro hsOne
              exact hch.1.s_involution.ne_one (congrArg Subtype.val hsOne)
            · apply Subtype.ext
              exact hch.1.s_involution.sq_eq_one
          let kToInv : K → InvS := fun k =>
            ⟨k • sS, hactualRegular.1 sS hsI k⟩
          have hkToInvInjective : Function.Injective kToInv := by
            intro a b hab
            obtain ⟨k, hk, huniq⟩ :=
              hactualRegular.2 sS hsI (a • sS) (hactualRegular.1 sS hsI a)
            have ha : (a • sS) = a • sS := rfl
            have hb : (a • sS) = b • sS := congrArg Subtype.val hab
            exact (huniq a ha).trans (huniq b hb).symm
          have hkToInvSurjective : Function.Surjective kToInv := by
            intro y
            obtain ⟨k, hk, _huniq⟩ :=
              hactualRegular.2 sS hsI y.1 y.property
            exact ⟨k, Subtype.ext hk.symm⟩
          have hcardInv : Nat.card InvS = Nat.card K :=
            (Nat.card_congr
              (Equiv.ofBijective kToInv
                ⟨hkToInvInjective, hkToInvSurjective⟩)).symm
          let invToCenter : InvS → CenterSharp := fun x => by
            have hx : x.1 ∈ involutions S := x.property
            rw [(higmanTheorem_involutions_center hSuzuki).1] at hx
            exact ⟨⟨x.1, hx.1⟩, hx.2⟩
          have hinvToCenterInjective : Function.Injective invToCenter := by
            intro x y hxy
            apply Subtype.ext
            exact congrArg (fun z : CenterSharp => ((z.1 : Subgroup.center S) : S)) hxy
          have hinvToCenterSurjective : Function.Surjective invToCenter := by
            intro z
            have hz : ((z.1 : Subgroup.center S) : S) ∈ involutions S := by
              rw [(higmanTheorem_involutions_center hSuzuki).1]
              exact ⟨z.1.property, z.property⟩
            refine ⟨⟨((z.1 : Subgroup.center S) : S), hz⟩, ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            rfl
          have hcardCenterSharp :
              Nat.card CenterSharp = Nat.card K := by
            calc
              Nat.card CenterSharp = Nat.card InvS :=
                (Nat.card_congr
                  (Equiv.ofBijective invToCenter
                    ⟨hinvToCenterInjective, hinvToCenterSurjective⟩)).symm
              _ = Nat.card K := hcardInv
          have hcardCenterSub :
              Nat.card CenterSharp = Nat.card (Subgroup.center S) - 1 := by
            classical
            letI : Fintype (Subgroup.center S) := Fintype.ofFinite _
            letI : Fintype CenterSharp := Fintype.ofFinite _
            simpa [CenterSharp, Nat.card_eq_fintype_card] using
              (Set.card_ne_eq (1 : Subgroup.center S))
          have hcenterPos : 0 < Nat.card (Subgroup.center S) := Nat.card_pos
          have hsubEq :
              Nat.card (Subgroup.center S) - 1 = Nat.card K :=
            hcardCenterSub.symm.trans hcardCenterSharp
          omega
        have hcardCenterSq :
            Nat.card S = Nat.card (Subgroup.center S) ^ 2 := by
          rcases hch.2.2.1 with
            ⟨n, hn, theta, pairLift, cocycle, _hperiod, _htheta,
              _haddLeft, _haddRight, hdiag, hpairMem, hpairOne,
              hpairSurj, hpairInj, hpairMul⟩
          let F := BinaryGaloisField n
          let pairToS : F × F → S := fun p =>
            ⟨pairLift p.1 p.2, hpairMem p.1 p.2⟩
          have hpairToSInjective : Function.Injective pairToS := by
            rintro ⟨a, z⟩ ⟨b, w⟩ hab
            have hval : pairLift a z = pairLift b w :=
              congrArg Subtype.val hab
            rcases hpairInj a z b w hval with ⟨rfl, rfl⟩
            rfl
          have hpairToSSurjective : Function.Surjective pairToS := by
            intro x
            rcases hpairSurj (x : G) x.property with ⟨a, z, hx⟩
            refine ⟨(a, z), ?_⟩
            apply Subtype.ext
            exact hx.symm
          have hcardS : Nat.card S = Nat.card F ^ 2 := by
            calc
              Nat.card S = Nat.card (F × F) :=
                (Nat.card_congr
                  (Equiv.ofBijective pairToS
                    ⟨hpairToSInjective, hpairToSSurjective⟩)).symm
              _ = Nat.card F ^ 2 := by rw [Nat.card_prod, pow_two]
          have hpairZeroSq : ∀ z : F, pairLift 0 z ^ 2 = 1 := by
            intro z
            calc
              pairLift 0 z ^ 2 = pairLift 0 z * pairLift 0 z := by
                rw [pow_two]
              _ = pairLift (0 + 0) (z + z + cocycle 0 0) :=
                hpairMul 0 z 0 z
              _ = pairLift 0 0 := by
                rw [hdiag]
                simp only [zero_add, zero_mul, CharTwo.add_self_eq_zero]
              _ = 1 := hpairOne
          let fieldToCenter : F → Subgroup.center S := fun z => by
            let zS : S := ⟨pairLift 0 z, hpairMem 0 z⟩
            refine ⟨zS, ?_⟩
            by_cases hz : z = 0
            · subst z
              have hzSOne : zS = 1 := by
                apply Subtype.ext
                exact hpairOne
              rw [hzSOne]
              exact (Subgroup.center S).one_mem
            · have hzNe : zS ≠ 1 := by
                intro hone
                have hval : pairLift 0 z = pairLift 0 0 := by
                  simpa [zS, hpairOne] using congrArg Subtype.val hone
                exact hz (hpairInj 0 z 0 0 hval).2
              have hzInv : zS ∈ involutions S := by
                exact ⟨hzNe, Subtype.ext (hpairZeroSq z)⟩
              rw [(higmanTheorem_involutions_center hSuzuki).1] at hzInv
              exact hzInv.1
          have hfieldToCenterInjective : Function.Injective fieldToCenter := by
            intro z w hzw
            have hval : pairLift 0 z = pairLift 0 w :=
              congrArg Subtype.val (congrArg Subtype.val hzw)
            exact (hpairInj 0 z 0 w hval).2
          have hfieldToCenterSurjective :
              Function.Surjective fieldToCenter := by
            intro z
            rcases hpairSurj ((z : Subgroup.center S) : G) z.1.property with
              ⟨a, w, haw⟩
            have hsqSub := (higmanTheorem_involutions_center hSuzuki).2 z
            have hsqG : ((z : Subgroup.center S) : G) ^ 2 = 1 := by
              simpa using
                congrArg Subtype.val (congrArg Subtype.val hsqSub)
            have hsq : pairLift a w ^ 2 = 1 := by
              exact (congrArg (fun x : G => x ^ 2) haw).symm.trans
                hsqG
            have hcoordZero : a * theta a = 0 := by
              have hpairEq : pairLift 0 (a * theta a) = pairLift 0 0 := by
                calc
                  pairLift 0 (a * theta a) =
                      pairLift (a + a) (w + w + cocycle a a) := by
                    rw [hdiag]
                    simp only [CharTwo.add_self_eq_zero, zero_add]
                  _ = pairLift a w * pairLift a w :=
                    (hpairMul a w a w).symm
                  _ = 1 := by simpa [pow_two] using hsq
                  _ = pairLift 0 0 := hpairOne.symm
              exact (hpairInj 0 (a * theta a) 0 0 hpairEq).2
            have ha : a = 0 := by
              by_contra ha
              exact (mul_ne_zero ha ((map_ne_zero theta).2 ha)) hcoordZero
            refine ⟨w, ?_⟩
            apply Subtype.ext
            apply Subtype.ext
            simpa [fieldToCenter, ha] using haw.symm
          have hcardCenter : Nat.card (Subgroup.center S) = Nat.card F :=
            (Nat.card_congr
              (Equiv.ofBijective fieldToCenter
                ⟨hfieldToCenterInjective, hfieldToCenterSurjective⟩)).symm
          rw [hcardS, hcardCenter]
        rcases higmanTheorem_order_center_sq_typeA hSuzuki hKcyclic
            hactualFaithful hactualRegular hcardCenterSq with
          ⟨m, hm, thetaF, pairLiftF, cocycleF, eK, eQ, eZ,
            _hperiodF, _hthetaF, _haddLeftF, _haddRightF, _hdiagF,
            _hpairMemF, _hpairOneF, _hpairSurjF, _hpairInjF, _hpairMulF,
            _hcenterCardF, hquotientAction, _hcenterAction⟩
        have hcoordinateSeparation : ∀ k₁ k₂ : KSharp,
            SameOrbit (rrOf k₁) (rrOf k₂) → k₁ = k₂ := by
          let F := BinaryGaloisField m
          let alpha : S → F := fun x =>
            (eQ (QuotientGroup.mk' (Subgroup.center S) x)).toAdd
          let rS : S := ⟨r, hrS⟩
          have halphaRNe : alpha rS ≠ 0 := by
            intro hzero
            have heQOne :
                eQ (QuotientGroup.mk' (Subgroup.center S) rS) = 1 := by
              have := congrArg Multiplicative.ofAdd hzero
              simpa [alpha] using this
            have hmkOne : QuotientGroup.mk' (Subgroup.center S) rS = 1 :=
              eQ.injective (by simpa using heQOne)
            have hrCenter : rS ∈ Subgroup.center S :=
              (QuotientGroup.eq_one_iff rS).mp (by simpa using hmkOne)
            have hrSqSub := (higmanTheorem_involutions_center hSuzuki).2
              (⟨rS, hrCenter⟩ : Subgroup.center S)
            have hrSq : r ^ 2 = 1 :=
              congrArg Subtype.val (congrArg Subtype.val hrSqSub)
            have hdvd : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one hrSq
            rw [hrOrder] at hdvd
            norm_num at hdvd
          let beta : S → F := fun x => alpha x / alpha rS
          let kappa : K → F := fun a => ((eK a : Fˣ) : F)⁻¹
          have hkappaNe : ∀ a : K, kappa a ≠ 0 := by
            intro a
            simp [kappa]
          have hbetaR : beta rS = 1 := by
            simp [beta, halphaRNe]
          have hbetaMul : ∀ x y : S, beta (x * y) = beta x + beta y := by
            intro x y
            simp [beta, alpha, map_mul, div_eq_mul_inv]
            ring
          have hbetaInv : ∀ x : S, beta x⁻¹ = beta x := by
            intro x
            simp [beta, alpha, map_inv, CharTwo.neg_eq]
          have hbetaRightConj : ∀ x : S, ∀ a : K,
              ∀ hxa : rightConjugateElem (x : G) (a : G) ∈ S,
                beta ⟨rightConjugateElem (x : G) (a : G), hxa⟩ =
                  kappa a * beta x := by
            intro x a hxa
            let xa : S :=
              ⟨rightConjugateElem (x : G) (a : G), hxa⟩
            have hxaEq : xa = (a⁻¹ : K) • x := by
              apply Subtype.ext
              simp [xa, rightConjugateElem,
                Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
            have halphaAction :
                alpha ((a⁻¹ : K) • x) =
                  ((eK (a⁻¹ : K) : Fˣ) : F) * alpha x := by
              simpa [alpha] using hquotientAction (a⁻¹ : K) x
            calc
              beta xa = alpha xa / alpha rS := rfl
              _ = alpha ((a⁻¹ : K) • x) / alpha rS := by rw [hxaEq]
              _ = (((eK (a⁻¹ : K) : Fˣ) : F) * alpha x) /
                    alpha rS := by rw [halphaAction]
              _ = kappa a * beta x := by
                simp [kappa, beta, map_inv, div_eq_mul_inv]
                ring
          have hbetaRR : ∀ k : KSharp,
              beta ⟨rrOf k, by
                simpa [rrOf, representative] using
                  hrepresentativeMem (Sum.inr k : RepParam)⟩ =
                1 + kappa k.1 := by
            intro k
            let rInvS : S := ⟨r⁻¹, hrInvS⟩
            have hconjS :
                rightConjugateElem (rInvS : G) (k.1 : G) ∈ S :=
              hrightConjS r⁻¹ hrInvS (k.1 : G) k.1.property
            let rConjS : S :=
              ⟨rightConjugateElem (rInvS : G) (k.1 : G), hconjS⟩
            have hrInvBeta : beta rInvS = 1 := by
              have hinv := hbetaInv rS
              have h_eq : rInvS = (rS : S)⁻¹ := by
                ext; simp [rInvS, rS]
              simpa [h_eq, hbetaR] using hinv
            have hconjBeta : beta rConjS = kappa k.1 := by
              calc
                beta rConjS = kappa k.1 * beta rInvS := by
                  exact hbetaRightConj rInvS k.1 hconjS
                _ = kappa k.1 := by rw [hrInvBeta]; simp
            have hprod :
                (⟨rrOf k, by
                    simpa [rrOf, representative] using
                      hrepresentativeMem (Sum.inr k : RepParam)⟩ : S) =
                  rS * rConjS := by
              apply Subtype.ext
              rfl
            rw [hprod, hbetaMul, hbetaR, hconjBeta]
          have hkappaMul : ∀ a b : K,
              kappa (a * b) = kappa a * kappa b := by
            intro a b
            simp [kappa, map_mul, mul_inv_rev]
            ring
          have hkappaInv : ∀ a : K, kappa a⁻¹ = (kappa a)⁻¹ := by
            intro a
            simp [kappa, map_inv]
          have hbetaExplicitG : ∀ ell : K, ∀ g : S,
              (g : G) = r * rightConjugateElem r⁻¹ ((ell : G)⁻¹) →
              beta g = 1 + (kappa ell)⁻¹ := by
            intro ell g hg
            let rInvS : S := ⟨r⁻¹, hrInvS⟩
            have hconjS :
                rightConjugateElem (rInvS : G) ((ell⁻¹ : K) : G) ∈ S :=
              hrightConjS r⁻¹ hrInvS ((ell⁻¹ : K) : G) (ell⁻¹ : K).property
            let rConjS : S :=
              ⟨rightConjugateElem (rInvS : G) ((ell⁻¹ : K) : G), hconjS⟩
            have hgSub : g = rS * rConjS := by
              apply Subtype.ext
              simpa [rS, rInvS, rConjS] using hg
            have hrInvBeta : beta rInvS = 1 := by
              have hinv := hbetaInv rS
              have h_eq : rInvS = (rS : S)⁻¹ := by
                ext; simp [rInvS, rS]
              simpa [h_eq, hbetaR] using hinv
            have hconjBeta : beta rConjS = (kappa ell)⁻¹ := by
              calc
                beta rConjS = kappa ell⁻¹ * beta rInvS :=
                  hbetaRightConj rInvS ell⁻¹ hconjS
                _ = kappa ell⁻¹ := by rw [hrInvBeta]; simp
                _ = (kappa ell)⁻¹ := hkappaInv ell
            rw [hgSub, hbetaMul, hbetaR, hconjBeta]
          have hbetaExplicitF : ∀ ell k : K, ∀ f : S,
              (f : G) =
                rightConjugateElem r
                    ((ell : G)⁻¹ * ((k : G) ^ 2)⁻¹) *
                  rightConjugateElem r⁻¹ (k : G)⁻¹ →
              beta f =
                (kappa ell)⁻¹ * (kappa k)⁻¹ ^ 2 + (kappa k)⁻¹ := by
            intro ell k f hf
            let a₁ : K := ell⁻¹ * (k ^ 2)⁻¹
            let a₂ : K := k⁻¹
            have hfirstMem :
                rightConjugateElem r (a₁ : G) ∈ S :=
              hrightConjS r hrS (a₁ : G) a₁.property
            have hsecondMem :
                rightConjugateElem r⁻¹ (a₂ : G) ∈ S :=
              hrightConjS r⁻¹ hrInvS (a₂ : G) a₂.property
            let firstS : S :=
              ⟨rightConjugateElem r (a₁ : G), hfirstMem⟩
            let secondS : S :=
              ⟨rightConjugateElem r⁻¹ (a₂ : G), hsecondMem⟩
            have hfSub : f = firstS * secondS := by
              apply Subtype.ext
              simpa [firstS, secondS, a₁, a₂] using hf
            have hrInvBeta : beta (⟨r⁻¹, hrInvS⟩ : S) = 1 := by
              have hinv := hbetaInv rS
              have h_eq : (⟨r⁻¹, hrInvS⟩ : S) = (rS : S)⁻¹ := by
                apply Subtype.ext; simp [rS, Subgroup.coe_inv]
              simpa [h_eq, hbetaR] using hinv
            have hkappaA₁ :
                kappa a₁ = (kappa ell)⁻¹ * (kappa k)⁻¹ ^ 2 := by
              calc
                kappa a₁ = kappa ell⁻¹ * kappa (k ^ 2)⁻¹ := by
                  simpa [a₁] using hkappaMul ell⁻¹ (k ^ 2)⁻¹
                _ = (kappa ell)⁻¹ * (kappa (k ^ 2))⁻¹ := by
                  rw [hkappaInv, hkappaInv]
                _ = (kappa ell)⁻¹ * (kappa k)⁻¹ ^ 2 := by
                  rw [show k ^ 2 = k * k by simp [pow_two], hkappaMul]
                  simp [mul_inv_rev, pow_two]
            have hfirst :
                beta firstS =
                  (kappa ell)⁻¹ * (kappa k)⁻¹ ^ 2 := by
              calc
                beta firstS = kappa a₁ * beta rS :=
                  hbetaRightConj rS a₁ hfirstMem
                _ = kappa a₁ := by rw [hbetaR]; simp
                _ = (kappa ell)⁻¹ * (kappa k)⁻¹ ^ 2 := hkappaA₁
            have hsecond : beta secondS = (kappa k)⁻¹ := by
              calc
                beta secondS =
                    kappa a₂ * beta (⟨r⁻¹, hrInvS⟩ : S) :=
                  hbetaRightConj (⟨r⁻¹, hrInvS⟩ : S) a₂ hsecondMem
                _ = kappa a₂ := by rw [hrInvBeta]; simp
                _ = (kappa k)⁻¹ := by exact hkappaInv k
            rw [hfSub, hbetaMul, hfirst, hsecond]
          have hfieldAlgebra : ∀ a k₁ k₂ ell₁ ell₂ : F,
              a ≠ 0 → k₁ ≠ 0 → k₂ ≠ 0 → ell₁ ≠ 0 → ell₂ ≠ 0 →
              1 + k₂ = a * (1 + k₁) →
              ell₂ * k₂ = a * ell₁ * k₁ →
              ell₂⁻¹ * k₂⁻¹ ^ 2 + k₂⁻¹ =
                a⁻¹ * (ell₁⁻¹ * k₁⁻¹ ^ 2 + k₁⁻¹) →
              ell₁⁻¹ * (k₁⁻¹ + 1) ≠ 1 →
              k₁ = k₂ := by
            intro a k₁ k₂ ell₁ ell₂ ha hk₁ hk₂ hell₁ hell₂
              heq1 heq2 heq3 hexceptional
            have hinvMul : ∀ x y : F, (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
              intro x y
              rw [mul_inv_rev]
              ring
            have hinvCancel : ∀ x : F, x ≠ 0 → x⁻¹ * x = 1 := by
              intro x hx
              exact inv_mul_cancel₀ (G₀ := F) hx
            have hmulInvCancel : ∀ x : F, x ≠ 0 → x * x⁻¹ = 1 := by
              intro x hx
              exact mul_inv_cancel₀ (G₀ := F) hx
            have hinvOneAdd : ∀ k : F, k ≠ 0 →
                k⁻¹ * (1 + k) = k⁻¹ + 1 := by
              intro k hk
              rw [mul_add, mul_one, hinvCancel k hk]
            have hscaledAdd : ∀ k ell : F, k ≠ 0 →
                ell⁻¹ * (k⁻¹ + 1) = (ell * k)⁻¹ * (1 + k) := by
              intro k ell hk
              rw [hinvMul, ← hinvOneAdd k hk]
              ring
            have hcancelScaledAdd : ∀ a k ell : F, a ≠ 0 → k ≠ 0 →
                (a * ell * k)⁻¹ * (a * (1 + k)) =
                  ell⁻¹ * (k⁻¹ + 1) := by
              intro b k ell hb hk
              rw [hinvMul, hinvMul]
              calc
                (b⁻¹ * ell⁻¹ * k⁻¹) * (b * (1 + k)) =
                    (b⁻¹ * b) * ell⁻¹ * (k⁻¹ * (1 + k)) := by
                  ring
                _ = ell⁻¹ * (k⁻¹ * (1 + k)) := by
                  rw [hinvCancel b hb]
                  simp
                _ = ell⁻¹ * (k⁻¹ + 1) := by rw [hinvOneAdd k hk]
            have hbaseProduct : ∀ k ell : F, k ≠ 0 → ell ≠ 0 →
                (ell * k) * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹) =
                  k⁻¹ + ell := by
              intro k ell hk hell
              have hkInvSq : k * k⁻¹ ^ 2 = k⁻¹ := by
                rw [pow_two, ← mul_assoc, hmulInvCancel k hk, one_mul]
              calc
                (ell * k) * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹) =
                    (ell * ell⁻¹) * (k * k⁻¹ ^ 2) +
                      ell * (k * k⁻¹) := by
                  ring
                _ = k⁻¹ + ell := by
                  rw [hmulInvCancel ell hell, hkInvSq, hmulInvCancel k hk]
                  simp
            have hcancelScaledProduct :
                ∀ a k ell : F, a ≠ 0 → k ≠ 0 → ell ≠ 0 →
                  (a * ell * k) *
                      (a⁻¹ * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹)) =
                    k⁻¹ + ell := by
              intro b k ell hb hk hell
              calc
                (b * ell * k) *
                    (b⁻¹ * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹)) =
                    (b * b⁻¹) *
                      ((ell * k) * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹)) := by
                  ring
                _ = (ell * k) * (ell⁻¹ * k⁻¹ ^ 2 + k⁻¹) := by
                  rw [hmulInvCancel b hb]
                  simp
                _ = k⁻¹ + ell := hbaseProduct k ell hk hell
            let x₁ := ell₁⁻¹ * (k₁⁻¹ + 1)
            let x₂ := ell₂⁻¹ * (k₂⁻¹ + 1)
            let y₁ := k₁⁻¹ + ell₁
            let y₂ := k₂⁻¹ + ell₂
            have hx : x₂ = x₁ := by
              calc
                x₂ = (ell₂ * k₂)⁻¹ * (1 + k₂) := by
                  exact hscaledAdd k₂ ell₂ hk₂
                _ = (a * ell₁ * k₁)⁻¹ * (a * (1 + k₁)) := by
                  rw [heq2, heq1]
                _ = x₁ := by
                  exact hcancelScaledAdd a k₁ ell₁ ha hk₁
            have hy : y₂ = y₁ := by
              calc
                y₂ = (ell₂ * k₂) *
                    (ell₂⁻¹ * k₂⁻¹ ^ 2 + k₂⁻¹) := by
                  exact (hbaseProduct k₂ ell₂ hk₂ hell₂).symm
                _ = (a * ell₁ * k₁) *
                    (a⁻¹ * (ell₁⁻¹ * k₁⁻¹ ^ 2 + k₁⁻¹)) := by
                  rw [heq2, heq3]
                _ = y₁ := by
                  exact hcancelScaledProduct a k₁ ell₁ ha hk₁ hell₁
            have hidentity : ∀ k ell : F, k ≠ 0 → ell ≠ 0 →
                (ell⁻¹ * (k⁻¹ + 1) + 1) * k⁻¹ =
                  (ell⁻¹ * (k⁻¹ + 1)) * (k⁻¹ + ell) + 1 := by
              intro k ell _hk hell
              let common := ell⁻¹ * k⁻¹ ^ 2 + ell⁻¹ * k⁻¹ + k⁻¹
              have hleft :
                  (ell⁻¹ * (k⁻¹ + 1) + 1) * k⁻¹ = common := by
                dsimp [common]
                ring
              have hright :
                  (ell⁻¹ * (k⁻¹ + 1)) * (k⁻¹ + ell) + 1 =
                    common := by
                calc
                  (ell⁻¹ * (k⁻¹ + 1)) * (k⁻¹ + ell) + 1 =
                      ell⁻¹ * k⁻¹ ^ 2 +
                        (ell⁻¹ * ell) * k⁻¹ + ell⁻¹ * k⁻¹ +
                          (ell⁻¹ * ell) + 1 := by
                    ring
                  _ = common := by
                    rw [hinvCancel ell hell]
                    have htwo : (1 : F) + 1 = 0 :=
                      CharTwo.add_self_eq_zero 1
                    dsimp [common]
                    linear_combination htwo
              exact hleft.trans hright.symm
            have hproduct :
                (x₁ + 1) * k₁⁻¹ = (x₁ + 1) * k₂⁻¹ := by
              calc
                (x₁ + 1) * k₁⁻¹ = x₁ * y₁ + 1 := by
                  exact hidentity k₁ ell₁ hk₁ hell₁
                _ = x₂ * y₂ + 1 := by rw [hx, hy]
                _ = (x₂ + 1) * k₂⁻¹ :=
                  (hidentity k₂ ell₂ hk₂ hell₂).symm
                _ = (x₁ + 1) * k₂⁻¹ := by rw [hx]
            have hxPlusNe : x₁ + 1 ≠ 0 := by
              intro hxZero
              apply hexceptional
              change x₁ = 1
              have hxNeg : x₁ = -1 := eq_neg_of_add_eq_zero_left hxZero
              simpa only [CharTwo.neg_eq] using hxNeg
            have hinvEq : k₁⁻¹ = k₂⁻¹ :=
              mul_left_cancel₀ hxPlusNe hproduct
            exact inv_injective hinvEq
          have hnoExceptional : ∀ k : KSharp, ∀ ell : K,
              rightConjugateElem s (ell : G) =
                s * ((k : G) * s * (k : G)⁻¹) →
              (kappa ell)⁻¹ * ((kappa k.1)⁻¹ + 1) ≠ 1 := by
            intro k ell hell hbad
            have hxS : rrOf k ∈ S := by
              simpa [rrOf, representative] using
                hrepresentativeMem (Sum.inr k : RepParam)
            have hxNe : rrOf k ≠ 1 := by
              simpa [rrOf, representative] using
                hrepresentativeNe (Sum.inr k : RepParam)
            rcases hcanonical (rrOf k) hxS hxNe with
              ⟨g, hgS, d, hdD, f, hfS, hdecomp⟩
            rcases hrrCanonicalData (k : G) k.1.property k.2
                g hgS d hdD f hfS (by simpa [rrOf] using hdecomp) with
              ⟨ell0, hell0K, hell0Def, _hell0Ne, _hkell0Ne,
                g0, hg0, d0, hd0, f0, hf0, hgEq, hdEq, hfEq⟩
            let ell0K : K := ⟨ell0, hell0K⟩
            have hellTargets :
                rightConjugateElem s ell0 =
                  rightConjugateElem s (ell : G) :=
              hell0Def.trans hell.symm
            have hfixEll :
                rightConjugateElem s (ell0 * (ell : G)⁻¹) = s := by
              calc
                rightConjugateElem s (ell0 * (ell : G)⁻¹) =
                    rightConjugateElem (rightConjugateElem s ell0)
                      (ell : G)⁻¹ :=
                  (rightConjugateElem_comp s ell0 (ell : G)⁻¹).symm
                _ = rightConjugateElem
                    (rightConjugateElem s (ell : G)) (ell : G)⁻¹ := by
                  rw [hellTargets]
                _ = rightConjugateElem s ((ell : G) * (ell : G)⁻¹) :=
                  rightConjugateElem_comp s (ell : G) (ell : G)⁻¹
                _ = s := by simp [rightConjugateElem]
            have hell0EqG : ell0 = (ell : G) := by
              have hactorOne := hKfreeOnSSharp s hsS
                hch.1.s_involution.ne_one
                (ell0 * (ell : G)⁻¹)
                (K.mul_mem hell0K (K.inv_mem ell.property)) hfixEll
              exact mul_inv_eq_one.mp hactorOne
            have hell0Eq : ell0K = ell := by
              apply Subtype.ext
              exact hell0EqG
            have hgForm :
                g = r * rightConjugateElem r⁻¹ ((ell : G)⁻¹) := by
              rw [hgEq, hg0, hell0EqG]
            have hdForm : d = (ell : G) ^ 2 * (k : G) ^ 2 := by
              rw [hdEq, hd0, hell0EqG]
            have hfForm :
                f = rightConjugateElem r
                    ((ell : G)⁻¹ * ((k : G) ^ 2)⁻¹) *
                  rightConjugateElem r⁻¹ (k : G)⁻¹ := by
              rw [hfEq, hf0, hell0EqG]
            have hdK : d ∈ K := by
              rw [hdForm]
              exact K.mul_mem (K.pow_mem ell.property 2)
                (K.pow_mem k.1.property 2)
            let gS : S := ⟨g, hgS⟩
            let fS : S := ⟨f, hfS⟩
            let zS : S := fS * gS
            have hbetaG : beta gS = 1 + (kappa ell)⁻¹ :=
              hbetaExplicitG ell gS (by simpa [gS] using hgForm)
            have hbetaF :
                beta fS =
                  (kappa ell)⁻¹ * (kappa k.1)⁻¹ ^ 2 +
                    (kappa k.1)⁻¹ :=
              hbetaExplicitF ell k.1 fS (by simpa [fS] using hfForm)
            have hbetaZ : beta zS = 0 := by
              change beta (fS * gS) = 0
              rw [hbetaMul, hbetaF, hbetaG]
              calc
                (kappa ell)⁻¹ * (kappa k.1)⁻¹ ^ 2 +
                      (kappa k.1)⁻¹ +
                    (1 + (kappa ell)⁻¹) =
                    ((kappa k.1)⁻¹ + 1) *
                      (1 + (kappa ell)⁻¹ *
                        ((kappa k.1)⁻¹ + 1)) := by
                  have htwo : (1 : F) + 1 = 0 :=
                    CharTwo.add_self_eq_zero 1
                  linear_combination
                    -((kappa ell)⁻¹ * (kappa k.1)⁻¹) * htwo
                _ = 0 := by
                  rw [hbad, CharTwo.add_self_eq_zero]
                  simp
            have halphaZ : alpha zS = 0 := by
              change alpha zS / alpha rS = 0 at hbetaZ
              have hdiv : alpha zS = 0 ∨ alpha rS = 0 :=
                (div_eq_zero_iff (G₀ := F) : alpha zS / alpha rS = 0 ↔
                  alpha zS = 0 ∨ alpha rS = 0).mp hbetaZ
              rcases hdiv with hzero | hzero
              · exact hzero
              · exact False.elim (halphaRNe hzero)
            have heQOne :
                eQ (QuotientGroup.mk' (Subgroup.center S) zS) = 1 := by
              have := congrArg Multiplicative.ofAdd halphaZ
              simpa [alpha] using this
            have hmkOne :
                QuotientGroup.mk' (Subgroup.center S) zS = 1 :=
              eQ.injective (by simpa using heQOne)
            have hzCenter : zS ∈ Subgroup.center S :=
              (QuotientGroup.eq_one_iff zS).mp (by simpa using hmkOne)
            have htdt : t * d * t = d⁻¹ := by
              have hright := (hch.1.section2.K_def d).1 hdK
              simpa [rightConjugateElem, htInv] using hright.2
            have hdt : d * t = t * d⁻¹ := by
              symm
              calc
                t * d⁻¹ = t * (t * d * t) := by rw [htdt]
                _ = (t * t) * d * t := by group
                _ = d * t := by rw [ht]; simp
            have hyOrder : orderOf (t * rrOf k * t) = 4 := by
              calc
                orderOf (t * rrOf k * t) =
                    orderOf (rightConjugateElem (rrOf k) t) := by
                  simp [rightConjugateElem, htInv]
                _ = orderOf (rrOf k) := horderRightConj (rrOf k) t
                _ = 4 := hrrOrder k
            have hzNe : zS ≠ 1 := by
              intro hzOne
              have hzOneG : f * g = 1 := by
                simpa [zS, fS, gS] using congrArg Subtype.val hzOne
              have hySq : (t * rrOf k * t) ^ 2 = 1 := by
                rw [pow_two, hdecomp]
                calc
                  (g * d * t * f) * (g * d * t * f) =
                      g * d * t * (f * g) * d * t * f := by group
                  _ = g * d * t * d * t * f := by rw [hzOneG]; simp
                  _ = g * (d * t) * d * t * f := by group
                  _ = g * (t * d⁻¹) * d * t * f := by rw [hdt]
                  _ = g * (t * t) * f := by group
                  _ = g * f := by rw [ht]; simp
                  _ = 1 := by
                    have hfg : g * f = 1 := by
                      calc
                        g * f = g * (f * g) * g⁻¹ := by group
                        _ = 1 := by rw [hzOneG]; simp
                    exact hfg
              have hdvd : orderOf (t * rrOf k * t) ∣ 2 :=
                orderOf_dvd_of_pow_eq_one hySq
              rw [hyOrder] at hdvd
              norm_num at hdvd
            have hzInvS : IsInvolution zS := by
              have hzMem : zS ∈ involutions S := by
                rw [(higmanTheorem_involutions_center hSuzuki).1]
                exact ⟨hzCenter, hzNe⟩
              exact hzMem
            have hzInvG : IsInvolution (zS : G) := by
              exact ⟨fun h => hzNe (Subtype.ext h),
                congrArg Subtype.val hzInvS.sq_eq_one⟩
            have hzH : (zS : G) ∈ H := by
              apply hch.1.section2.hA.A1.Q_le_H
              simpa [hSQ] using zS.property
            have hzConjS : rightConjugateElem (zS : G) d ∈ S :=
              hrightConjS (zS : G) zS.property d hdK
            let zConj : G := rightConjugateElem (zS : G) d
            have hzConjNe : zConj ≠ 1 :=
              hrightConjNe (zS : G) hzInvG.ne_one d
            have hzConjInv : IsInvolution zConj := by
              simpa [zConj] using
                (isInvolution_rightConjugateElem (g := d) hzInvG)
            let A : G := t * zConj * t
            have hAInv : IsInvolution A := by
              have hconj :=
                isInvolution_rightConjugateElem (g := t) hzConjInv
              simpa [A, zConj, rightConjugateElem, htInv] using hconj
            have hAnotH : A ∉ H := by
              exact htxtNotH zConj (by simpa [zConj] using hzConjS)
                hzConjNe
            have hySqNe : (t * rrOf k * t) ^ 2 ≠ 1 := by
              intro hySq
              have hdvd : orderOf (t * rrOf k * t) ∣ 2 :=
                orderOf_dvd_of_pow_eq_one hySq
              rw [hyOrder] at hdvd
              norm_num at hdvd
            have hyFour : (t * rrOf k * t) ^ 4 = 1 := by
              have hpow := pow_orderOf_eq_one (t * rrOf k * t)
              simpa [hyOrder] using hpow
            have hySqInv : IsInvolution ((t * rrOf k * t) ^ 2) := by
              refine ⟨hySqNe, ?_⟩
              calc
                ((t * rrOf k * t) ^ 2) ^ 2 =
                    (t * rrOf k * t) ^ 4 := by group
                _ = 1 := hyFour
            have hySquareForm :
                (t * rrOf k * t) ^ 2 = g * A * f := by
              rw [pow_two, hdecomp]
              calc
                (g * d * t * f) * (g * d * t * f) =
                    g * d * t * (f * g) * d * t * f := by group
                _ = g * (d * t) * (f * g) * d * t * f := by group
                _ = g * (t * d⁻¹) * (f * g) * d * t * f := by
                  rw [hdt]
                _ = g * t * (d⁻¹ * (f * g) * d) * t * f := by group
                _ = g * A * f := by
                  simp [A, zConj, zS, fS, gS, rightConjugateElem]
                  group
            have hconjSquare :
                rightConjugateElem ((t * rrOf k * t) ^ 2) g =
                  A * (zS : G) := by
              rw [hySquareForm]
              simp [rightConjugateElem, zS, fS, gS]
              group
            have hAzInv : IsInvolution (A * (zS : G)) := by
              have hconj :=
                isInvolution_rightConjugateElem (g := g) hySqInv
              rw [hconjSquare] at hconj
              exact hconj
            have hAzComm : A * (zS : G) = (zS : G) * A := by
              calc
                A * (zS : G) = (A * (zS : G))⁻¹ :=
                  hAzInv.inv_eq_self.symm
                _ = (zS : G)⁻¹ * A⁻¹ := by rw [mul_inv_rev]
                _ = (zS : G) * A := by
                  rw [hzInvG.inv_eq_self, hAInv.inv_eq_self]
            have hzAInv : IsInvolution ((zS : G) * A) := by
              rw [← hAzComm]
              exact hAzInv
            have hodd := PFchapter1section1.proposition_2_a
              H D Q t hch.1.section2.hA.A1 (zS : G) A hzH hzInvG hAInv hAnotH
            have hzAOrder : orderOf ((zS : G) * A) = 2 :=
              orderOf_eq_prime hzAInv.sq_eq_one hzAInv.ne_one
            rw [hzAOrder] at hodd
            exact (by norm_num : ¬ Odd 2) hodd
          intro k₁ k₂ horb
          rcases horb with ⟨a, haK, ha⟩
          let aK : K := ⟨a, haK⟩
          have hcollisionEquations :
              ∃ ell₁ ell₂ : K,
                rightConjugateElem s (ell₁ : G) =
                    s * ((k₁ : G) * s * (k₁ : G)⁻¹) ∧
                rightConjugateElem s (ell₂ : G) =
                    s * ((k₂ : G) * s * (k₂ : G)⁻¹) ∧
                1 + kappa k₂.1 = kappa aK * (1 + kappa k₁.1) ∧
                kappa ell₂ * kappa k₂.1 =
                  kappa aK * kappa ell₁ * kappa k₁.1 ∧
                (kappa ell₂)⁻¹ * (kappa k₂.1)⁻¹ ^ 2 +
                    (kappa k₂.1)⁻¹ =
                (kappa aK)⁻¹ *
                    ((kappa ell₁)⁻¹ * (kappa k₁.1)⁻¹ ^ 2 +
                      (kappa k₁.1)⁻¹) := by
            have hx₁S : rrOf k₁ ∈ S := by
              simpa [rrOf, representative] using
                hrepresentativeMem (Sum.inr k₁ : RepParam)
            have hx₂S : rrOf k₂ ∈ S := by
              simpa [rrOf, representative] using
                hrepresentativeMem (Sum.inr k₂ : RepParam)
            have hx₁Ne : rrOf k₁ ≠ 1 := by
              simpa [rrOf, representative] using
                hrepresentativeNe (Sum.inr k₁ : RepParam)
            have hx₂Ne : rrOf k₂ ≠ 1 := by
              simpa [rrOf, representative] using
                hrepresentativeNe (Sum.inr k₂ : RepParam)
            rcases hcanonical (rrOf k₁) hx₁S hx₁Ne with
              ⟨g₁, hg₁S, d₁, hd₁D, f₁, hf₁S, hdec₁⟩
            rcases hcanonical (rrOf k₂) hx₂S hx₂Ne with
              ⟨g₂, hg₂S, d₂, hd₂D, f₂, hf₂S, hdec₂⟩
            rcases hrrCanonicalData (k₁ : G) k₁.1.property k₁.2
                g₁ hg₁S d₁ hd₁D f₁ hf₁S (by simpa [rrOf] using hdec₁) with
              ⟨ell₁G, hell₁K, hell₁Def, _hell₁Ne, _hkell₁Ne,
                g01, _hg01, d01, hd01, f01, hf01, _hg₁Eq, hd₁Eq, hf₁Eq⟩
            rcases hrrCanonicalData (k₂ : G) k₂.1.property k₂.2
                g₂ hg₂S d₂ hd₂D f₂ hf₂S (by simpa [rrOf] using hdec₂) with
              ⟨ell₂G, hell₂K, hell₂Def, _hell₂Ne, _hkell₂Ne,
                g02, _hg02, d02, hd02, f02, hf02, _hg₂Eq, hd₂Eq, hf₂Eq⟩
            let ell₁ : K := ⟨ell₁G, hell₁K⟩
            let ell₂ : K := ⟨ell₂G, hell₂K⟩
            let x₁S : S := ⟨rrOf k₁, hx₁S⟩
            let x₂S : S := ⟨rrOf k₂, hx₂S⟩
            have hxaS : rightConjugateElem (x₁S : G) (aK : G) ∈ S :=
              hrightConjS (rrOf k₁) hx₁S a haK
            let xaS : S :=
              ⟨rightConjugateElem (x₁S : G) (aK : G), hxaS⟩
            have hxaEq : xaS = x₂S := by
              apply Subtype.ext
              exact ha
            have heq1' :
                1 + kappa k₂.1 = kappa aK * (1 + kappa k₁.1) := by
              calc
                1 + kappa k₂.1 = beta x₂S := (hbetaRR k₂).symm
                _ = beta xaS := by rw [hxaEq]
                _ = kappa aK * beta x₁S :=
                  hbetaRightConj x₁S aK hxaS
                _ = kappa aK * (1 + kappa k₁.1) := by rw [hbetaRR k₁]
            have htrans :
                t * rrOf k₂ * t =
                  (a * g₁ * a⁻¹) * (a * d₁ * a) * t *
                    (a * f₁ * a⁻¹) := by
              rw [← ha]
              simpa [rightConjugateElem] using
                hcanonicalTransport (rrOf k₁) g₁ d₁ f₁ a hdec₁ haK
            have hgcS : a * g₁ * a⁻¹ ∈ S := hKnormS a haK g₁ hg₁S
            have hdcD : a * d₁ * a ∈ D :=
              D.mul_mem (D.mul_mem (hch.1.section2.K_le_D haK) hd₁D)
                (hch.1.section2.K_le_D haK)
            have hfcS : a * f₁ * a⁻¹ ∈ S := hKnormS a haK f₁ hf₁S
            have huniq := hcanonicalUnique (rrOf k₂) hx₂S hx₂Ne
              (a * g₁ * a⁻¹) hgcS (a * d₁ * a) hdcD
              (a * f₁ * a⁻¹) hfcS htrans
              g₂ hg₂S d₂ hd₂D f₂ hf₂S hdec₂
            have hd₁K : d₁ ∈ K := by
              rw [hd₁Eq, hd01]
              exact K.mul_mem (K.pow_mem hell₁K 2) (K.pow_mem k₁.1.property 2)
            have hd₂K : d₂ ∈ K := by
              rw [hd₂Eq, hd02]
              exact K.mul_mem (K.pow_mem hell₂K 2) (K.pow_mem k₂.1.property 2)
            let d₁K : K := ⟨d₁, hd₁K⟩
            let d₂K : K := ⟨d₂, hd₂K⟩
            have hd₁Form : d₁K = ell₁ ^ 2 * k₁.1 ^ 2 := by
              apply Subtype.ext
              exact hd₁Eq.trans hd01
            have hd₂Form : d₂K = ell₂ ^ 2 * k₂.1 ^ 2 := by
              apply Subtype.ext
              exact hd₂Eq.trans hd02
            have hdRel : d₂K = aK * d₁K * aK := by
              ext; simpa [d₁K, d₂K, aK] using huniq.2.1.symm
            have h_sq_mul (x y : G) (hx : x ∈ K) (hy : y ∈ K) : (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
              have hcomm_xy : x * y = y * x := hKcomm x hx y hy
              calc
                (x * y) ^ 2 = (x * y) * (x * y) := by simp [pow_two]
                _ = x * (y * x) * y := by simp [mul_assoc]
                _ = x * (x * y) * y := by rw [hcomm_xy]
                _ = (x * x) * (y * y) := by simp [mul_assoc]
                _ = x ^ 2 * y ^ 2 := by simp [pow_two]
            have hsquareK :
                (ell₂ * k₂.1) ^ 2 = (aK * ell₁ * k₁.1) ^ 2 := by
              apply Subtype.ext
              calc
                ((ell₂ * k₂.1) ^ 2 : G) = ((ell₂ : G) * (k₂.1 : G)) ^ 2 := by simp
                _ = (ell₂ : G) ^ 2 * (k₂.1 : G) ^ 2 :=
                  h_sq_mul (ell₂ : G) (k₂.1 : G) ell₂.property k₂.1.property
                _ = (ell₂ ^ 2 * k₂.1 ^ 2 : G) := by simp
                _ = (d₂K : G) := by
                  simpa [Subgroup.coe_mul, Subgroup.coe_pow] using
                    congrArg Subtype.val hd₂Form.symm
                _ = (aK * d₁K * aK : G) := by
                  simpa [Subgroup.coe_mul, Subgroup.coe_pow] using
                    congrArg Subtype.val hdRel
                _ = (aK * (ell₁ ^ 2 * k₁.1 ^ 2) * aK : G) := by
                  have hd₁FormG : (d₁K : G) = ((ell₁ ^ 2 * k₁.1 ^ 2 : K) : G) :=
                    congrArg Subtype.val hd₁Form
                  simp [Subgroup.coe_mul, hd₁FormG]
                _ = (aK : G) * ((ell₁ : G) ^ 2 * (k₁.1 : G) ^ 2) * (aK : G) := by simp
                _ = (aK : G) ^ 2 * (ell₁ : G) ^ 2 * (k₁.1 : G) ^ 2 := by
                  have hcomm_aK_sq : (aK : G) * ((k₁.1 : G) ^ 2) = ((k₁.1 : G) ^ 2) * (aK : G) :=
                    hKcomm (aK : G) aK.property ((k₁.1 : G) ^ 2) (K.pow_mem k₁.1.property 2)
                  have hcomm_sq_aK : (ell₁ : G) ^ 2 * (aK : G) = (aK : G) * (ell₁ : G) ^ 2 :=
                    hKcomm ((ell₁ : G) ^ 2) (K.pow_mem ell₁.property 2) (aK : G) aK.property
                  calc
                    (aK : G) * ((ell₁ : G) ^ 2 * (k₁.1 : G) ^ 2) * (aK : G) =
                        (aK : G) * ((ell₁ : G) ^ 2) * ((k₁.1 : G) ^ 2) * (aK : G) := by
                      simp [mul_assoc]
                    _ = (aK : G) * ((ell₁ : G) ^ 2) * ((aK : G) * (k₁.1 : G) ^ 2) := by
                      simp [mul_assoc, hcomm_aK_sq]
                    _ = (aK : G) * ((ell₁ : G) ^ 2 * (aK : G)) * (k₁.1 : G) ^ 2 := by
                      simp [mul_assoc]
                    _ = (aK : G) * ((aK : G) * (ell₁ : G) ^ 2) * (k₁.1 : G) ^ 2 := by
                      simp [hcomm_sq_aK, mul_assoc]
                    _ = (aK : G) ^ 2 * (ell₁ : G) ^ 2 * (k₁.1 : G) ^ 2 := by
                      simp [pow_two, mul_assoc]
                _ = ((aK * ell₁ * k₁.1) ^ 2 : G) := by
                  calc
                    (aK : G) ^ 2 * (ell₁ : G) ^ 2 * (k₁.1 : G) ^ 2 =
                        ((aK : G) ^ 2 * (ell₁ : G) ^ 2) * (k₁.1 : G) ^ 2 := by simp [mul_assoc]
                    _ = ((aK : G) * (ell₁ : G)) ^ 2 * (k₁.1 : G) ^ 2 := by
                      rw [h_sq_mul (aK : G) (ell₁ : G) aK.property ell₁.property]
                    _ = (((aK : G) * (ell₁ : G)) * (k₁.1 : G)) ^ 2 := by
                      rw [h_sq_mul ((aK : G) * (ell₁ : G)) (k₁.1 : G)
                        (K.mul_mem aK.property ell₁.property) k₁.1.property]
                    _ = ((aK * ell₁ * k₁.1) ^ 2 : G) := by simp [Subgroup.coe_mul]
            have hKodd : Odd (Nat.card K) :=
              odd_of_card_dvd hch.1.section2.hA.A1.D_odd
                (Subgroup.card_dvd_of_le hch.1.section2.K_le_D)
            have hfactorK : ell₂ * k₂.1 = aK * ell₁ * k₁.1 :=
              by
                have hsquareSurjective :
                    Function.Surjective (fun x : K => x ^ 2) := by
                  intro x
                  have hxordDvd : orderOf x ∣ Nat.card K :=
                    orderOf_dvd_natCard x
                  have hxordOdd : Odd (orderOf x) :=
                    hKodd.of_dvd_nat hxordDvd
                  have hxordCoprime : Nat.Coprime 2 (orderOf x) := by
                    simpa using hxordOdd.coprime_two_left
                  obtain ⟨m, hm⟩ :=
                    exists_pow_eq_self_of_coprime (x := x) (n := 2)
                      hxordCoprime
                  refine ⟨x ^ m, ?_⟩
                  calc
                    (x ^ m) ^ 2 = x ^ (m * 2) := by rw [pow_mul]
                    _ = x ^ (2 * m) := by rw [Nat.mul_comm]
                    _ = (x ^ 2) ^ m := by rw [pow_mul]
                    _ = x := hm
                have hsquareInjective :
                    Function.Injective (fun x : K => x ^ 2) := by
                  classical
                  exact Finite.injective_iff_surjective.2 hsquareSurjective
                exact hsquareInjective hsquareK
            have heq2' :
                kappa ell₂ * kappa k₂.1 =
                  kappa aK * kappa ell₁ * kappa k₁.1 := by
              have := congrArg kappa hfactorK
              simpa only [hkappaMul] using this
            let f₁S : S := ⟨f₁, hf₁S⟩
            let f₂S : S := ⟨f₂, hf₂S⟩
            have hf₁Form : (f₁S : G) =
                rightConjugateElem r
                    ((ell₁ : G)⁻¹ * ((k₁.1 : G) ^ 2)⁻¹) *
                  rightConjugateElem r⁻¹ (k₁.1 : G)⁻¹ := by
              exact hf₁Eq.trans hf01
            have hf₂Form : (f₂S : G) =
                rightConjugateElem r
                    ((ell₂ : G)⁻¹ * ((k₂.1 : G) ^ 2)⁻¹) *
                  rightConjugateElem r⁻¹ (k₂.1 : G)⁻¹ := by
              exact hf₂Eq.trans hf02
            have hfBetaRel : beta f₂S = (kappa aK)⁻¹ * beta f₁S := by
              have hfcMem :
                  rightConjugateElem (f₁S : G) ((aK⁻¹ : K) : G) ∈ S :=
                hrightConjS f₁ hf₁S ((aK⁻¹ : K) : G) (aK⁻¹ : K).property
              let fcS : S :=
                ⟨rightConjugateElem (f₁S : G) ((aK⁻¹ : K) : G), hfcMem⟩
              have hfcEq : fcS = f₂S := by
                apply Subtype.ext
                simpa [fcS, rightConjugateElem] using huniq.2.2
              calc
                beta f₂S = beta fcS := by rw [hfcEq]
                _ = kappa aK⁻¹ * beta f₁S :=
                  hbetaRightConj f₁S aK⁻¹ hfcMem
                _ = (kappa aK)⁻¹ * beta f₁S := by rw [hkappaInv]
            have heq3' :
                (kappa ell₂)⁻¹ * (kappa k₂.1)⁻¹ ^ 2 +
                    (kappa k₂.1)⁻¹ =
                  (kappa aK)⁻¹ *
                    ((kappa ell₁)⁻¹ * (kappa k₁.1)⁻¹ ^ 2 +
                      (kappa k₁.1)⁻¹) := by
              calc
                (kappa ell₂)⁻¹ * (kappa k₂.1)⁻¹ ^ 2 +
                      (kappa k₂.1)⁻¹ = beta f₂S :=
                  (hbetaExplicitF ell₂ k₂.1 f₂S hf₂Form).symm
                _ = (kappa aK)⁻¹ * beta f₁S := hfBetaRel
                _ = (kappa aK)⁻¹ *
                      ((kappa ell₁)⁻¹ * (kappa k₁.1)⁻¹ ^ 2 +
                        (kappa k₁.1)⁻¹) := by
                  rw [hbetaExplicitF ell₁ k₁.1 f₁S hf₁Form]
            exact ⟨ell₁, ell₂,
              by simpa [ell₁] using hell₁Def,
              by simpa [ell₂] using hell₂Def,
              heq1', heq2', heq3'⟩
          rcases hcollisionEquations with
            ⟨ell₁, ell₂, hell₁, hell₂, heq1, heq2, heq3⟩
          have hkappaEq : kappa k₁.1 = kappa k₂.1 :=
            hfieldAlgebra (kappa aK) (kappa k₁.1) (kappa k₂.1)
              (kappa ell₁) (kappa ell₂)
              (hkappaNe aK) (hkappaNe k₁.1) (hkappaNe k₂.1)
              (hkappaNe ell₁) (hkappaNe ell₂)
              heq1 heq2 heq3 (hnoExceptional k₁ ell₁ hell₁)
          apply Subtype.ext
          apply Subtype.ext
          have hinvEq :
              ((eK k₁.1 : Fˣ) : F)⁻¹ = ((eK k₂.1 : Fˣ) : F)⁻¹ :=
            hkappaEq
          have hvalEq : ((eK k₁.1 : Fˣ) : F) = ((eK k₂.1 : Fˣ) : F) :=
            inv_injective hinvEq
          exact congrArg Subtype.val (eK.injective (Units.ext hvalEq))
        exact hcoordinateSeparation
      intro i j a haK ha
      rcases i with i | k
      · rcases j with j | l
        · apply congrArg Sum.inl
          fin_cases i <;> fin_cases j
          · rfl
          · exact False.elim (hbaseOrbitSeparate.1 ⟨a, haK, by simpa [representative] using ha⟩)
          · exact False.elim (hbaseOrbitSeparate.2.1 ⟨a, haK, by simpa [representative] using ha⟩)
          · exact False.elim (hbaseOrbitSeparate.1
              (hsameOrbitSymm r s ⟨a, haK, by simpa [representative] using ha⟩))
          · rfl
          · exact False.elim (hbaseOrbitSeparate.2.2 ⟨a, haK, by simpa [representative] using ha⟩)
          · exact False.elim (hbaseOrbitSeparate.2.1
              (hsameOrbitSymm r⁻¹ s ⟨a, haK, by simpa [representative] using ha⟩))
          · exact False.elim (hbaseOrbitSeparate.2.2
              (hsameOrbitSymm r⁻¹ r ⟨a, haK, by simpa [representative] using ha⟩))
          · rfl
        · have horb : SameOrbit (rrOf l) (representative (Sum.inl i)) :=
            hsameOrbitSymm (representative (Sum.inl i)) (rrOf l)
              ⟨a, haK, by simpa [representative, rrOf] using ha⟩
          fin_cases i
          · exact False.elim (hrrNotS l (by simpa [representative] using horb))
          · exact False.elim ((hrrNotRorInv l).1 (by simpa [representative] using horb))
          · exact False.elim ((hrrNotRorInv l).2 (by simpa [representative] using horb))
      · rcases j with j | l
        · have horb : SameOrbit (rrOf k) (representative (Sum.inl j)) :=
            ⟨a, haK, by simpa [representative, rrOf] using ha⟩
          fin_cases j
          · exact False.elim (hrrNotS k (by simpa [representative] using horb))
          · exact False.elim ((hrrNotRorInv k).1 (by simpa [representative] using horb))
          · exact False.elim ((hrrNotRorInv k).2 (by simpa [representative] using horb))
        · apply congrArg Sum.inr
          exact hrrOrbitInjective k l
            ⟨a, haK, by simpa [representative, rrOf] using ha⟩
    have hcardRepParam : Nat.card RepParam = Nat.card K + 2 := by
      classical
      letI : Fintype K := Fintype.ofFinite K
      letI : Fintype {k : K // (k : G) ≠ 1} := Fintype.ofFinite _
      have hKSharp : Nat.card {k : K // (k : G) ≠ 1} = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using (Set.card_ne_eq (1 : K))
      dsimp [RepParam]
      rw [Nat.card_sum, Nat.card_fin, hKSharp]
      have hKpos : 0 < Nat.card K := Nat.card_pos
      omega
    have hcardSSharp :
        Nat.card SSharp = (Nat.card K + 2) * Nat.card K := by
      rcases hch.2.2.1 with
        ⟨n, hn, theta, pairLift, cocycle, _hperiod, _htheta,
          _haddLeft, _haddRight, hdiag, hpairMem, hpairOne,
          hpairSurj, hpairInj, hpairMul⟩
      let F := BinaryGaloisField n
      let InvS := {x : S // IsInvolution x}
      let FSharp := {z : F // z ≠ 0}
      let q := 2 ^ n
      have hcardS : Nat.card S = q ^ 2 := by
        let pairToS : F × F → S := fun p =>
          ⟨pairLift p.1 p.2, hpairMem p.1 p.2⟩
        have hpairToSInjective : Function.Injective pairToS := by
          rintro ⟨a, z⟩ ⟨b, w⟩ hab
          have hval : pairLift a z = pairLift b w := congrArg Subtype.val hab
          rcases hpairInj a z b w hval with ⟨rfl, rfl⟩
          rfl
        have hpairToSSurjective : Function.Surjective pairToS := by
          intro x
          rcases hpairSurj (x : G) x.property with ⟨a, z, hx⟩
          refine ⟨(a, z), ?_⟩
          apply Subtype.ext
          exact hx.symm
        have hcardF : Nat.card F = q := by
          dsimp [F, q]
          exact GaloisField.card 2 n hn
        calc
          Nat.card S = Nat.card (F × F) :=
            (Nat.card_congr
              (Equiv.ofBijective pairToS
                ⟨hpairToSInjective, hpairToSSurjective⟩)).symm
          _ = Nat.card F * Nat.card F := Nat.card_prod F F
          _ = q ^ 2 := by rw [hcardF]; simp [pow_two]
      have hcardInvS : Nat.card InvS = q - 1 := by
        have hpairZeroSq : ∀ z : F, pairLift 0 z ^ 2 = 1 := by
          intro z
          calc
            pairLift 0 z ^ 2 = pairLift 0 z * pairLift 0 z := by simp [pow_two]
            _ = pairLift (0 + 0) (z + z + cocycle 0 0) :=
              hpairMul 0 z 0 z
            _ = pairLift 0 0 := by
              rw [hdiag]
              simp only [zero_add, zero_mul, CharTwo.add_self_eq_zero]
            _ = 1 := hpairOne
        have hpairZeroNe : ∀ z : F, z ≠ 0 → pairLift 0 z ≠ 1 := by
          intro z hz hzero
          have heq : pairLift 0 z = pairLift 0 0 := hzero.trans hpairOne.symm
          exact hz (hpairInj 0 z 0 0 heq).2
        let zeroToInv : FSharp → InvS := fun z =>
          ⟨⟨pairLift 0 z, hpairMem 0 z⟩,
            ⟨by
                intro hone
                exact hpairZeroNe z z.property (congrArg Subtype.val hone),
              by
                apply Subtype.ext
                exact hpairZeroSq z⟩⟩
        have hzeroToInvInjective : Function.Injective zeroToInv := by
          intro z w hzw
          apply Subtype.ext
          have hval : pairLift 0 z = pairLift 0 w := by
            exact congrArg (fun x : InvS => ((x.1 : S) : G)) hzw
          exact (hpairInj 0 z 0 w hval).2
        have hzeroToInvSurjective : Function.Surjective zeroToInv := by
          intro x
          rcases hpairSurj (x.1 : G) x.1.property with ⟨a, z, hx⟩
          have hpairDiag : pairLift 0 (a * theta a) = pairLift 0 0 := by
            calc
              pairLift 0 (a * theta a) =
                  pairLift (a + a) (z + z + cocycle a a) := by
                rw [hdiag]
                simp only [CharTwo.add_self_eq_zero, zero_add]
              _ = pairLift a z * pairLift a z := (hpairMul a z a z).symm
              _ = (x.1 : G) ^ 2 := by rw [hx]; simp [pow_two]
              _ = 1 := congrArg Subtype.val x.property.sq_eq_one
              _ = pairLift 0 0 := hpairOne.symm
          have hmulZero : a * theta a = 0 :=
            (hpairInj 0 (a * theta a) 0 0 hpairDiag).2
          have haZero : a = 0 := by
            rcases mul_eq_zero.mp hmulZero with ha | hthetaZero
            · exact ha
            · exact theta.injective (by simpa using hthetaZero)
          have hzNe : z ≠ 0 := by
            intro hzZero
            apply x.property.ne_one
            apply Subtype.ext
            calc
              (x.1 : G) = pairLift a z := hx
              _ = pairLift 0 0 := by rw [haZero, hzZero]
              _ = 1 := hpairOne
          refine ⟨⟨z, hzNe⟩, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          simpa [zeroToInv, haZero] using hx.symm
        have hcardF : Nat.card F = q := by
          dsimp [F, q]
          exact GaloisField.card 2 n hn
        have hcardFSharp : Nat.card FSharp = q - 1 := by
          classical
          letI : Fintype F := Fintype.ofFinite F
          letI : Fintype FSharp := Fintype.ofFinite FSharp
          calc
            Nat.card FSharp = Nat.card F - 1 := by
              simpa [FSharp, Nat.card_eq_fintype_card] using
                (Set.card_ne_eq (0 : F))
            _ = q - 1 := by rw [hcardF]
        calc
          Nat.card InvS = Nat.card FSharp :=
            (Nat.card_congr
              (Equiv.ofBijective zeroToInv
                ⟨hzeroToInvInjective, hzeroToInvSurjective⟩)).symm
          _ = q - 1 := hcardFSharp
      have hcardK : Nat.card K = q - 1 := by
        let kToInv : K → InvS := fun k =>
          ⟨⟨rightConjugateElem s (k : G),
              hrightConjS s hsS (k : G) k.property⟩,
            ⟨by
                intro hone
                exact hrightConjNe s hch.1.s_involution.ne_one (k : G)
                  (congrArg Subtype.val hone),
              by
                apply Subtype.ext
                exact (isInvolution_rightConjugateElem
                  (g := (k : G)) hch.1.s_involution).sq_eq_one⟩⟩
        have hkToInvInjective : Function.Injective kToInv := by
          intro a b hab
          have hvalue :
              rightConjugateElem s (a : G) = rightConjugateElem s (b : G) :=
            congrArg (fun x : InvS => ((x.1 : S) : G)) hab
          have hfix :
              rightConjugateElem s ((a : G) * (b : G)⁻¹) = s := by
            calc
              rightConjugateElem s ((a : G) * (b : G)⁻¹) =
                  rightConjugateElem (rightConjugateElem s (a : G))
                    (b : G)⁻¹ :=
                (rightConjugateElem_comp s (a : G) (b : G)⁻¹).symm
              _ = rightConjugateElem (rightConjugateElem s (b : G))
                    (b : G)⁻¹ := by rw [hvalue]
              _ = s := by
                rw [rightConjugateElem_comp]
                simp [rightConjugateElem]
          have habOne : (a : G) * (b : G)⁻¹ = 1 :=
            hKfreeOnSSharp s hsS hch.1.s_involution.ne_one
              ((a : G) * (b : G)⁻¹)
              (K.mul_mem a.property (K.inv_mem b.property)) hfix
          apply Subtype.ext
          exact mul_inv_eq_one.mp habOne
        have hkToInvSurjective : Function.Surjective kToInv := by
          intro y
          have hyI : IsInvolution (y.1 : G) := by
            constructor
            · intro hyOne
              exact y.property.ne_one (Subtype.ext hyOne)
            · exact congrArg Subtype.val y.property.sq_eq_one
          have hyQ : (y.1 : G) ∈ Q := by simpa [hSQ] using y.1.property
          have hyH : (y.1 : G) ∈ H := hch.1.section2.hA.A1.Q_le_H hyQ
          rcases ((PFchapter1section1.proposition_3 H D Q t
              hch.1.section2.hA.A1).2 s hch.1.s_mem_H hch.1.s_involution
                (y.1 : G)).1 ⟨hyH, hyI⟩ with ⟨a, haSet, haeq⟩
          have haK : a ∈ K := (hch.1.section2.K_def a).2 haSet
          refine ⟨⟨a, haK⟩, ?_⟩
          apply Subtype.ext
          apply Subtype.ext
          exact haeq
        calc
          Nat.card K = Nat.card InvS :=
            Nat.card_congr
              (Equiv.ofBijective kToInv ⟨hkToInvInjective, hkToInvSurjective⟩)
          _ = q - 1 := hcardInvS
      have hcardSSharpSub : Nat.card SSharp = Nat.card S - 1 := by
        let SSharpSub := {x : S // x ≠ 1}
        let sharpEquiv : SSharp ≃ SSharpSub :=
          { toFun := fun x =>
              ⟨⟨x, x.property.1⟩, fun hx =>
                x.property.2 (congrArg Subtype.val hx)⟩
            invFun := fun x =>
              ⟨(x.1 : G), x.1.property, fun hx =>
                x.property (Subtype.ext hx)⟩
            left_inv := by intro x; rfl
            right_inv := by intro x; rfl }
        have hcardSub : Nat.card SSharpSub = Nat.card S - 1 := by
          classical
          letI : Fintype S := Fintype.ofFinite S
          letI : Fintype SSharpSub := Fintype.ofFinite SSharpSub
          simpa [SSharpSub, Nat.card_eq_fintype_card] using
            (Set.card_ne_eq (1 : S))
        calc
          Nat.card SSharp = Nat.card SSharpSub := Nat.card_congr sharpEquiv
          _ = Nat.card S - 1 := hcardSub
      rw [hcardSSharpSub, hcardS, hcardK]
      have hqPos : 0 < q := by simp [q]
      have hq : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
      have hfactor : q ^ 2 = (q - 1 + 2) * (q - 1) + 1 := by
        calc
          q ^ 2 = (q - 1 + 1) ^ 2 := by rw [hq]
          _ = (q - 1 + 2) * (q - 1) + 1 := by ring
      omega
    let orbitParam : RepParam × K → SSharp := fun p =>
      ⟨rightConjugateElem (representative p.1) (p.2 : G),
        hrightConjS (representative p.1) (hrepresentativeMem p.1)
          (p.2 : G) p.2.property,
        hrightConjNe (representative p.1) (hrepresentativeNe p.1) (p.2 : G)⟩
    have horbitParamInjective : Function.Injective orbitParam := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have hvalue :
          rightConjugateElem (representative i) (a : G) =
            rightConjugateElem (representative j) (b : G) :=
        congrArg Subtype.val hab
      have hsep :
          rightConjugateElem (representative i) ((a : G) * (b : G)⁻¹) =
            representative j := by
        calc
          rightConjugateElem (representative i) ((a : G) * (b : G)⁻¹) =
              rightConjugateElem
                (rightConjugateElem (representative i) (a : G)) (b : G)⁻¹ :=
            (rightConjugateElem_comp (representative i)
              (a : G) (b : G)⁻¹).symm
          _ = rightConjugateElem
                (rightConjugateElem (representative j) (b : G)) (b : G)⁻¹ := by
            rw [hvalue]
          _ = representative j := by
            rw [rightConjugateElem_comp]
            simp [rightConjugateElem]
      have hij : i = j :=
        hrepresentativeOrbitSeparate i j ((a : G) * (b : G)⁻¹)
          (K.mul_mem a.property (K.inv_mem b.property)) hsep
      subst j
      have habOne : (a : G) * (b : G)⁻¹ = 1 :=
        hKfreeOnSSharp (representative i) (hrepresentativeMem i)
          (hrepresentativeNe i) ((a : G) * (b : G)⁻¹)
          (K.mul_mem a.property (K.inv_mem b.property)) hsep
      have habEq : a = b := by
        apply Subtype.ext
        exact mul_inv_eq_one.mp habOne
      simp [habEq]
    have hcardOrbitParam : Nat.card (RepParam × K) = Nat.card SSharp := by
      calc
        Nat.card (RepParam × K) = Nat.card RepParam * Nat.card K := by
          exact Nat.card_prod RepParam K
        _ = (Nat.card K + 2) * Nat.card K := by rw [hcardRepParam]
        _ = Nat.card SSharp := hcardSSharp.symm
    have horbitParamSurjective : Function.Surjective orbitParam :=
      (Nat.bijective_iff_injective_and_card orbitParam).2
        ⟨horbitParamInjective, hcardOrbitParam⟩ |>.2
    intro x hxS hxNe
    rcases horbitParamSurjective (⟨x, hxS, hxNe⟩ : SSharp) with
      ⟨⟨i, a⟩, hia⟩
    refine ⟨(a : G)⁻¹, K.inv_mem a.property, ?_⟩
    have hvalue : rightConjugateElem (representative i) (a : G) = x :=
      congrArg Subtype.val hia
    have hrecover : (a : G) * x * (a : G)⁻¹ = representative i := by
      rw [← hvalue]
      simp [rightConjugateElem, mul_assoc]
    simpa [hrecover] using hrepresentativeShape i
  have hrepresentativeCoefficient : ∀ y : G, IsRepresentative y →
      ∀ g : G, g ∈ S → ∀ d : G, d ∈ D → ∀ f : G, f ∈ S →
        t * y * t = g * d * t * f → d ∈ K := by
    intro y hy g hgS d hdD f hfS hdecomp
    rcases hy with hyS | hyR | hyRinv | ⟨k, hkK, hkNe, hyrr⟩
    · subst y
      have hdOne := hDcoefficientCovariant s hsS hch.1.s_involution.ne_one
        r⁻¹ hrInvS 1 D.one_mem r hrS (by simpa using hstruct)
        1 K.one_mem g hgS d hdD f hfS (by simpa using hdecomp)
      have hdOne' : d = 1 := by simpa using hdOne
      simpa [hdOne']
    · subst y
      have hdOne := hDcoefficientCovariant r hrS hrNe
        r hrS 1 D.one_mem s hsS (by simpa using htrt)
        1 K.one_mem g hgS d hdD f hfS (by simpa using hdecomp)
      have hdOne' : d = 1 := by simpa using hdOne
      simpa [hdOne']
    · subst y
      have hdOne := hDcoefficientCovariant r⁻¹ hrInvS hrInvNe
        s hsS 1 D.one_mem r⁻¹ hrInvS (by simpa using htrInvt)
        1 K.one_mem g hgS d hdD f hfS (by simpa using hdecomp)
      have hdOne' : d = 1 := by simpa using hdOne
      simpa [hdOne']
    · subst y
      exact hrrCoefficient k hkK hkNe g hgS d hdD f hfS hdecomp
  have hDcoefficient : ∀ x : G, x ∈ S → x ≠ 1 →
      ∀ g : G, g ∈ S → ∀ d : G, d ∈ D → ∀ f : G, f ∈ S →
        t * x * t = g * d * t * f → d ∈ K := by
    intro x hxS hxne g hgS d hdD f hfS hdecomp
    rcases horbitRepresentatives x hxS hxne with ⟨a, haK, hrep⟩
    let y : G := a⁻¹ * x * a
    have hyS : y ∈ S := by
      simpa [y] using hKnormS a⁻¹ (K.inv_mem haK) x hxS
    have hyne : y ≠ 1 := by
      intro hyOne
      apply hxne
      calc
        x = a * y * a⁻¹ := by dsimp [y]; group
        _ = 1 := by rw [hyOne]; simp
    rcases hcanonical y hyS hyne with ⟨gy, hgyS, dy, hdyD, fy, hfyS, hydecomp⟩
    have hdyK := hrepresentativeCoefficient y hrep
      gy hgyS dy hdyD fy hfyS hydecomp
    have hdy : dy = a * d * a :=
      hDcoefficientCovariant x hxS hxne g hgS d hdD f hfS hdecomp
        a haK gy hgyS dy hdyD fy hfyS hydecomp
    have : a⁻¹ * dy * a⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.inv_mem haK) hdyK) (K.inv_mem haK)
    convert this using 1
    rw [hdy]
    group
  have htSt : ∀ x : G, x ∈ S → x ≠ 1 → t * x * t ∈ SKtS := by
    intro x hxS hxne
    rcases hcanonical x hxS hxne with ⟨g, hgS, d, hdD, f, hfS, htxt⟩
    exact ⟨g, hgS, d,
      hDcoefficient x hxS hxne g hgS d hdD f hfS htxt, f, hfS, htxt⟩
  have htRight (x : G) : t * x = (t * x * t) * t := by
    calc
      t * x = t * x * 1 := by simp
      _ = t * x * (t * t) := by rw [ht]
      _ = (t * x * t) * t := by group
  have hKinvConjS : ∀ k : G, k ∈ K → ∀ x : G, x ∈ S →
      k⁻¹ * x * k ∈ S := by
    intro k hk x hx
    simpa using hKnormS k⁻¹ (K.inv_mem hk) x hx
  have hOne : (1 : G) ∈ SK ∪ SKtS := by
    left
    exact ⟨1, S.one_mem, 1, K.one_mem, by simp⟩
  have hInv : ∀ x : G, x ∈ SK ∪ SKtS → x⁻¹ ∈ SK ∪ SKtS := by
    intro x hx
    rcases hx with ⟨a, ha, b, hb, rfl⟩ |
      ⟨a, ha, b, hb, c, hc, rfl⟩
    · left
      refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, K.inv_mem hb, ?_⟩
      · exact hKinvConjS b hb a⁻¹ (S.inv_mem ha)
      · group
    · right
      refine ⟨c⁻¹, S.inv_mem hc, t * b⁻¹ * t,
        htK b⁻¹ (K.inv_mem hb), a⁻¹, S.inv_mem ha, ?_⟩
      rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, htInv]
      calc
        c⁻¹ * (t * (b⁻¹ * a⁻¹)) = c⁻¹ * (t * b⁻¹) * a⁻¹ := by group
        _ = c⁻¹ * ((t * b⁻¹ * t) * t) * a⁻¹ := by rw [← htRight b⁻¹]
        _ = c⁻¹ * (t * b⁻¹ * t) * t * a⁻¹ := by group
  have hSKSK : ∀ x y : G, x ∈ SK → y ∈ SK → x * y ∈ SK ∪ SKtS := by
    intro x y hx hy
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, rfl⟩
    left
    refine ⟨a * (b * c * b⁻¹),
      S.mul_mem ha (hKnormS b hb c hc), b * d, K.mul_mem hb hd, ?_⟩
    group
  have hSKSKtS : ∀ x y : G, x ∈ SK → y ∈ SKtS →
      x * y ∈ SK ∪ SKtS := by
    intro x y hx hy
    rcases hx with ⟨a, ha, b, hb, rfl⟩
    rcases hy with ⟨c, hc, d, hd, e, he, rfl⟩
    right
    refine ⟨a * (b * c * b⁻¹),
      S.mul_mem ha (hKnormS b hb c hc), b * d,
      K.mul_mem hb hd, e, he, ?_⟩
    group
  have hSKtSSK : ∀ x y : G, x ∈ SKtS → y ∈ SK →
      x * y ∈ SK ∪ SKtS := by
    intro x y hx hy
    rcases hx with ⟨a, ha, b, hb, c, hc, rfl⟩
    rcases hy with ⟨d, hd, e, he, rfl⟩
    let u : G := c * d
    have hu : u ∈ S := S.mul_mem hc hd
    let u' : G := e⁻¹ * u * e
    have hu' : u' ∈ S := hKinvConjS e he u hu
    right
    refine ⟨a, ha, b * (t * e * t),
      K.mul_mem hb (htK e he), u', hu', ?_⟩
    calc
      a * b * t * c * (d * e) = a * b * t * ((c * d) * e) := by group
      _ = a * b * t * (e * u') := by dsimp [u, u']; group
      _ = a * b * (t * e) * u' := by group
      _ = a * b * ((t * e * t) * t) * u' := by rw [← htRight e]
      _ = a * (b * (t * e * t)) * t * u' := by group
  have hSKtSSKtS : ∀ x y : G, x ∈ SKtS → y ∈ SKtS →
      x * y ∈ SK ∪ SKtS := by
    intro x y hx hy
    rcases hx with ⟨a, ha, b, hb, c, hc, rfl⟩
    rcases hy with ⟨d, hd, e, he, f, hf, rfl⟩
    let u : G := c * d
    have hu : u ∈ S := S.mul_mem hc hd
    let u' : G := e⁻¹ * u * e
    have hu' : u' ∈ S := hKinvConjS e he u hu
    let k0 : G := b * (t * e * t)
    have hk0 : k0 ∈ K := K.mul_mem hb (htK e he)
    have horiginal :
        a * b * t * c * (d * e * t * f) =
          a * k0 * (t * u' * t) * f := by
      calc
        a * b * t * c * (d * e * t * f) =
            a * b * t * ((c * d) * e) * t * f := by group
        _ = a * b * t * (e * u') * t * f := by
          dsimp [u, u']
          group
        _ = a * b * (t * e) * u' * t * f := by group
        _ = a * b * ((t * e * t) * t) * u' * t * f := by
          rw [← htRight e]
        _ = a * k0 * (t * u' * t) * f := by
          dsimp [k0]
          group
    by_cases huOne : u' = 1
    · left
      refine ⟨a * (k0 * f * k0⁻¹),
        S.mul_mem ha (hKnormS k0 hk0 f hf), k0, hk0, ?_⟩
      rw [horiginal, huOne]
      simp only [mul_one, ht]
      group
    · rcases htSt u' hu' huOne with ⟨p, hp, q, hq, r, hr, hmiddle⟩
      right
      refine ⟨a * (k0 * p * k0⁻¹),
        S.mul_mem ha (hKnormS k0 hk0 p hp),
        k0 * q, K.mul_mem hk0 hq, r * f, S.mul_mem hr hf, ?_⟩
      rw [horiginal, hmiddle]
      group
  refine ⟨
    { carrier := SK ∪ SKtS
      one_mem' := hOne
      mul_mem' := fun {a b} ha hb => by
        rcases ha with haSK | haSKtS
        · rcases hb with hbSK | hbSKtS
          · exact hSKSK a b haSK hbSK
          · exact hSKSKtS a b haSK hbSKtS
        · rcases hb with hbSK | hbSKtS
          · exact hSKtSSK a b haSKtS hbSK
          · exact hSKtSSKtS a b haSKtS hbSKtS
      inv_mem' := fun {a} ha => hInv a ha }, ?_⟩
  rfl

end PFchapter3section2
end CFSG.BenderSuzuki
