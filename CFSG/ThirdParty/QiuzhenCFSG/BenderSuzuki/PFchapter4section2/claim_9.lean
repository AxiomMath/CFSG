module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_8
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_5_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (9) -/

private theorem claim_9_Q0_sq_eq_one
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ q : G, q ∈ Q0 → q ^ 2 = 1 := by
  intro q hq
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have _ := hKW
  have _ := hzeta
  have _ := hzeta_ne
  have _ := hzeta_gen
  have _ := omega
  have _ := n
  have hsec2 := hsection3.1
  rcases (hsec2.Q0_def q).mp hq with hq_one | hq_inv
  · simp [hq_one]
  · exact hq_inv.2.sq_eq_one

private theorem claim_9_W_commutes_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ w k : G, w ∈ W → k ∈ K → k * w = w * k := by
  intro w k hw hk
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have _ := hKW
  have _ := hzeta
  have _ := hzeta_ne
  have _ := hzeta_gen
  have _ := omega
  have _ := n
  have hsec2 := hsection3.1
  have hwcentral : w ∈ Subgroup.centralizer (K : Set G) := by
    rw [hsec2.W_eq] at hw
    exact hw.2
  exact (Subgroup.mem_centralizer_iff.mp hwcentral) k hk

private theorem claim_9_choice_from_claim_5_7_8_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (m n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W)
    (hWorder : m = Nat.card W) (hn : n * m = Nat.card Q0 + 1)
    (horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ x z k : G, x ∈ Q0 ∧ z ∈ Q0 ∧ k ∈ K ∧
        f (omega i * x) = rightConjugateElem (omega i * z) (k * zeta) := by
  intro i hi hin
  classical
  have hsec2 := hsection3.1
  have homega : omega i ∈ Q ∧ omega i ∉ Q0 :=
    horbit_representatives.1 i hi hin
  have homega1 : omega i ≠ 1 := fun h => homega.2 (h ▸ Q0.one_mem)
  have hV_le_D : V ≤ D := by
    rw [hsec2.V_eq]
    exact inf_le_left
  have hW_le_D : W ≤ D := hsec2.W_le_V.trans hV_le_D
  have hW_centralizes_K : W ≤ Subgroup.centralizer (K : Set G) := by
    intro w hwW
    rw [hsec2.W_eq] at hwW
    exact hwW.2
  have hW_normalizes_K : W ≤ Subgroup.normalizer (K : Set G) :=
    hW_centralizes_K.trans (centralizer_le_normalizer K)
  have hKW_decomp : ∀ d : G, d ∈ KW →
      ∃ k w : G, k ∈ K ∧ w ∈ W ∧ d = k * w := by
    intro d hdKW
    have hdSup : d ∈ K ⊔ W := by simpa [hKW] using hdKW
    change d ∈ ((K ⊔ W : Subgroup G) : Set G) at hdSup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K W hW_normalizes_K] at hdSup
    rcases Set.mem_mul.mp hdSup with ⟨k, hkK, w, hwW, hkw⟩
    exact ⟨k, w, hkK, hwW, hkw.symm⟩
  have hQ0_conj_D : ∀ q a : G, q ∈ Q0 → a ∈ D →
      rightConjugateElem q a ∈ Q0 := by
    intro q a hqQ0 haD
    have haH := PFchapter4section1.rankOneSplit_D_le_M hD_eq haD
    rcases (hsec2.Q0_def q).1 hqQ0 with rfl | ⟨hqH, hqI⟩
    · simpa [rightConjugateElem] using Q0.one_mem
    · exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem haH) hqH) haH,
          isInvolution_rightConjugateElem hqI⟩)
  have hK_forbidden : ∀ x y a : G,
      x ∈ Q0 → y ∈ Q0 → a ∈ D → a ∈ K →
      f (omega i * x) = rightConjugateElem (omega i * y) a → False := by
    intro x y a hxQ0 hyQ0 haD haK heq
    have hxQ : omega i * x ∈ Q :=
      Q.mul_mem homega.1 (hsec2.Q0_le_Q hxQ0)
    have hyQ : omega i * y ∈ Q :=
      Q.mul_mem homega.1 (hsec2.Q0_le_Q hyQ0)
    have hx1 : omega i * x ≠ 1 := by
      intro hxone
      apply homega.2
      have homega_eq : omega i = (omega i * x) * x⁻¹ := by simp [mul_assoc]
      rw [homega_eq, hxone]
      simpa using Q0.inv_mem hxQ0
    have hy1 : omega i * y ≠ 1 := by
      intro hyone
      apply homega.2
      have homega_eq : omega i = (omega i * y) * y⁻¹ := by simp [mul_assoc]
      rw [homega_eq, hyone]
      simpa using Q0.inv_mem hyQ0
    have hx0 : omega i * x ∉ Q0 := by
      intro hxprod
      apply homega.2
      have homega_eq : omega i = (omega i * x) * x⁻¹ := by simp [mul_assoc]
      rw [homega_eq]
      exact Q0.mul_mem hxprod (Q0.inv_mem hxQ0)
    have ha_t : rightConjugateElem a t = a⁻¹ := ((hsec2.K_def a).mp haK).2
    have hdouble := PFchapter4section1.claim_H2 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega i * x) hxQ hx1
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega i * y) a hyQ hy1 haD
    have hz_eq : omega i * x =
        rightConjugateElem (f (omega i * y)) a⁻¹ := by
      calc
        omega i * x = f (f (omega i * x)) := hdouble.symm
        _ = f (rightConjugateElem (omega i * y) a) := by rw [← heq]
        _ = rightConjugateElem (f (omega i * y))
            (rightConjugateElem a t) := htransport
        _ = rightConjugateElem (f (omega i * y)) a⁻¹ := by rw [ha_t]
    have hreverse : f (omega i * y) =
        rightConjugateElem (omega i * x) a := by
      have hconj := congrArg (fun z : G => rightConjugateElem z a) hz_eq
      simpa [rightConjugateElem, mul_assoc] using hconj.symm
    by_cases hxy : x = y
    · subst y
      exact (claim_5_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        (omega i * x) 1 a hxQ hx0 Q0.one_mem haD (by simpa using heq)) rfl
    · have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        (omega i) (omega i) x y y x a a homega.1 homega.2 homega.1 homega.2
        hxQ0 hyQ0 hyQ0 hxQ0 haD haD hxy heq hreverse
      exact hnot ⟨1, K.one_mem, by simp⟩
  let Fiber := {x : G // x ∈ Q0 ∧
    (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
      f (omega i * x) = rightConjugateElem (omega i) d * q0)}
  have hcardFiber : Nat.card Fiber = m - 1 := by
    simpa [Fiber] using
      (claim_8 H D Q K V W Q0 S Q1 KW t s (omega i) f g h m n i i omega
        hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
        ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem
        hh_mem hcanonical_eq hKW hWorder hn ⟨hi, hin⟩ ⟨hi, hin⟩
        horbit_representatives rfl)
  let Data (u : Fiber) := {p : G × G × G //
    p.1 ∈ K ∧ p.2.1 ∈ W ∧ p.2.2 ∈ Q0 ∧
      f (omega i * (u : G)) =
        rightConjugateElem (omega i * p.2.2) (p.1 * p.2.1)}
  have hdata_nonempty : ∀ u : Fiber, Nonempty (Data u) := by
    intro u
    rcases u.property.2 with ⟨d, q0, hdKW, hq0, hu⟩
    rcases hKW_decomp d hdKW with ⟨k, w, hkK, hwW, rfl⟩
    let y := rightConjugateElem q0 (k * w)⁻¹
    have hkwD : k * w ∈ D :=
      D.mul_mem (hsec2.K_le_D hkK) (hW_le_D hwW)
    have hyQ0 : y ∈ Q0 := hQ0_conj_D q0 (k * w)⁻¹ hq0 (D.inv_mem hkwD)
    refine ⟨⟨(k, w, y), hkK, hwW, hyQ0, ?_⟩⟩
    calc
      f (omega i * (u : G)) = rightConjugateElem (omega i) (k * w) * q0 := hu
      _ = rightConjugateElem (omega i * y) (k * w) := by
        simp [y, rightConjugateElem, mul_assoc]
  let data (u : Fiber) : Data u := Classical.choice (hdata_nonempty u)
  let kOf (u : Fiber) : G := (data u).val.1
  let wOf (u : Fiber) : G := (data u).val.2.1
  let qOf (u : Fiber) : G := (data u).val.2.2
  have hkOf (u : Fiber) : kOf u ∈ K := (data u).property.1
  have hwOf (u : Fiber) : wOf u ∈ W := (data u).property.2.1
  have hqOf (u : Fiber) : qOf u ∈ Q0 := (data u).property.2.2.1
  have heqOf (u : Fiber) :
      f (omega i * (u : G)) =
        rightConjugateElem (omega i * qOf u) (kOf u * wOf u) :=
    (data u).property.2.2.2
  have hw_ne_one (u : Fiber) : wOf u ≠ 1 := by
    intro hwone
    have hparamK : kOf u * wOf u ∈ K := by simpa [hwone] using hkOf u
    exact hK_forbidden (u : G) (qOf u) (kOf u * wOf u)
      u.property.1 (hqOf u) (hsec2.K_le_D hparamK) hparamK (heqOf u)
  let phi : Fiber → {w : W // w ≠ 1} := fun u =>
    ⟨⟨wOf u, hwOf u⟩, fun hw => hw_ne_one u (congrArg Subtype.val hw)⟩
  have hphi_inj : Function.Injective phi := by
    intro u v huv
    by_contra huv_ne
    have huv_val : (u : G) ≠ (v : G) := fun huv_val =>
      huv_ne (Subtype.ext huv_val)
    have hw_eq : wOf u = wOf v :=
      congrArg (fun w : {w : W // w ≠ 1} => (w.1 : G)) huv
    have hkdiff : (kOf u)⁻¹ * kOf v ∈ K :=
      K.mul_mem (K.inv_mem (hkOf u)) (hkOf v)
    have hcomm : ((kOf u)⁻¹ * kOf v) * wOf u =
        wOf u * ((kOf u)⁻¹ * kOf v) :=
      Subgroup.mem_centralizer_iff.mp (hW_centralizes_K (hwOf u))
        ((kOf u)⁻¹ * kOf v) hkdiff
    have hdcos : kOf v * wOf v =
        (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by
      rw [← hw_eq]
      calc
        kOf v * wOf u = kOf u * ((kOf u)⁻¹ * kOf v) * wOf u := by group
        _ = kOf u * (wOf u * ((kOf u)⁻¹ * kOf v)) := by
          rw [← hcomm]
          group
        _ = (kOf u * wOf u) * ((kOf u)⁻¹ * kOf v) := by group
    have hd_u : kOf u * wOf u ∈ D :=
      D.mul_mem (hsec2.K_le_D (hkOf u)) (hW_le_D (hwOf u))
    have hd_v : kOf v * wOf v ∈ D :=
      D.mul_mem (hsec2.K_le_D (hkOf v)) (hW_le_D (hwOf v))
    have hnot := claim_7 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega i) (omega i) (u : G) (v : G) (qOf u) (qOf v)
      (kOf u * wOf u) (kOf v * wOf v) homega.1 homega.2 homega.1 homega.2
      u.property.1 v.property.1 (hqOf u) (hqOf v) hd_u hd_v huv_val
      (heqOf u) (heqOf v)
    exact hnot ⟨(kOf u)⁻¹ * kOf v, hkdiff, hdcos⟩
  have hcardWne : Nat.card {w : W // w ≠ 1} = m - 1 := by
    letI := Fintype.ofFinite W
    have hcard : Nat.card {w : W // w ≠ 1} = Nat.card W - 1 := by
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_subtype_compl (fun w : W => w = 1))
    simpa [hWorder] using hcard
  letI := Fintype.ofFinite Fiber
  letI := Fintype.ofFinite {w : W // w ≠ 1}
  have hphi_bij : Function.Bijective phi :=
    (Fintype.bijective_iff_injective_and_card phi).2 ⟨hphi_inj, by
      simpa [Nat.card_eq_fintype_card] using hcardFiber.trans hcardWne.symm⟩
  let zetaW : {w : W // w ≠ 1} :=
    ⟨⟨zeta, hzeta⟩, fun hz => hzeta_ne (congrArg Subtype.val hz)⟩
  rcases hphi_bij.2 zetaW with ⟨u, hu⟩
  have hwzeta : wOf u = zeta :=
    congrArg (fun w : {w : W // w ≠ 1} => (w.1 : G)) hu
  exact ⟨u, qOf u, kOf u, u.property.1, hqOf u, hkOf u, by
    simpa [hwzeta] using heqOf u⟩

private theorem claim_9_conjugation_calc_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ i : ℕ, ∀ x z k a : G, 1 ≤ i → i ≤ n →
      (omega i ∈ Q ∧ omega i ∉ Q0) → x ∈ Q0 → z ∈ Q0 →
      k ∈ K → a ∈ K → a ^ 2 = k →
        f (omega i * x) = rightConjugateElem (omega i * z) (k * zeta) →
          f (rightConjugateElem (omega i * x) a) =
            rightConjugateElem
              (rightConjugateElem (omega i * x) a * rightConjugateElem (x * z) a)
              zeta := by
  intro i x z k a hi hin homega hx hz hk ha hak hfk
  have hsec2 := hsection3.1
  have hxQ : x ∈ Q := hsec2.Q0_le_Q hx
  have hprodQ : omega i * x ∈ Q := Q.mul_mem homega.1 hxQ
  have hprod_ne : omega i * x ≠ 1 := by
    intro hprod_one
    have hprodQ0 : omega i * x ∈ Q0 := by
      simp [hprod_one]
    have homegaQ0 : omega i ∈ Q0 := by
      have hmul : (omega i * x) * x⁻¹ ∈ Q0 :=
        Q0.mul_mem hprodQ0 (Q0.inv_mem hx)
      simpa [mul_assoc] using hmul
    exact homega.2 homegaQ0
  have haD : a ∈ D := hsec2.K_le_D ha
  have ha_t : rightConjugateElem a t = a⁻¹ := ((hsec2.K_def a).mp ha).2
  have hf_conj :
      f (rightConjugateElem (omega i * x) a) =
        rightConjugateElem (f (omega i * x)) a⁻¹ := by
    simpa [ha_t] using
      PFchapter4section1.claim_H3 H Q D t f g h
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq (omega i * x) a hprodQ hprod_ne haD
  have hx_sq : x ^ 2 = 1 :=
    claim_9_Q0_sq_eq_one H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen x hx
  have hx_mul : x * x = 1 := by
    simpa [pow_two] using hx_sq
  have hcomm : a * zeta = zeta * a :=
    claim_9_W_commutes_K H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
      zeta a hzeta ha
  have hcz : Commute a zeta := hcomm
  calc
    f (rightConjugateElem (omega i * x) a)
        = rightConjugateElem (f (omega i * x)) a⁻¹ := hf_conj
    _ = rightConjugateElem (rightConjugateElem (omega i * z) (k * zeta)) a⁻¹ := by
      rw [hfk]
    _ = rightConjugateElem (omega i * z) (a * zeta) := by
      subst k
      simp [rightConjugateElem, pow_two, hcomm, mul_assoc]
      rw [← mul_assoc zeta⁻¹ a⁻¹ (omega i * (z * (zeta * a)))]
      rw [← hcz.inv_inv.eq]
      rw [mul_assoc]
    _ =
        rightConjugateElem
          (rightConjugateElem (omega i * x) a * rightConjugateElem (x * z) a)
          zeta := by
      simp [rightConjugateElem, mul_assoc]
      rw [← mul_assoc x x (z * (a * zeta))]
      rw [hx_mul]
      simp

private theorem claim_9_sq_surjective_of_odd_card
    {X : Type*} [Group X] [Finite X] (hXodd : Odd (Nat.card X)) :
    Function.Surjective (fun x : X => x ^ 2) := by
  intro x
  have hxord_dvd : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
  have hxord_odd : Odd (orderOf x) := hXodd.of_dvd_nat hxord_dvd
  have hxord_coprime : Nat.Coprime 2 (orderOf x) := by
    simpa using hxord_odd.coprime_two_left
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := x) (n := 2) hxord_coprime
  refine ⟨x ^ m, ?_⟩
  calc
    (x ^ m) ^ 2 = x ^ (m * 2) := by rw [pow_mul]
    _ = x ^ (2 * m) := by rw [Nat.mul_comm]
    _ = (x ^ 2) ^ m := by rw [pow_mul]
    _ = x := hm

private theorem claim_9_K_square_root_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ k : G, k ∈ K → ∃ a : G, a ∈ K ∧ a ^ 2 = k := by
  intro k hk
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have _ := hKW
  have _ := hzeta
  have _ := hzeta_ne
  have _ := hzeta_gen
  have _ := omega
  have _ := n
  have hsec2 := hsection3.1
  have hKodd : Odd (Nat.card K) :=
    odd_of_card_dvd hsec2.hA.A1.D_odd (Subgroup.card_dvd_of_le hsec2.K_le_D)
  rcases claim_9_sq_surjective_of_odd_card (X := K) hKodd ⟨k, hk⟩ with ⟨a, ha⟩
  refine ⟨a, a.property, ?_⟩
  exact congrArg (fun x : K => (x : G)) ha

private theorem claim_9_rightConjugate_Q_mem_of_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ q k : G, q ∈ Q → k ∈ K → rightConjugateElem q k ∈ Q := by
  intro q k hq hk
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have _ := hKW
  have _ := hzeta
  have _ := hzeta_ne
  have _ := hzeta_gen
  have _ := omega
  have _ := n
  have hsec2 := hsection3.1
  have hA1 := hsec2.hA.A1
  have hkD : k ∈ D := hsec2.K_le_D hk
  let qH : H := ⟨q, hA1.Q_le_H hq⟩
  let kH : H := ⟨k, hA1.D_le_H hkD⟩
  have hqH : qH ∈ Q.subgroupOf H := by
    simpa [qH, Subgroup.mem_subgroupOf] using hq
  have hconj := hA1.Q_normal_in_H.conj_mem qH hqH kH⁻¹
  simpa [qH, kH, Subgroup.mem_subgroupOf, rightConjugateElem, mul_assoc] using hconj

private theorem claim_9_rightConjugate_Q0_mem_of_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ q k : G, q ∈ Q0 → k ∈ K → rightConjugateElem q k ∈ Q0 := by
  intro q k hq hk
  classical
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have _ := hKW
  have _ := hzeta
  have _ := hzeta_ne
  have _ := hzeta_gen
  have _ := omega
  have _ := n
  have hsec2 := hsection3.1
  let d : D := ⟨k⁻¹, D.inv_mem (hsec2.K_le_D hk)⟩
  let qQ0 : Q0 := ⟨q, hq⟩
  have hmem :=
    PFchapter1section2.proposition_3_Q0_rightConjugate_mem_of_D
      H D Q K V W Q0 S Q1 t hsec2 d qQ0
  simpa [d, qQ0] using hmem

private theorem claim_9_omega_conj_mem_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ i : ℕ, ∀ x a : G, 1 ≤ i → i ≤ n →
      (omega i ∈ Q ∧ omega i ∉ Q0) → x ∈ Q0 → a ∈ K →
        rightConjugateElem (omega i * x) a ∈ Q ∧
        rightConjugateElem (omega i * x) a ∉ Q0 := by
  intro i x a hi hin homega hx ha
  have hsec2 := hsection3.1
  have hxQ : x ∈ Q := hsec2.Q0_le_Q hx
  have hprodQ : omega i * x ∈ Q := Q.mul_mem homega.1 hxQ
  constructor
  · exact
      claim_9_rightConjugate_Q_mem_of_K H D Q K V W Q0 S Q1 KW
        t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
        (omega i * x) a hprodQ ha
  · intro hconjQ0
    have hbackQ0 :
        rightConjugateElem (rightConjugateElem (omega i * x) a) a⁻¹ ∈ Q0 :=
      claim_9_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 KW
        t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
        (rightConjugateElem (omega i * x) a) a⁻¹ hconjQ0 (K.inv_mem ha)
    have hprodQ0 : omega i * x ∈ Q0 := by
      simpa [rightConjugateElem, mul_assoc] using hbackQ0
    have homegaQ0 : omega i ∈ Q0 := by
      have hmul : (omega i * x) * x⁻¹ ∈ Q0 := Q0.mul_mem hprodQ0 (Q0.inv_mem hx)
      simpa [mul_assoc] using hmul
    exact homega.2 homegaQ0

private theorem claim_9_Q0_conj_product_mem_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ x z a : G, x ∈ Q0 → z ∈ Q0 → a ∈ K →
      rightConjugateElem (x * z) a ∈ Q0 := by
  intro x z a hx hz ha
  exact
    claim_9_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
      (x * z) a (Q0.mul_mem hx hz) ha

private theorem claim_9_quotient_orbit_conj_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W) :
    ∀ i : ℕ, ∀ x a : G, 1 ≤ i → i ≤ n → x ∈ Q0 → a ∈ K →
      (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧ rightConjugateElem (omega i * x) a = rightConjugateElem (omega i) d * q0) := by
  intro i x a _hi _hin hx ha
  refine ⟨a, rightConjugateElem x a, ?_, ?_, ?_⟩
  · rw [hKW]
    exact Subgroup.mem_sup_left ha
  · simpa using
      claim_9_Q0_conj_product_mem_obligation H D Q K V W Q0 S Q1 KW
        t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
        x 1 a hx Q0.one_mem ha
  · simp [rightConjugateElem, mul_assoc]

public theorem claim_9
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 KW : Subgroup G) (t s zeta : G) (f g h : G → G)
    (omega : ℕ → G) (m n : ℕ)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hKW : KW = K ⊔ W) (hzeta : zeta ∈ W) (hzeta_ne : zeta ≠ 1)
    (hzeta_gen : Subgroup.closure ({zeta} : Set G) = W)
    (hWorder : m = Nat.card W) (hn : n * m = Nat.card Q0 + 1)
    (horbit_representatives :
      (∀ j : ℕ, 1 ≤ j → j ≤ n → omega j ∈ Q ∧ omega j ∉ Q0) ∧
      (∀ x : G, x ∈ Q → x ∉ Q0 →
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧
          ∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
            x = rightConjugateElem (omega j) d * q0) ∧
      (∀ j k : ℕ, 1 ≤ j → j ≤ n → 1 ≤ k → k ≤ n →
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧
          omega j = rightConjugateElem (omega k) d * q0) → j = k)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∃ omega' y : G, omega' ∈ Q ∧ omega' ∉ Q0 ∧ y ∈ Q0 ∧ y ≠ 1 ∧
        (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧ omega' = rightConjugateElem (omega i) d * q0) ∧
          f omega' = rightConjugateElem (omega' * y) zeta := by
  intro i hi hin
  have homega := horbit_representatives.1 i hi hin
  have hK_square_root :=
    claim_9_K_square_root_obligation H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
  have homega_conj_mem :=
    claim_9_omega_conj_mem_obligation H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
  have hQ0_conj_product_mem :=
    claim_9_Q0_conj_product_mem_obligation H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
  have hquotient_orbit_conj :=
    claim_9_quotient_orbit_conj_obligation H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
  rcases
    claim_9_choice_from_claim_5_7_8_obligation H D Q K V W Q0 S Q1 KW
      t s zeta f g h omega m n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen hWorder hn horbit_representatives
      i hi hin with
    ⟨x, z, k, hx, hz, hk, hfk⟩
  rcases hK_square_root k hk with ⟨a, ha, hak⟩
  let omega' := rightConjugateElem (omega i * x) a
  let y := rightConjugateElem (x * z) a
  have homega' : omega' ∈ Q ∧ omega' ∉ Q0 := by
    simpa [omega'] using homega_conj_mem i x a hi hin homega hx ha
  have hy : y ∈ Q0 := by
    simpa [y] using hQ0_conj_product_mem x z a hx hz ha
  have hfinal :
      f omega' = rightConjugateElem (omega' * y) zeta := by
    simpa [omega', y] using
      claim_9_conjugation_calc_obligation H D Q K V W Q0 S Q1 KW
        t s zeta f g h omega n hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq hKW hzeta hzeta_ne hzeta_gen
        i x z k a hi hin homega hx hz hk ha hak hfk
  have hsec2 := hsection3.1
  have hzetaD : zeta ∈ D :=
    PFchapter1section2.proposition_3_W_le_D H D Q K V W Q0 S Q1 t hsec2 hzeta
  have hyne : y ≠ 1 :=
    claim_5_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega' y zeta homega'.1 homega'.2 hy hzetaD hfinal
  have horbit : (∃ d q0 : G, d ∈ KW ∧ q0 ∈ Q0 ∧ omega' = rightConjugateElem (omega i) d * q0) := by
    simpa [omega'] using hquotient_orbit_conj i x a hi hin hx ha
  exact ⟨omega', y, homega'.1, homega'.2, hy, hyne, horbit, hfinal⟩

end PFchapter4section2
end CFSG.BenderSuzuki
