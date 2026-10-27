module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_6

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (7) -/

/--
Source obligation for Claim (7).  The printed proof combines the two displayed
equalities to rewrite `f (omega * x₂)` in terms of `f (omega * x₁)` with
parameter `a₁⁻¹ * a₂`, then applies Claim (6).  The current setup does not
expose that coordinate rearrangement as local data.
-/
private theorem claim_7_reduces_to_claim_6_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
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
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ omega omega' x₁ x₂ y₁ y₂ a₁ a₂ : G,
      omega ∈ Q → omega ∉ Q0 → omega' ∈ Q → omega' ∉ Q0 →
      x₁ ∈ Q0 → x₂ ∈ Q0 → y₁ ∈ Q0 → y₂ ∈ Q0 →
      a₁ ∈ D → a₂ ∈ D → x₁ ≠ x₂ →
      f (omega * x₁) = rightConjugateElem (omega' * y₁) a₁ →
      f (omega * x₂) = rightConjugateElem (omega' * y₂) a₂ →
        (∃ k : G, k ∈ K ∧ a₂ = a₁ * k) →
          ∃ x y a : G,
            x ∈ Q0 ∧ y ∈ Q0 ∧ x ≠ 1 ∧ a ∈ D ∧ a ∈ K ∧
              f ((omega * x₁) * x) =
                rightConjugateElem (f (omega * x₁) * y) a := by
  intro omega omega' x₁ x₂ y₁ y₂ a₁ a₂ homega homega0 homega' homega'0
    hx₁ hx₂ hy₁ hy₂ ha₁ ha₂ hxne hf₁ hf₂ hcos
  have hsec2 := hsection3.1
  have hQ0_inv_self : ∀ u : G, u ∈ Q0 → u⁻¹ = u := by
    intro u huQ0
    rcases (hsec2.Q0_def u).1 huQ0 with rfl | ⟨_, huI⟩
    · simp
    · exact huI.inv_eq_self
  have hx₁sq : x₁ * x₁ = 1 := by
    have := hQ0_inv_self x₁ hx₁
    calc
      x₁ * x₁ = x₁⁻¹ * x₁ := by rw [this]
      _ = 1 := inv_mul_cancel x₁
  have hy₁sq : y₁ * y₁ = 1 := by
    have := hQ0_inv_self y₁ hy₁
    calc
      y₁ * y₁ = y₁⁻¹ * y₁ := by rw [this]
      _ = 1 := inv_mul_cancel y₁
  let x := x₁ * x₂
  have hxQ0 : x ∈ Q0 := Q0.mul_mem hx₁ hx₂
  have hx1 : x ≠ 1 := by
    intro hx_one
    apply hxne
    have hx₁_eq : x₁ = x₂⁻¹ := eq_inv_of_mul_eq_one_left hx_one
    rw [hx₁_eq, hQ0_inv_self x₂ hx₂]
  let y := rightConjugateElem (y₁ * y₂) a₁
  have ha₁H : a₁ ∈ H := PFchapter4section1.rankOneSplit_D_le_M hD_eq ha₁
  have hyQ0 : y ∈ Q0 := by
    have hyprodQ0 : y₁ * y₂ ∈ Q0 := Q0.mul_mem hy₁ hy₂
    rcases (hsec2.Q0_def (y₁ * y₂)).1 hyprodQ0 with hy_one | ⟨hyH, hyI⟩
    · simp [y, hy_one, rightConjugateElem]
    · exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem ha₁H) hyH) ha₁H,
          isInvolution_rightConjugateElem hyI⟩)
  let a := a₁⁻¹ * a₂
  have haD : a ∈ D := D.mul_mem (D.inv_mem ha₁) ha₂
  rcases hcos with ⟨k, hkK, ha₂_eq⟩
  have haK : a ∈ K := by
    simp [a, ha₂_eq, hkK]
  have hbase_mul : (omega * x₁) * x = omega * x₂ := by
    dsimp [x]
    calc
      (omega * x₁) * (x₁ * x₂) = omega * (x₁ * x₁) * x₂ := by group
      _ = omega * x₂ := by rw [hx₁sq]; simp
  have hinside :
      f (omega * x₁) * y = rightConjugateElem (omega' * y₂) a₁ := by
    calc
      f (omega * x₁) * y =
          rightConjugateElem (omega' * y₁) a₁ *
            rightConjugateElem (y₁ * y₂) a₁ := by rw [hf₁]
      _ = rightConjugateElem ((omega' * y₁) * (y₁ * y₂)) a₁ := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (omega' * y₂) a₁ := by
        congr 1
        calc
          (omega' * y₁) * (y₁ * y₂) = omega' * (y₁ * y₁) * y₂ := by group
          _ = omega' * y₂ := by rw [hy₁sq]; simp
  have hresult :
      f ((omega * x₁) * x) = rightConjugateElem (f (omega * x₁) * y) a := by
    calc
      f ((omega * x₁) * x) = f (omega * x₂) := by rw [hbase_mul]
      _ = rightConjugateElem (omega' * y₂) a₂ := hf₂
      _ = rightConjugateElem
            (rightConjugateElem (omega' * y₂) a₁) (a₁⁻¹ * a₂) := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (f (omega * x₁) * y) a := by
        rw [hinside]
  exact ⟨x, y, a, hxQ0, hyQ0, hx1, haD, haK, hresult⟩

public theorem claim_7
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
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
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ omega omega' x₁ x₂ y₁ y₂ a₁ a₂ : G,
      omega ∈ Q → omega ∉ Q0 → omega' ∈ Q → omega' ∉ Q0 →
      x₁ ∈ Q0 → x₂ ∈ Q0 → y₁ ∈ Q0 → y₂ ∈ Q0 →
      a₁ ∈ D → a₂ ∈ D → x₁ ≠ x₂ →
      f (omega * x₁) = rightConjugateElem (omega' * y₁) a₁ →
      f (omega * x₂) = rightConjugateElem (omega' * y₂) a₂ →
        a₂ ∉ {y : G | ∃ k : G, k ∈ K ∧ y = a₁ * k} := by
  intro omega omega' x₁ x₂ y₁ y₂ a₁ a₂ homega homega0 homega' homega'0
    hx₁ hx₂ hy₁ hy₂ ha₁ ha₂ hxne hf₁ hf₂ hcos
  have hcos' : ∃ k : G, k ∈ K ∧ a₂ = a₁ * k := hcos
  rcases claim_7_reduces_to_claim_6_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega omega' x₁ x₂ y₁ y₂ a₁ a₂
      homega homega0 homega' homega'0 hx₁ hx₂ hy₁ hy₂ ha₁ ha₂ hxne hf₁ hf₂ hcos' with
    ⟨x, y, a, hx, hy, hx1, haD, haK, hfxy⟩
  have hbaseQ : omega * x₁ ∈ Q := Q.mul_mem homega (hsection3.1.Q0_le_Q hx₁)
  have hbase0 : omega * x₁ ∉ Q0 := by
    intro hbaseQ0
    apply homega0
    have homega_eq : omega = (omega * x₁) * x₁⁻¹ := by simp [mul_assoc]
    rw [homega_eq]
    exact Q0.mul_mem hbaseQ0 (Q0.inv_mem hx₁)
  exact
    (claim_6 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      (omega * x₁) x y a hbaseQ hbase0 hx hy hx1 haD hfxy) haK

end PFchapter4section2
end CFSG.BenderSuzuki

