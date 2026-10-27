module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_5_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (5)(b) -/

/--
Source obligation for the second half of Claim (5).  The printed proof derives
`a⁻¹ * a^{-t} ≠ 1` from the H2/H3 transport formula and Claim (4).  The
current setup has neither that specialized transport calculation nor the
Claim (4) source package as usable local data.
-/
private theorem claim_5_b_twisted_factor_ne_one_obligation
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
    ∀ omega y a : G, omega ∈ Q → omega ∉ Q0 → y ∈ Q0 → a ∈ D →
      f omega = rightConjugateElem (omega * y) a →
        a⁻¹ * rightConjugateElem a⁻¹ t ≠ 1 := by
  intro omega y a homega homega0 hyQ0 haD hfomega htwist
  have hsec2 := hsection3.1
  have homega1 : omega ≠ 1 := fun homega_one =>
    homega0 (homega_one ▸ Q0.one_mem)
  have hyQ : y ∈ Q := hsec2.Q0_le_Q hyQ0
  have hprodQ : omega * y ∈ Q := Q.mul_mem homega hyQ
  have hprod1 : omega * y ≠ 1 := by
    intro hprod
    apply homega0
    have homega_eq : omega = y⁻¹ := eq_inv_of_mul_eq_one_left hprod
    rw [homega_eq]
    exact Q0.inv_mem hyQ0
  have hA_D : rightConjugateElem a t ∈ D :=
    PFchapter4section1.rightConjugateElem_mem_D ht_involution.inv_eq_self hD_eq haD
  have hAinv_eq : (rightConjugateElem a t)⁻¹ = a := by
    calc
      (rightConjugateElem a t)⁻¹ = rightConjugateElem a⁻¹ t := by
        simp [rightConjugateElem, mul_assoc]
      _ = a := (inv_mul_eq_one.mp htwist).symm
  have homega_transport :
      omega = rightConjugateElem (f (omega * y)) (rightConjugateElem a t) := by
    calc
      omega = f (f omega) :=
        (PFchapter4section1.claim_H2 H Q D t f g h htwo_transitive
          hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
          hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
          omega homega homega1).symm
      _ = f (rightConjugateElem (omega * y) a) := by rw [hfomega]
      _ = rightConjugateElem (f (omega * y)) (rightConjugateElem a t) :=
        PFchapter4section1.claim_H3 H Q D t f g h htwo_transitive
          hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
          hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
          (omega * y) a hprodQ hprod1 haD
  have hfprod : f (omega * y) = rightConjugateElem omega a := by
    have hback := congrArg
      (fun u : G => rightConjugateElem u (rightConjugateElem a t)⁻¹)
      homega_transport
    have hrecover :
        rightConjugateElem omega (rightConjugateElem a t)⁻¹ =
          f (omega * y) := by
      calc
        rightConjugateElem omega (rightConjugateElem a t)⁻¹ =
            rightConjugateElem
              (rightConjugateElem (f (omega * y)) (rightConjugateElem a t))
              (rightConjugateElem a t)⁻¹ := hback
        _ = f (omega * y) := by simp [rightConjugateElem, mul_assoc]
    calc
      f (omega * y) = rightConjugateElem omega (rightConjugateElem a t)⁻¹ :=
        hrecover.symm
      _ = rightConjugateElem omega a := by rw [hAinv_eq]
  have hyy : y * y = 1 := by
    rcases (hsec2.Q0_def y).1 hyQ0 with rfl | ⟨_, hyI⟩
    · simp
    · simpa [pow_two] using hyI.sq_eq_one
  have hyaQ0 : rightConjugateElem y a ∈ Q0 := by
    rcases (hsec2.Q0_def y).1 hyQ0 with rfl | ⟨hyH, hyI⟩
    · simpa [rightConjugateElem] using Q0.one_mem
    · have haH : a ∈ H := PFchapter4section1.rankOneSplit_D_le_M hD_eq haD
      exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem haH) hyH) haH,
          isInvolution_rightConjugateElem hyI⟩)
  have hya_sq : rightConjugateElem y a * rightConjugateElem y a = 1 := by
    calc
      rightConjugateElem y a * rightConjugateElem y a =
          rightConjugateElem (y * y) a := by
        simp [rightConjugateElem, mul_assoc]
      _ = 1 := by rw [hyy]; simp [rightConjugateElem]
  have hfprod_target :
      f (omega * y) = f omega * rightConjugateElem y a := by
    calc
      f (omega * y) = rightConjugateElem omega a := hfprod
      _ = rightConjugateElem (omega * y) a * rightConjugateElem y a := by
        calc
          rightConjugateElem omega a = rightConjugateElem omega a * 1 := by simp
          _ = rightConjugateElem omega a *
              (rightConjugateElem y a * rightConjugateElem y a) := by rw [hya_sq]
          _ = (rightConjugateElem omega a * rightConjugateElem y a) *
              rightConjugateElem y a := (mul_assoc _ _ _).symm
          _ = rightConjugateElem (omega * y) a * rightConjugateElem y a := by
            congr 1
            simp [rightConjugateElem, mul_assoc]
      _ = f omega * rightConjugateElem y a := by rw [hfomega]
  have hy_one := claim_4 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
    hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
    omega y (rightConjugateElem y a) homega homega0 hyQ0 hyaQ0 hfprod_target
  exact
    (claim_5_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega y a homega homega0 hyQ0 haD hfomega) hy_one

private theorem claim_5_b_K_twisted_factor_eq_one_obligation
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
    ∀ a : G, a ∈ K → a⁻¹ * rightConjugateElem a⁻¹ t = 1 := by
  intro a haK
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
  rcases hsection3 with ⟨⟨_, _, hK_def, _, _, _, _, _, _, _, _, _, _, _, _⟩, _⟩
  have hKinv : a⁻¹ ∈ K := K.inv_mem haK
  have hconj : rightConjugateElem a⁻¹ t = (a⁻¹)⁻¹ :=
    ((hK_def a⁻¹).mp hKinv).2
  simp [hconj]

public theorem claim_5_b
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
    ∀ omega y a : G, omega ∈ Q → omega ∉ Q0 → y ∈ Q0 → a ∈ D →
      f omega = rightConjugateElem (omega * y) a → a ∉ K := by
  intro omega y a homega homega0 hy ha hfomega haK
  exact
    (claim_5_b_twisted_factor_ne_one_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega y a homega homega0 hy ha hfomega)
      (claim_5_b_K_twisted_factor_eq_one_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        a haK)

end PFchapter4section2
end CFSG.BenderSuzuki
