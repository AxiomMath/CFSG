module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_5_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (6) -/

/--
Source obligation for Claim (6).  The printed proof chooses `k ∈ K` with
`x = s^k`, substitutes Claim (2), and rewrites the resulting equality into an
instance of Claim (5)(b) with parameter `a * k^2`.  The current setup does not
expose that `Q0` parameterization or the Claim (2) substitution calculation as
local data.
-/
private theorem claim_6_reduces_to_claim_5_obligation
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
    ∀ omega x y a : G, omega ∈ Q → omega ∉ Q0 → x ∈ Q0 → y ∈ Q0 →
      x ≠ 1 → a ∈ D → f (omega * x) = rightConjugateElem (f omega * y) a →
        a ∈ K →
          ∃ omega' y' b : G,
            omega' ∈ Q ∧ omega' ∉ Q0 ∧ y' ∈ Q0 ∧ b ∈ D ∧ b ∈ K ∧
              f omega' = rightConjugateElem (omega' * y') b := by
  intro omega x y a homega homega0 hxQ0 hyQ0 hx1 haD ha_eq haK
  have hsec2 := hsection3.1
  rcases (hsec2.Q0_def x).1 hxQ0 with hx_one | ⟨hxH, hxI⟩
  · exact (hx1 hx_one).elim
  rcases
      ((PFchapter1section1.proposition_3 H D Q t hsec2.hA.A1).2
        s hsection3.s_mem_H hsection3.s_involution x).1 ⟨hxH, hxI⟩ with
    ⟨k, hkKset, hsk⟩
  have hkK : k ∈ K := (hsec2.K_def k).2 hkKset
  have hkinvK : k⁻¹ ∈ K := K.inv_mem hkK
  have hkinvH : k⁻¹ ∈ H :=
    PFchapter4section1.rankOneSplit_D_le_M hD_eq (hsec2.K_le_D hkinvK)
  let r := rightConjugateElem s k⁻¹
  have hrQ0 : r ∈ Q0 :=
    (hsec2.Q0_def _).2 (Or.inr
      ⟨H.mul_mem (H.mul_mem (H.inv_mem hkinvH) hsection3.s_mem_H) hkinvH,
        isInvolution_rightConjugateElem hsection3.s_involution⟩)
  have hrI : IsInvolution r := isInvolution_rightConjugateElem hsection3.s_involution
  have hrr : r * r = 1 := by simpa [pow_two] using hrI.sq_eq_one
  have homega1 : omega ≠ 1 := fun homega_one =>
    homega0 (homega_one ▸ Q0.one_mem)
  have hfomegaQ : f omega ∈ Q := (hf_mem omega homega homega1).1
  have hfomega1 : f omega ≠ 1 := (hf_mem omega homega homega1).2
  have hfomega0 : f omega ∉ Q0 := by
    intro hfomegaQ0
    exact homega0
      ((claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega homega homega1).1 hfomegaQ0)
  let omega' := f omega * r
  have homega'Q : omega' ∈ Q := Q.mul_mem hfomegaQ (hsec2.Q0_le_Q hrQ0)
  have homega'0 : omega' ∉ Q0 := by
    intro homega'Q0
    apply hfomega0
    have hfomega_eq : f omega = omega' * r⁻¹ := by
      simp [omega', mul_assoc]
    rw [hfomega_eq]
    exact Q0.mul_mem homega'Q0 (Q0.inv_mem hrQ0)
  let b := a * k ^ 2
  have hbK : b ∈ K := K.mul_mem haK (K.pow_mem hkK 2)
  have hbD : b ∈ D := hsec2.K_le_D hbK
  have hbinvH : b⁻¹ ∈ H :=
    H.inv_mem (PFchapter4section1.rankOneSplit_D_le_M hD_eq hbD)
  let z := rightConjugateElem x b⁻¹
  have hzQ0 : z ∈ Q0 :=
    (hsec2.Q0_def _).2 (Or.inr
      ⟨H.mul_mem (H.mul_mem (H.inv_mem hbinvH) hxH) hbinvH,
        isInvolution_rightConjugateElem hxI⟩)
  let y' := r * y * z
  have hy'Q0 : y' ∈ Q0 := Q0.mul_mem (Q0.mul_mem hrQ0 hyQ0) hzQ0
  have hclaim2 := claim_2 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
    hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
    omega k homega homega0 hkK
  have heq :
      rightConjugateElem (f omega') (k⁻¹ ^ 2) * r =
        rightConjugateElem (f omega * y) a := by
    calc
      rightConjugateElem (f omega') (k⁻¹ ^ 2) * r =
          f (omega * rightConjugateElem s k) := by
        simpa [omega', r] using hclaim2.symm
      _ = f (omega * x) := by rw [hsk]
      _ = rightConjugateElem (f omega * y) a := ha_eq
  have heq_base :
      rightConjugateElem (f omega') (k⁻¹ ^ 2) =
        rightConjugateElem (f omega * y) a * r := by
    calc
      rightConjugateElem (f omega') (k⁻¹ ^ 2) =
          rightConjugateElem (f omega') (k⁻¹ ^ 2) * 1 := by simp
      _ = rightConjugateElem (f omega') (k⁻¹ ^ 2) * (r * r) := by rw [hrr]
      _ = (rightConjugateElem (f omega') (k⁻¹ ^ 2) * r) * r :=
        (mul_assoc _ _ _).symm
      _ = rightConjugateElem (f omega * y) a * r := by rw [heq]
  have hfomega' :
      f omega' = rightConjugateElem (rightConjugateElem (f omega * y) a * r) (k ^ 2) := by
    have hback := congrArg (fun u : G => rightConjugateElem u (k ^ 2)) heq_base
    calc
      f omega' =
          rightConjugateElem (rightConjugateElem (f omega') (k⁻¹ ^ 2)) (k ^ 2) := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = rightConjugateElem (rightConjugateElem (f omega * y) a * r) (k ^ 2) :=
        hback
  have hr_transport : rightConjugateElem r (k ^ 2) = x := by
    calc
      rightConjugateElem r (k ^ 2) = rightConjugateElem s k := by
        simp [r, rightConjugateElem, pow_two, mul_assoc]
      _ = x := hsk
  have hz_back : rightConjugateElem z b = x := by
    simp [z, rightConjugateElem, mul_assoc]
  have homega_y' : omega' * y' = f omega * y * z := by
    dsimp [omega', y']
    calc
      (f omega * r) * (r * y * z) = f omega * ((r * r) * (y * z)) := by group
      _ = f omega * y * z := by
        rw [hrr, one_mul]
        exact (mul_assoc _ _ _).symm
  have htarget :
      rightConjugateElem (omega' * y') b =
        rightConjugateElem (rightConjugateElem (f omega * y) a * r) (k ^ 2) := by
    calc
      rightConjugateElem (omega' * y') b =
          rightConjugateElem (f omega * y * z) b := by rw [homega_y']
      _ = rightConjugateElem (f omega * y) b * rightConjugateElem z b := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (rightConjugateElem (f omega * y) a) (k ^ 2) * x := by
        rw [hz_back]
        congr 1
        simp [b, rightConjugateElem, pow_two, mul_assoc]
      _ = rightConjugateElem (rightConjugateElem (f omega * y) a) (k ^ 2) *
          rightConjugateElem r (k ^ 2) := by rw [hr_transport]
      _ = rightConjugateElem (rightConjugateElem (f omega * y) a * r) (k ^ 2) := by
        simp [rightConjugateElem, mul_assoc]
  exact ⟨omega', y', b, homega'Q, homega'0, hy'Q0, hbD, hbK, hfomega'.trans htarget.symm⟩

public theorem claim_6
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
    ∀ omega x y a : G, omega ∈ Q → omega ∉ Q0 → x ∈ Q0 → y ∈ Q0 →
      x ≠ 1 → a ∈ D → f (omega * x) = rightConjugateElem (f omega * y) a →
        a ∉ K := by
  intro omega x y a homega homega0 hx hy hx1 ha hfxy haK
  rcases claim_6_reduces_to_claim_5_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega x y a homega homega0
      hx hy hx1 ha hfxy haK with
    ⟨omega', y', b, homega', homega'0, hy', hbD, hbK, hfb⟩
  exact
    (claim_5_b H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega' y' b homega' homega'0 hy' hbD hfb) hbK

end PFchapter4section2
end CFSG.BenderSuzuki
