module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_3

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (4) -/

/-- On the nonidentity elements of `Q`, the canonical map `f` reflects
membership in `Q0`. -/
public theorem claim_4_f_mem_Q0_iff
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
    ∀ z : G, z ∈ Q → z ≠ 1 → (f z ∈ Q0 ↔ z ∈ Q0) := by
  intro z hzQ hz1
  have hsec2 := hsection3.1
  have hf_preserves : ∀ u : G, u ∈ Q0 → u ≠ 1 → f u ∈ Q0 := by
    intro u huQ0 hu1
    rcases (hsec2.Q0_def u).1 huQ0 with hu_one | ⟨huH, huI⟩
    · exact (hu1 hu_one).elim
    rcases
        ((PFchapter1section1.proposition_3 H D Q t hsec2.hA.A1).2
          s hsection3.s_mem_H hsection3.s_involution u).1 ⟨huH, huI⟩ with
      ⟨k, hkKset, hsk⟩
    have hkK : k ∈ K := (hsec2.K_def k).2 hkKset
    have hkinvH : k⁻¹ ∈ H :=
      H.inv_mem (PFchapter4section1.rankOneSplit_D_le_M hD_eq (hsec2.K_le_D hkK))
    have hskinvQ0 : rightConjugateElem s k⁻¹ ∈ Q0 :=
      (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem hkinvH) hsection3.s_mem_H) hkinvH,
          isInvolution_rightConjugateElem hsection3.s_involution⟩)
    have hfsk := (claim_1_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq k hkK).1
    rw [← hsk, hfsk]
    exact hskinvQ0
  constructor
  · intro hfzQ0
    have hfz := hf_mem z hzQ hz1
    have hffzQ0 := hf_preserves (f z) hfzQ0 hfz.2
    rwa [PFchapter4section1.claim_H2 H Q D t f g h htwo_transitive
      hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
      hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq z hzQ hz1] at hffzQ0
  · intro hzQ0
    exact hf_preserves z hzQ0 hz1

/--
Peterfalvi source `g`-image obligation landing in `Q0`.

The source argument uses the `g`-reflection calculation from the coordinate
model to show that if `f (omega * x) = f omega * y` with `x, y ∈ Q0`, then the
image `g omega` lies in `Q0`. The current `explicit Chapter IV Section 2 hypotheses` exposes only
the abstract canonical maps; it does not include the explicit `g`/`Q0`
reflection formula needed to derive this membership result from the displayed
hypotheses alone.
-/
private theorem claim_4_g_image_mem_Q0_obligation
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
    ∀ omega x y : G, omega ∈ Q → omega ∉ Q0 → x ∈ Q0 → y ∈ Q0 →
      x ≠ 1 → f (omega * x) = f omega * y → g omega ∈ Q0 := by
  intro omega x y homega homega0 hxQ0 hyQ0 hx1 hfxy
  have hsec2 := hsection3.1
  have homega1 : omega ≠ 1 := fun homega_one =>
    homega0 (homega_one ▸ Q0.one_mem)
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
  have hskinvQ0 : rightConjugateElem s k⁻¹ ∈ Q0 :=
    (hsec2.Q0_def _).2 (Or.inr
      ⟨H.mul_mem (H.mul_mem (H.inv_mem hkinvH) hsection3.s_mem_H) hkinvH,
        isInvolution_rightConjugateElem hsection3.s_involution⟩)
  have hclaim3 := claim_3 H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
    hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
    omega k homega homega0 hkK
  have hclaim3' :
      f (omega * x) =
        rightConjugateElem (f (g omega * rightConjugateElem s k⁻¹))
          (rightConjugateElem (h omega) t) * f omega := by
    simpa [hsk] using hclaim3
  have hfomegaQ : f omega ∈ Q := (hf_mem omega homega homega1).1
  have hy_comm_fomega : y * f omega = f omega * y :=
    Q0_commutes_Q H D Q K V W Q0 S Q1 t s hsection3 hC2 y hyQ0
      (f omega) hfomegaQ
  have hconj_eq_y :
      rightConjugateElem (f (g omega * rightConjugateElem s k⁻¹))
        (rightConjugateElem (h omega) t) = y := by
    apply mul_right_cancel (b := f omega)
    calc
      rightConjugateElem (f (g omega * rightConjugateElem s k⁻¹))
            (rightConjugateElem (h omega) t) * f omega =
          f (omega * x) := hclaim3'.symm
      _ = f omega * y := hfxy
      _ = y * f omega := hy_comm_fomega.symm
  have hA_D : rightConjugateElem (h omega) t ∈ D :=
    PFchapter4section1.rightConjugateElem_mem_D ht_involution.inv_eq_self hD_eq
      (hh_mem omega homega homega1)
  have hA_H : rightConjugateElem (h omega) t ∈ H :=
    PFchapter4section1.rankOneSplit_D_le_M hD_eq hA_D
  have hconj_preserves_Q0 :
      ∀ z a : G, z ∈ Q0 → a ∈ H → rightConjugateElem z a ∈ Q0 := by
    intro z a hzQ0 haH
    rcases (hsec2.Q0_def z).1 hzQ0 with rfl | ⟨hzH, hzI⟩
    · simpa [rightConjugateElem] using Q0.one_mem
    · exact (hsec2.Q0_def _).2 (Or.inr
        ⟨H.mul_mem (H.mul_mem (H.inv_mem haH) hzH) haH,
          isInvolution_rightConjugateElem hzI⟩)
  have hconj_reflects_Q0 :
      ∀ z a : G, rightConjugateElem z a ∈ Q0 → a ∈ H → z ∈ Q0 := by
    intro z a hzaQ0 haH
    have hback := hconj_preserves_Q0 (rightConjugateElem z a) a⁻¹ hzaQ0 (H.inv_mem haH)
    simpa [rightConjugateElem, mul_assoc] using hback
  have hfuQ0 : f (g omega * rightConjugateElem s k⁻¹) ∈ Q0 :=
    hconj_reflects_Q0 _ _ (hconj_eq_y ▸ hyQ0) hA_H
  have hgomegaQ : g omega ∈ Q := (hg_mem omega homega homega1).1
  have huQ : g omega * rightConjugateElem s k⁻¹ ∈ Q :=
    Q.mul_mem hgomegaQ (hsec2.Q0_le_Q hskinvQ0)
  by_cases hu1 : g omega * rightConjugateElem s k⁻¹ = 1
  · have hg_eq : g omega = (rightConjugateElem s k⁻¹)⁻¹ :=
      eq_inv_of_mul_eq_one_left hu1
    rw [hg_eq]
    exact Q0.inv_mem hskinvQ0
  · have huQ0 : g omega * rightConjugateElem s k⁻¹ ∈ Q0 :=
      (claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        _ huQ hu1).1 hfuQ0
    have hg_eq :
        g omega = (g omega * rightConjugateElem s k⁻¹) *
          (rightConjugateElem s k⁻¹)⁻¹ := by simp [mul_assoc]
    rw [hg_eq]
    exact Q0.mul_mem huQ0 (Q0.inv_mem hskinvQ0)

/--
Peterfalvi source reflection obligation for `g omega` in `Q0`.

The printed proof also needs the converse reflection: if `omega ∈ Q` and
`g omega ∈ Q0`, then `omega ∈ Q0`. This is the same coordinate-model reflection
datum as above, but expressed in the reverse direction. The present interface
does not expose that `g`/`Q0` reflection package, so the conclusion is kept as
a theorem-local source obligation.
-/
private theorem claim_4_g_image_reflects_Q0_obligation
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
    ∀ omega : G, omega ∈ Q → g omega ∈ Q0 → omega ∈ Q0 := by
  intro omega homega hgomegaQ0
  by_cases homega1 : omega = 1
  · simpa [homega1] using Q0.one_mem
  · have homega_invQ : omega⁻¹ ∈ Q := Q.inv_mem homega
    have homega_inv1 : omega⁻¹ ≠ 1 := by
      simpa using homega1
    have hf_inv_eq : f omega⁻¹ = (g omega)⁻¹ :=
      PFchapter4section1.claim_H1 H Q D t f g h htwo_transitive
        hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
        hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq omega homega homega1
    have hf_invQ0 : f omega⁻¹ ∈ Q0 := by
      rw [hf_inv_eq]
      exact Q0.inv_mem hgomegaQ0
    have homega_invQ0 : omega⁻¹ ∈ Q0 :=
      (claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega⁻¹ homega_invQ homega_inv1).1 hf_invQ0
    simpa using Q0.inv_mem homega_invQ0

public theorem claim_4
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
    ∀ omega x y : G, omega ∈ Q → omega ∉ Q0 → x ∈ Q0 → y ∈ Q0 →
      f (omega * x) = f omega * y → x = 1 := by
  intro omega x y homega homega0 hx hy hfxy
  by_contra hx1
  exact homega0
    (claim_4_g_image_reflects_Q0_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq omega homega
      (claim_4_g_image_mem_Q0_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega x y homega homega0 hx hy hx1 hfxy))

end PFchapter4section2
end CFSG.BenderSuzuki
