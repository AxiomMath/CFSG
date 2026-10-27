module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H5

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (5)(a) -/

/-- Inversion has no fixed orbit on `Q \ Q0` under right conjugation by `D`. -/
private theorem claim_5_a_inversion_moves_D_orbit
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ z d : G, z ∈ Q → z ∉ Q0 → d ∈ D →
      rightConjugateElem z d ≠ z⁻¹ := by
  intro z d hzQ hzQ0 hdD hconj
  let dD : D := ⟨d, hdD⟩
  have hd_order_odd : Odd (orderOf dD) :=
    Odd.of_dvd_nat hsection3.1.hA.A1.D_odd (orderOf_dvd_natCard dD)
  obtain ⟨n, hn⟩ := hd_order_odd
  have hd_eq : d = (d ^ 2) ^ (n + 1) := by
    have hdD_eq : dD = (dD ^ 2) ^ (n + 1) := by
      calc
        dD = dD ^ orderOf dD * dD := by rw [pow_orderOf_eq_one]; simp
        _ = dD ^ (orderOf dD + 1) := by rw [pow_succ]
        _ = dD ^ (2 * (n + 1)) := by rw [hn]; congr 1
        _ = (dD ^ 2) ^ (n + 1) := by rw [pow_mul]
    exact congrArg Subtype.val hdD_eq
  have hconj2 : rightConjugateElem z (d ^ 2) = z := by
    calc
      rightConjugateElem z (d ^ 2) =
          rightConjugateElem (rightConjugateElem z d) d := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = rightConjugateElem z⁻¹ d := by rw [hconj]
      _ = (rightConjugateElem z d)⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = z := by rw [hconj]; simp
  have hcomm2 : Commute z (d ^ 2) := by
    rw [Commute]
    calc
      z * d ^ 2 = d ^ 2 * rightConjugateElem z (d ^ 2) := by
        simp [rightConjugateElem, mul_assoc]
      _ = d ^ 2 * z := by rw [hconj2]
  have hcomm : Commute z d := by
    rw [hd_eq]
    exact hcomm2.pow_right (n + 1)
  have hconj_self : rightConjugateElem z d = z := by
    calc
      rightConjugateElem z d = d⁻¹ * (z * d) := by rw [rightConjugateElem, mul_assoc]
      _ = d⁻¹ * (d * z) := by rw [hcomm]
      _ = z := by simp
  have hzinv : z⁻¹ = z := hconj.symm.trans hconj_self
  have hz1 : z ≠ 1 := fun hz_one => hzQ0 (hz_one ▸ Q0.one_mem)
  apply hzQ0
  exact (hsection3.1.Q0_def z).2 (Or.inr
    ⟨hsection3.1.hA.A1.Q_le_H hzQ,
      ⟨hz1, by
        calc
          z ^ 2 = z * z := pow_two z
          _ = z⁻¹ * z := by rw [hzinv]
          _ = 1 := inv_mul_cancel z⟩⟩)

/--
Source obligation for the first half of Claim (5).  Peterfalvi uses that the
inversion map `j` has no fixed points on the `D`-orbits of `Q - Q0`, and that
`f` is conjugate to `j` in the induced permutation group on those orbits.  The
current `explicit Chapter IV Section 2 hypotheses` exposes only membership data for the canonical
maps, not this orbit-action/conjugacy package.
-/
private theorem claim_5_a_f_moves_D_orbit_obligation
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
    ∀ omega a : G, omega ∈ Q → omega ∉ Q0 → a ∈ D →
      f omega ≠ rightConjugateElem omega a := by
  intro omega a homega homega0 haD hf_orbit
  have homega1 : omega ≠ 1 := fun homega_one =>
    homega0 (homega_one ▸ Q0.one_mem)
  have homega_invQ : omega⁻¹ ∈ Q := Q.inv_mem homega
  have homega_inv1 : omega⁻¹ ≠ 1 := by simpa using homega1
  let z := f omega⁻¹
  have hzQ : z ∈ Q := (hf_mem omega⁻¹ homega_invQ homega_inv1).1
  have hz1 : z ≠ 1 := (hf_mem omega⁻¹ homega_invQ homega_inv1).2
  have hzQ0 : z ∉ Q0 := by
    intro hzQ0
    have homega_invQ0 : omega⁻¹ ∈ Q0 :=
      (claim_4_f_mem_Q0_iff H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
        htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
        hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
        omega⁻¹ homega_invQ homega_inv1).1 (by simpa [z] using hzQ0)
    exact homega0 (by simpa using Q0.inv_mem homega_invQ0)
  have hfz : f z = omega⁻¹ := by
    dsimp [z]
    exact PFchapter4section1.claim_H2 H Q D t f g h htwo_transitive
      hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
      hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega⁻¹ homega_invQ homega_inv1
  have hA_D : rightConjugateElem a t ∈ D :=
    PFchapter4section1.rightConjugateElem_mem_D ht_involution.inv_eq_self hD_eq haD
  have hp_fomega :
      f (f omega)⁻¹ = rightConjugateElem z (rightConjugateElem a t) := by
    calc
      f (f omega)⁻¹ = f (rightConjugateElem omega a)⁻¹ := by rw [hf_orbit]
      _ = f (rightConjugateElem omega⁻¹ a) := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem (f omega⁻¹) (rightConjugateElem a t) :=
        PFchapter4section1.claim_H3 H Q D t f g h htwo_transitive
          hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
          hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
          omega⁻¹ a homega_invQ homega_inv1 haD
      _ = rightConjugateElem z (rightConjugateElem a t) := rfl
  have hzinvQ : z⁻¹ ∈ Q := Q.inv_mem hzQ
  have hzinv1 : z⁻¹ ≠ 1 := by simpa using hz1
  have hp3 :
      f (f omega)⁻¹ = rightConjugateElem z⁻¹ (h z⁻¹)⁻¹ := by
    have hH5 := PFchapter4section1.claim_H5 H Q D t f g h htwo_transitive
      hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
      hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      z⁻¹ hzinvQ hzinv1
    simpa [hfz] using hH5
  have horbit_eq :
      rightConjugateElem z (rightConjugateElem a t) =
        rightConjugateElem z⁻¹ (h z⁻¹)⁻¹ := hp_fomega.symm.trans hp3
  have hback := congrArg (fun u : G => rightConjugateElem u (h z⁻¹)) horbit_eq
  have hzd :
      rightConjugateElem z (rightConjugateElem a t * h z⁻¹) = z⁻¹ := by
    simpa [rightConjugateElem, mul_assoc] using hback
  have hdD : rightConjugateElem a t * h z⁻¹ ∈ D :=
    D.mul_mem hA_D (hh_mem z⁻¹ hzinvQ hzinv1)
  exact claim_5_a_inversion_moves_D_orbit H D Q K V W Q0 S Q1 t s hsection3
    z (rightConjugateElem a t * h z⁻¹) hzQ hzQ0 hdD hzd

public theorem claim_5_a
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
      f omega = rightConjugateElem (omega * y) a → y ≠ 1 := by
  intro omega y a homega homega0 hy ha hfomega hy1
  have hf_orbit : f omega = rightConjugateElem omega a := by
    simpa [rightConjugateElem, hy1] using hfomega
  exact
    (claim_5_a_f_moves_D_orbit_obligation H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      omega a homega homega0 ha) hf_orbit

end PFchapter4section2
end CFSG.BenderSuzuki
