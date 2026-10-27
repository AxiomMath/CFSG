module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 2(b)
-/

private theorem exists_involution_mem_H
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∃ s : G, s ∈ H ∧ IsInvolution s := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo_dvd_Q : 2 ∣ Nat.card Q := hA1.Q_even.two_dvd
  obtain ⟨sQ, hsQ_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Q) 2 htwo_dvd_Q
  let s : G := sQ
  have hs_order : orderOf s = 2 := by
    change orderOf (sQ : G) = 2
    rw [Subgroup.orderOf_coe, hsQ_order]
  have hs_pow_ne :=
    (orderOf_eq_prime_iff (x := s) (p := 2)).mp hs_order
  exact ⟨s, hA1.Q_le_H sQ.property, ⟨hs_pow_ne.2, hs_pow_ne.1⟩⟩

private theorem exists_rightConjugateElem_base_eq_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s₀ : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hs₀H : s₀ ∈ H) (hs₀ : IsInvolution s₀) :
    ∀ x : G, IsInvolution x → ∃ g : G, rightConjugateElem s₀ g = x := by
  classical
  intro x hx
  by_cases hxH : x ∈ H
  · have hs₀_ne_t : s₀ ≠ t := by
      intro h
      exact hA1.t_not_mem_H (h ▸ hs₀H)
    have hodd_s₀t : Odd (orderOf (s₀ * t)) :=
      proposition_2_a H D Q t hA1 s₀ t hs₀H hs₀ hA1.involution_t hA1.t_not_mem_H
    obtain ⟨a, _ha, ha⟩ :=
      exists_involution_conjugator_of_odd_product
        hs₀ hA1.involution_t hs₀_ne_t hodd_s₀t
    have hx_ne_t : x ≠ t := by
      intro h
      exact hA1.t_not_mem_H (h ▸ hxH)
    have hodd_xt : Odd (orderOf (x * t)) :=
      proposition_2_a H D Q t hA1 x t hxH hx hA1.involution_t hA1.t_not_mem_H
    obtain ⟨b, _hb, hb⟩ :=
      exists_involution_conjugator_of_odd_product
        hx hA1.involution_t hx_ne_t hodd_xt
    refine ⟨a * b⁻¹, ?_⟩
    calc
      rightConjugateElem s₀ (a * b⁻¹) =
          rightConjugateElem (rightConjugateElem s₀ a) b⁻¹ := by
        rw [rightConjugateElem_comp]
      _ = rightConjugateElem t b⁻¹ := by rw [ha]
      _ = rightConjugateElem (rightConjugateElem x b) b⁻¹ := by rw [hb]
      _ = rightConjugateElem x (b * b⁻¹) := by rw [rightConjugateElem_comp]
      _ = x := by simp [rightConjugateElem]
  · have hs₀_ne_x : s₀ ≠ x := by
      intro h
      exact hxH (h ▸ hs₀H)
    have hodd_s₀x : Odd (orderOf (s₀ * x)) :=
      proposition_2_a H D Q t hA1 s₀ x hs₀H hs₀ hx hxH
    obtain ⟨g, _hg, hg⟩ :=
      exists_involution_conjugator_of_odd_product hs₀ hx hs₀_ne_x hodd_s₀x
    exact ⟨g, hg⟩

public theorem proposition_2_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    ∀ x y : G, IsInvolution x → IsInvolution y →
      ∃ g : G, y = rightConjugateElem x g := by
  classical
  obtain ⟨s₀, hs₀H, hs₀⟩ := exists_involution_mem_H H D Q t hA1
  have hbase :=
    exists_rightConjugateElem_base_eq_involution H D Q t s₀ hA1 hs₀H hs₀
  intro x y hx hy
  obtain ⟨a, ha⟩ := hbase x hx
  obtain ⟨b, hb⟩ := hbase y hy
  refine ⟨a⁻¹ * b, ?_⟩
  calc
    y = rightConjugateElem s₀ b := hb.symm
    _ = rightConjugateElem s₀ (a * (a⁻¹ * b)) := by simp
    _ = rightConjugateElem (rightConjugateElem s₀ a) (a⁻¹ * b) := by
      rw [rightConjugateElem_comp]
    _ = rightConjugateElem x (a⁻¹ * b) := by rw [ha]

end PFchapter1section1
end CFSG.BenderSuzuki
