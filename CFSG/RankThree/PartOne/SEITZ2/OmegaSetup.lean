module

public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms
public import CFSG.RankThree.PartOne.CTP.SeitzMaxAbstract
public import CFSG.RankThree.PartOne.CTP.StrongPClassification

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Subgroup CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus)

structure OmegaSetup (K : Type) [Field K] (k : Subfield K) (σ : K ≃+* K) (p f₀ : ℕ) (b c : k) :
    Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  one_le : 1 ≤ f₀
  card_k : Nat.card k = 2 ^ f₀
  card_K : Nat.card K = 2 ^ (f₀ * p)
  order : orderOf σ = p
  fixed : ∀ x, x ∈ k ↔ σ x = x
  irr : ∀ s : k, s ^ 2 + b * s + c ≠ 0

namespace OmegaSetup

variable {K : Type} [Field K] {k : Subfield K} {σ : K ≃+* K} {p f₀ : ℕ} {b c : k}

theorem ne_two (h : OmegaSetup K k σ p f₀ b c) : p ≠ 2 := by
  have := h.five_le
  omega

theorem three_lt (h : OmegaSetup K k σ p f₀ b c) : 3 < p := by
  have := h.five_le
  omega

theorem card_K' (h : OmegaSetup K k σ p f₀ b c) : Nat.card K = 2 ^ (p * f₀) := by
  rw [h.card_K, mul_comm]

theorem charP [Finite K] (h : OmegaSetup K k σ p f₀ b c) : CharP K 2 :=
  charP_two_of_card h.card_K

theorem finrank [Finite K] (h : OmegaSetup K k σ p f₀ b c) : Module.finrank k K = p :=
  finrank_subfield_eq k Nat.prime_two h.one_le h.card_k h.card_K

theorem irr_K [Finite K] (h : OmegaSetup K k σ p f₀ b c) (s : K) :
    s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
  rootFree_of_odd_degree k h.prime h.ne_two h.finrank b c h.irr s

theorem fixed_of_orderOf (h : OmegaSetup K k σ p f₀ b c) {σ' : K ≃+* K} (hσ' : orderOf σ' = p) :
    ∀ x, x ∈ k ↔ σ' x = x := by
  have hf : 1 ≤ f₀ * p := Nat.mul_pos h.one_le h.prime.pos
  have hzp : Subgroup.zpowers σ = Subgroup.zpowers σ' :=
    zpowers_ringEquiv_eq_of_orderOf Nat.prime_two hf h.card_K h.order hσ'
  have key : ∀ {a a' : K ≃+* K}, Subgroup.zpowers a = Subgroup.zpowers a' →
      ∀ x, a x = x → a' x = x := by
    intro a a' haa' x hx
    have hb : a' ∈ Subgroup.zpowers a := haa' ▸ Subgroup.mem_zpowers a'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hstab : Subgroup.zpowers a ≤ MulAction.stabilizer (K ≃+* K) x :=
      (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx
    exact hstab (Subgroup.zpow_mem_zpowers a m)
  intro x
  rw [h.fixed x]
  exact ⟨key hzp x, key hzp.symm x⟩

theorem quad_invariant (h : OmegaSetup K k σ p f₀ b c) {n : ℕ} (hn : 1 ≤ n) {σ' : K ≃+* K}
    (hσ' : orderOf σ' = p) (v : Fin (2 * n) → K) :
    coordinateQuadMinus n K hn (b : K) (c : K) (coordinateFieldMap (2 * n) σ' v) =
      σ' (coordinateQuadMinus n K hn (b : K) (c : K) v) :=
  coordinateQuadMinus_fieldAut k n hn (h.fixed_of_orderOf hσ') b c v

end OmegaSetup

end CFSG.RankThree.PartOne.SEITZ2
