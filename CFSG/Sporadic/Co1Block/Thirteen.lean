module

public import CFSG.Sporadic.Co1Block.TwoANode
public import CFSG.Sporadic.Co1Block.TwoCNode
public import CFSG.Sporadic.Co1Block.TwoBComp

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier Subgroup

@[expose] def centralizerMulEquiv {H K : Type*} [Group H] [Group K] (f : H ≃* K) (x : H) :
    centralizer ({x} : Set H) ≃* centralizer ({f x} : Set K) where
  toFun c := ⟨f c, by
    rw [mem_centralizer_singleton_iff]
    have h := c.2
    rw [mem_centralizer_singleton_iff] at h
    rw [← map_mul, ← map_mul, h]⟩
  invFun c := ⟨f.symm c, by
    rw [mem_centralizer_singleton_iff]
    have h := c.2
    rw [mem_centralizer_singleton_iff] at h
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]⟩
  left_inv c := Subtype.ext (f.symm_apply_apply _)
  right_inv c := Subtype.ext (f.apply_symm_apply _)
  map_mul' a b := Subtype.ext (map_mul f _ _)

@[expose] def mulEquivOfFun {H K : Type*} [Group H] [Group K] (φ : H → K) (ψ : K → H)
    (h₁ : ∀ x, ψ (φ x) = x) (h₂ : ∀ y, φ (ψ y) = y) (hmul : ∀ a b, φ (a * b) = φ a * φ b) :
    H ≃* K where
  toFun := φ
  invFun := ψ
  left_inv := h₁
  right_inv := h₂
  map_mul' := hmul

theorem forall_card_quotient_center_of_point {H K : Type*} [Group H] [Group K] (f : H ≃* K)
    (t : H) {n : ℕ} (h : ∀ B : Subgroup (centralizer ({f t} : Set K)), CFSG.IsComponent B →
      Nat.card (B ⧸ center B) = n) :
    ∀ B : Subgroup (centralizer ({t} : Set H)), CFSG.IsComponent B →
      Nat.card (B ⧸ center B) = n :=
  forall_card_quotient_center_of_mulEquiv (centralizerMulEquiv f t).symm h

theorem ncard_fix_cases
    {s : GA} (hs : orderOf s = 2) :
    (xFix (s : GL24)).ncard = 2280 ∨ (xFix (s : GL24)).ncard = 264 ∨
      (xFix (s : GL24)).ncard = 0 := by
  rcases involution_classes.1 s hs with h | h | h
  · left
    rw [← ncard_fix_isConj h, ncard_fix_aC]
  · right
    left
    rw [← ncard_fix_isConj h, ncard_fix_cC]
  · right
    right
    rw [← ncard_fix_isConj h, ncard_fix_a₁]

theorem card_quotient_center_GA
    {s : GA} (hs : orderOf s = 2)
    (B : Subgroup (centralizer ({s} : Set GA))) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ center B) = 251596800 := by
  rcases ncard_fix_cases hs with h | h | h
  · obtain ⟨-, -, -, -, hno⟩ := cti_co1_2280_fixed_point_centralizer_has_no_components hs h
    exact absurd hB (hno B)
  · obtain ⟨-, -, -, -, -, hno⟩ := cti_co1_264_fixed_point_centralizer_has_no_components hs h
    exact absurd hB (hno B)
  · exact forall_card_quotient_center_of_isConj (isConj_a₁_of_ncard_fix hs h).symm
      card_quotient_center_a₁ B hB

theorem cti_co1_involution_local_components_simple_quotient_divisible_by_thirteen
    {S : Type*}
    [Group S] (hS : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Co1)) {t : S}
    (ht : orderOf t = 2) (B : Subgroup (centralizer ({t} : Set S))) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ center B) = 251596800 ∧ 13 ∣ Nat.card (B ⧸ center B) := by
  obtain ⟨e⟩ := hS
  let f := mulEquivOfFun (H := S) (K := GA) (fun s => co1MatEquiv (e s))
    (fun g => e.symm (co1MatEquiv.symm g)) (fun s => by simp only [MulEquiv.symm_apply_apply])
    (fun g => by simp only [MulEquiv.apply_symm_apply]) (fun a b => by rw [map_mul, map_mul])
  have het : orderOf (e t) = orderOf t := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow, ← map_one e, e.injective.eq_iff]
  have hft : orderOf (f t) = 2 := by
    show orderOf (co1MatEquiv (e t)) = 2
    rw [orderOf_co1MatEquiv, het, ht]
  have h := forall_card_quotient_center_of_point f t (card_quotient_center_GA hft) B hB
  exact ⟨h, by rw [h]; norm_num⟩

end CFSG.Sporadic.Co1Block
