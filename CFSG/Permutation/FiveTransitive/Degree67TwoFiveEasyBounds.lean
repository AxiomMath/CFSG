module

public import CFSG.Permutation.FiveTransitive.Degree67TwoFivePairBound
public import CFSG.Permutation.FiveTransitive.Degree67TwoFiveSelectedKernel

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveEasyBounds
open MulAction NormalizerOrbitFamily

theorem pairs_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hX : Fintype.card X = 67) (Q : Subgroup G)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 2)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) : Nat.card Q ≤ 11 := by
  classical
  let s := (fixedPoints Q X).toFinset
  have hs : s.card = 5 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card]
    exact hF
  have hb := Degree67TwoFivePairBound.card_inequality hX s
    (fun q x hx => (Set.mem_toFinset.mp hx) q) horbit hbound
  rw [hs] at hb
  omega

theorem fifteen_pairs_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (hc : Nat.card (Family (X := X) Q 2) = 15)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) : Nat.card Q ≤ 32768 := by
  classical
  let a : Fin 15 ≃ Family (X := X) Q 2 := (Finite.equivFinOfCardEq hc).symm
  obtain ⟨R,hindex,s,hs,hfix,_⟩ := Degree67TwoFiveSelectedKernel.exists_kernel Q hQ hF
    15 2 (Or.inl ⟨rfl,rfl⟩) a
  have hR : R = ⊥ := by
    apply le_antisymm
    · intro q hq
      change q = 1
      by_contra hn
      have hb := hbound q hn
      have hsub : (s : Set X) ⊆ fixedBy X q := fun x hx => hfix ⟨q,hq⟩ x hx
      have hl := Set.ncard_le_ncard hsub
      rw [Set.ncard_coe_finset,← Nat.card_coe_set_eq] at hl
      omega
    · exact bot_le
  have he := R.card_mul_index
  have hcR : Nat.card R = 1 := by rw [hR,Subgroup.card_bot]
  rw [hcR] at he
  omega

theorem five_quads_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hX : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (hc : Nat.card (Family (X := X) Q 4) = 5)
    (horbit : ∀ x : X, Nat.card (orbit Q x) = 1 ∨ Nat.card (orbit Q x) = 2 ∨
      Nat.card (orbit Q x) = 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) : Nat.card Q ≤ 65536 := by
  classical
  let a : Fin 5 ≃ Family (X := X) Q 4 := (Finite.equivFinOfCardEq hc).symm
  obtain ⟨R,hindex,s,hs,hfix,hfixquad⟩ := Degree67TwoFiveSelectedKernel.exists_kernel Q hQ hF
    5 4 (Or.inr ⟨rfl,rfl⟩) a
  have hRorbit (x : X) : Nat.card (orbit R x) ≤ 2 := by
    rcases horbit x with h1 | h2 | h4
    · have hsub : orbit R x ⊆ orbit Q x := by
        rintro y ⟨r,rfl⟩
        exact ⟨r.val,rfl⟩
      have hb := Set.ncard_le_ncard hsub
      rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,h1] at hb
      omega
    · have hsub : orbit R x ⊆ orbit Q x := by
        rintro y ⟨r,rfl⟩
        exact ⟨r.val,rfl⟩
      have hb := Set.ncard_le_ncard hsub
      rwa [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,h2] at hb
    · have he : orbit R x = {x} := by
        ext y
        constructor
        · rintro ⟨r,rfl⟩
          exact hfixquad x h4 r
        · rintro rfl
          exact mem_orbit_self _
      rw [he,Nat.card_coe_set_eq,Set.ncard_singleton]
      omega
  have hRbound (r : R) (hr : r ≠ 1) : Nat.card (fixedBy X r) ≤ 33 := by
    exact hbound r.val (fun he => hr (Subtype.ext he))
  have hb := Degree67TwoFivePairBound.card_inequality hX s hfix hRorbit hRbound
  rw [hs] at hb
  have hcR : Nat.card R ≤ 2 := by omega
  have he := R.card_mul_index
  have hm := Nat.mul_le_mul hcR hindex
  rw [he] at hm
  exact hm

end FiveTransitive.Degree67TwoFiveEasyBounds

end CFSG
