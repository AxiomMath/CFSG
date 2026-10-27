module

public import CFSG.Permutation.FiveTransitive.Degree79TwoProjection
public import CFSG.Permutation.FiveTransitive.Degree79TwoKernelFirstMoment

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoGeometryBound
open MulAction NormalizerOrbitFamily

private theorem eighteen_pairs_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (hc : 18 ≤ Nat.card (Family (X := X) Q 2))
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 39) : Nat.card Q ≤ 2 ^ 18 := by
  classical
  let a : Fin 18 ↪ Family (X := X) Q 2 :=
    (Fin.castLEEmb hc).trans (Finite.equivFin _).symm.toEmbedding
  obtain ⟨R,hindex,s,hs,hfix⟩ := Degree79TwoProjection.exists_kernel Q hQ hF
    18 2 (Or.inl ⟨rfl,rfl⟩) a
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

private theorem six_quads_card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hX : Fintype.card X = 79) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (hc : 6 ≤ Nat.card (Family (X := X) Q 4))
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 39) : Nat.card Q ≤ 2 ^ 22 := by
  classical
  let a : Fin 6 ↪ Family (X := X) Q 4 :=
    (Fin.castLEEmb hc).trans (Finite.equivFin _).symm.toEmbedding
  obtain ⟨R,hindex,s,hs,hfixed⟩ := Degree79TwoProjection.exists_kernel Q hQ hF
    6 4 (Or.inr ⟨rfl,rfl⟩) a
  have hRorbit (x : X) : Nat.card (orbit R x) ≤ 4 := by
    have hsub : orbit R x ⊆ orbit Q x := by
      intro y hy
      obtain ⟨r,hr⟩ := mem_orbit_iff.mp hy
      exact mem_orbit_iff.mpr ⟨r.val,hr⟩
    have hle := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hle
    exact hle.trans (horbit x)
  have hRbound (r : R) (hr : r ≠ 1) : Nat.card (fixedBy X r) ≤ 39 :=
    hbound r.val (fun he => hr (Subtype.ext he))
  have hR := Degree79TwoKernelFirstMoment.card_le_sixteen hX s hs hfixed hRorbit hRbound
  have hm := Nat.mul_le_mul hindex hR
  rw [R.index_mul_card] at hm
  exact hm

theorem card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hX : Fintype.card X = 79) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 5)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 39)
    (hgeometry : 18 ≤ Nat.card (Family (X := X) Q 2) ∨
      ((∀ x : X, Nat.card (orbit Q x) ≤ 4) ∧ 6 ≤ Nat.card (Family (X := X) Q 4))) :
    Nat.card Q ≤ 2 ^ 22 := by
  rcases hgeometry with hp | ⟨ho,hq⟩
  · exact (eighteen_pairs_card_le Q hQ hF hp hbound).trans (by decide)
  · exact six_quads_card_le hX Q hQ hF hq ho hbound

end FiveTransitive.Degree79TwoGeometryBound

end CFSG
