module

public import CFSG.Permutation.FiveTransitive.Degree67TwoSelectedOrbitKernel
public import CFSG.Permutation.FiveTransitive.Degree67TwoKernelBound

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoSevenBound
open MulAction NormalizerOrbitFamily

theorem card_le
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Fintype X]
    (hcard : Fintype.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (fixedPoints Q X) = 7)
    (horbit : ∀ x : X, Nat.card (orbit Q x) ≤ 4)
    (hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 33) :
    Nat.card Q ≤ 65536 := by
  classical
  have hsize : ∀ O : orbitRel.Quotient Q X,
      Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 := by
    intro O
    refine Quotient.inductionOn O ?_
    intro x
    rw [orbitRel.Quotient.orbit_mk]
    obtain ⟨e,he⟩ := hQ.card_orbit x
    have hb := horbit x
    have he2 : e ≤ 2 := by
      by_contra hn
      have hp : 8 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ e)
      omega
    rw [he]
    interval_cases e <;> norm_num
  have hcount := card_eq_one_two_four Q hsize
  rw [Nat.card_eq_fintype_card,hcard,hF] at hcount
  have hkernel : ∃ R : Subgroup Q, R.index ≤ 4096 ∧ ∃ s : Finset X,
      s.card = 23 ∧ ∀ r : R, ∀ x ∈ s, r • x = x := by
    by_cases hpair : 8 ≤ Nat.card (Family (X := X) Q 2)
    · let a : Fin 8 ↪ Family (X := X) Q 2 :=
        (Fin.castLEEmb hpair).trans (Finite.equivFin _).symm.toEmbedding
      exact Degree67TwoSelectedOrbitKernel.exists_kernel Q hQ hF 8 2 (Or.inl ⟨rfl,rfl⟩) a
    · have hquad : 4 ≤ Nat.card (Family (X := X) Q 4) := by omega
      let a : Fin 4 ↪ Family (X := X) Q 4 :=
        (Fin.castLEEmb hquad).trans (Finite.equivFin _).symm.toEmbedding
      exact Degree67TwoSelectedOrbitKernel.exists_kernel Q hQ hF 4 4 (Or.inr ⟨rfl,rfl⟩) a
  obtain ⟨R,hindex,s,hs,hfixed⟩ := hkernel
  have hRorbit (x : X) : Nat.card (orbit R x) ≤ 4 := by
    have hsub : orbit R x ⊆ orbit Q x := by
      intro y hy
      obtain ⟨r,hr⟩ := mem_orbit_iff.mp hy
      exact mem_orbit_iff.mpr ⟨r.val,hr⟩
    have hle := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hle
    exact hle.trans (horbit x)
  have hRbound (r : R) (hr : r ≠ 1) : Nat.card (fixedBy X r) ≤ 33 :=
    hbound r.val (fun he => hr (Subtype.ext he))
  have hR := Degree67TwoKernelBound.card_le_sixteen (hQ.to_subgroup R) hcard s hs
    hfixed hRorbit hRbound
  have hm := Nat.mul_le_mul hindex hR
  rw [R.index_mul_card] at hm
  exact hm

end FiveTransitive.Degree67TwoSevenBound

end CFSG
