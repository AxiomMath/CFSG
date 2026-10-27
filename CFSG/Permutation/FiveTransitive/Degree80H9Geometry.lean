module

public import CFSG.Permutation.FiveTransitive.Degree80H9Preserved

public section

namespace CFSG

namespace FiveTransitive.Degree80H9Geometry
open MulAction

theorem nonpair_family_dvd_nine
    {G H X : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Fintype X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hX : Nat.card X = 80) (_hF : Nat.card (fixedPoints Q X) = 6)
    (i : H →* Subgroup.normalizer (Q : Set G))
    (hH : Nat.card H = 9) (hpow : ∀ h : H, h ^ 3 = 1)
    (E : Set X) (hE : E.ncard = 2)
    (hEout : ∀ x ∈ E, x ∉ fixedPoints Q X)
    (hEfix : ∀ h : H, ∀ x ∈ E, (i h).val • x = x)
    (hexact : ∀ h : H, h ≠ 1 → ∀ x : X,
      x ∉ fixedPoints Q X → ((i h).val • x = x ↔ x ∈ E)) :
    ∀ m ∈ ({4,8,16,32,64} : Finset ℕ),
      9 ∣ Nat.card (NormalizerOrbitFamily.Family (X := X) Q m) := by
  classical
  intro m hm
  have hm1 : m ≠ 1 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega
  have hm2 : m ≠ 2 := by simp only [Finset.mem_insert,Finset.mem_singleton] at hm; omega
  let B := NormalizerOrbitFamily.Family (X := X) Q m
  let rho := (NormalizerOrbitFamily.toPermHom (X := X) Q m).comp i
  let _ : MulAction H B := MulAction.compHom _ rho
  have hcount (h : H) (hh : h ≠ 1) : Nat.card (fixedBy B h) = 0 := by
    let _ : IsEmpty (fixedBy B h) := ⟨by
      intro O
      have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q (i h) O.val.val = O.val.val :=
        congrArg Subtype.val O.property
      have he := Degree80H9Preserved.preserved_card_eq_two Q hQ hX i hH hpow E hE
        hEout hEfix hexact O.val.val (by rw [O.val.property]; exact hm1) h hh hpres
      exact hm2 (O.val.property.symm.trans he)⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
  have hd := OrderNineFixedCount.constant_divisibility (Y := B) hH 0 hcount
  simpa only [Nat.mul_zero,Nat.add_zero] using hd

end FiveTransitive.Degree80H9Geometry

end CFSG
