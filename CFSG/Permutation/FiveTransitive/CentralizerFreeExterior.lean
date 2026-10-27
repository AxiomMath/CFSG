module

public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount

public section

namespace CFSG

namespace FiveTransitive.CentralizerFreeExterior
open MulAction

theorem card_dvd_complement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q A : Subgroup G) (k : ℕ)
    (hcomm : ∀ a : A, ∀ q : Q, a.val * q.val = q.val * a.val)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → k < Nat.card (orbit Q x))
    (hfix : ∀ a : A, a ≠ 1 → Nat.card (fixedBy X a.val) ≤ k) :
    Nat.card A ∣ Nat.card X - Nat.card (fixedPoints Q X) := by
  classical
  have hstable : ∀ (a : A) (x : X), x ∈ fixedPoints Q X → a • x ∈ fixedPoints Q X := by
    intro a x hx q
    change q.val • (a.val • x) = a.val • x
    rw [← mul_smul,← hcomm a q,mul_smul]
    exact congrArg (fun y => a.val • y) (hx q)
  let Y := FreeComplementOrbitCount.complement A (fixedPoints Q X) hstable
  have hfree : ∀ (a : A) (y : Y), a • y = y → a = 1 := by
    intro a y hay
    by_contra hne
    have hy : a.val • y.val = y.val := congrArg Subtype.val hay
    let f : orbit Q y.val → fixedBy X a.val := fun z => ⟨z.val,by
      obtain ⟨q,hq⟩ := mem_orbit_iff.mp z.property
      rw [← hq]
      change a.val • (q.val • y.val) = q.val • y.val
      rw [← mul_smul,hcomm a q,mul_smul,hy]⟩
    have hf : Function.Injective f := fun u v h => Subtype.ext (congrArg (fun z : fixedBy X a.val => z.val) h)
    have hb := Nat.card_le_card_of_injective f hf
    have hl := horbit y.val y.property
    have hu := hfix a hne
    omega
  have he := FreeComplementOrbitCount.card_eq_mul_orbits hfree
  have hc : Nat.card Y = Nat.card X - Nat.card (fixedPoints Q X) := by
    rw [FreeComplementOrbitCount.card_complement,← Nat.card_coe_set_eq]
  rw [hc] at he
  exact ⟨_,he⟩

end FiveTransitive.CentralizerFreeExterior

end CFSG
