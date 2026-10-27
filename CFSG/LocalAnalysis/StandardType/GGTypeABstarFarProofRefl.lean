module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLinPerm

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Refl

variable {G : Type} [Group G] {Bs : Subgroup G} {p : ℕ}

theorem GGIsReflection.conj {φ : MulAut ↥Bs} (h : GGIsReflection p φ) (ψ : MulAut ↥Bs) :
    GGIsReflection p (ψ * φ * ψ⁻¹) := by
  refine ⟨by rw [conj_pow, h.1, mul_one, mul_inv_cancel], ?_⟩
  rw [← h.2]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquiv (ψ⁻¹ : MulAut ↥Bs).toEquiv fun b => ?_)
  show ψ (φ (ψ⁻¹ b)) = b ↔ φ (ψ⁻¹ b) = ψ⁻¹ b
  constructor
  · intro hb
    have h1 := congrArg (ψ⁻¹ : MulAut ↥Bs) hb
    rwa [MulAut.inv_apply_self] at h1
  · intro hb
    rw [hb, MulAut.apply_inv_self]

theorem ggIsReflection_swap_of_swap {α : Type*} [DecidableEq α]
    (E : Equiv.Perm α →* MulAut ↥Bs) {a b : α} (hab : a ≠ b)
    (h : GGIsReflection p (E (Equiv.swap a b))) {x y : α} (hxy : x ≠ y) :
    GGIsReflection p (E (Equiv.swap x y)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hxy)
  have hc' : E (Equiv.swap x y) = E c * E (Equiv.swap a b) * (E c)⁻¹ := by
    rw [← hc, map_mul, map_mul, map_inv]
  rw [hc']
  exact h.conj (E c)

theorem isSwap_of_ggIsReflection [Fact p.Prime] [Finite ↥Bs] (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) {α : Type*} [DecidableEq α] [Fintype α]
    (E : Equiv.Perm α →* MulAut ↥Bs) (hinj : Function.Injective E)
    (hsw : ∀ x y, x ≠ y → GGIsReflection p (E (Equiv.swap x y))) {π : Equiv.Perm α}
    (h : GGIsReflection p (E π)) : π.IsSwap := by
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let T : Equiv.Perm α →* (V ≃ₗ[ZMod p] V) := (ggLin (p := p) ι).comp E
  refine isSwap_of_isLinRefl hp2 T ((ggLin_injective (p := p) ι).comp hinj) ?_ ?_
  · intro x y hxy
    exact exists_of_ggIsReflection (p := p) ι (hsw x y hxy)
  · exact exists_of_ggIsReflection (p := p) ι h

end Refl

end CFSG.StandardType
