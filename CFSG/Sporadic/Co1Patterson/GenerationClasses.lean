module

public import CFSG.Sporadic.Co1Block.TwoACent
public import CFSG.Sporadic.Co1Block.TwoCCent
public import CFSG.Sporadic.Co1Block.TwoBCentBase2

public section

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier
open CFSG.Blueprint (NativeSporadic.Co1)

theorem card_eq_of_mulEquiv_co1 {Y : Type*} [Group Y]
    (e : Y ≃* NativeSporadic.Co1) : Nat.card Y = 4157776806543360000 := by
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Co1.card_Co1]

theorem exists_involution_classes_of_mulEquiv {Y G₀ : Type*} [Group Y] [Group G₀]
    (ψ : Y ≃* G₀) {a b c : G₀} {nA nB nC : ℕ}
    (hcls : ∀ s : G₀, orderOf s = 2 → IsConj s a ∨ IsConj s b ∨ IsConj s c)
    (hab : ¬ IsConj a b) (hac : ¬ IsConj a c) (hbc : ¬ IsConj b c)
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hc : orderOf c = 2)
    (hCa : Nat.card (centralizer ({a} : Set G₀)) = nA)
    (hCb : Nat.card (centralizer ({b} : Set G₀)) = nB)
    (hCc : Nat.card (centralizer ({c} : Set G₀)) = nC) :
    ∃ a b c : Y, (∀ y : Y, orderOf y = 2 → IsConj a y ∨ IsConj b y ∨ IsConj c y) ∧
      ¬ IsConj a b ∧ ¬ IsConj a c ∧ ¬ IsConj b c ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 2 ∧
      Nat.card (centralizer ({a} : Set Y)) = nA ∧
      Nat.card (centralizer ({b} : Set Y)) = nB ∧
      Nat.card (centralizer ({c} : Set Y)) = nC := by
  have hpull : ∀ {r s : G₀}, IsConj r s → IsConj (ψ.symm r) (ψ.symm s) := fun h => by
    obtain ⟨g, rfl⟩ := isConj_iff.mp h
    exact isConj_iff.mpr ⟨ψ.symm g, by rw [map_mul, map_mul, map_inv]⟩
  have hpush : ∀ {r s : G₀}, IsConj (ψ.symm r) (ψ.symm s) → IsConj r s := fun h => by
    obtain ⟨g, hg⟩ := isConj_iff.mp h
    refine isConj_iff.mpr ⟨ψ g, ?_⟩
    have := congrArg ψ hg
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      at this
  have hcard : ∀ r : G₀, Nat.card (centralizer ({ψ.symm r} : Set Y)) =
      Nat.card (centralizer ({r} : Set G₀)) := fun r => by
    rw [card_centralizer_equiv ψ, MulEquiv.apply_symm_apply]
  refine ⟨ψ.symm a, ψ.symm b, ψ.symm c, fun y hy => ?_, fun h => hab (hpush h),
    fun h => hac (hpush h), fun h => hbc (hpush h), by rw [MulEquiv.orderOf_eq, ha],
    by rw [MulEquiv.orderOf_eq, hb], by rw [MulEquiv.orderOf_eq, hc], (hcard a).trans hCa,
    (hcard b).trans hCb, (hcard c).trans hCc⟩
  have h2 : orderOf (ψ y) = 2 := by rw [MulEquiv.orderOf_eq]; exact hy
  have hy' : ∀ r : G₀, IsConj (ψ y) r → IsConj (ψ.symm r) y := fun r h => by
    have := hpull h
    rw [MulEquiv.symm_apply_apply] at this
    exact this.symm
  rcases hcls (ψ y) h2 with h | h | h
  · exact Or.inl (hy' _ h)
  · exact Or.inr (Or.inl (hy' _ h))
  · exact Or.inr (Or.inr (hy' _ h))

theorem exists_involution_classes
    {Y : Type*} [Group Y] (e : Y ≃* NativeSporadic.Co1) :
    ∃ a b c : Y, (∀ y : Y, orderOf y = 2 → IsConj a y ∨ IsConj b y ∨ IsConj c y) ∧
      ¬ IsConj a b ∧ ¬ IsConj a c ∧ ¬ IsConj b c ∧
      orderOf a = 2 ∧ orderOf b = 2 ∧ orderOf c = 2 ∧
      Nat.card (centralizer ({a} : Set Y)) = 89181388800 ∧
      Nat.card (centralizer ({b} : Set Y)) = 2012774400 ∧
      Nat.card (centralizer ({c} : Set Y)) = 389283840 := by
  obtain ⟨hcls, hac, ha1, hc1⟩ := involution_classes
  have hCa : Nat.card (centralizer ({aC} : Set GA)) = 89181388800 := by
    rw [card_centralizer_GA, coe_aC]
    exact card_cent_aG
  have hCc : Nat.card (centralizer ({cC} : Set GA)) = 389283840 := by
    rw [card_centralizer_GA, coe_cC]
    exact card_cent_cG
  have hcls' : ∀ s : GA, orderOf s = 2 → IsConj s aC ∨ IsConj s a₁ ∨ IsConj s cC := by
    intro s hs
    rcases hcls s hs with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  exact @exists_involution_classes_of_mulEquiv Y GA _ (inferInstance : Group GA)
    (e.trans co1MatEquiv) aC a₁ cC _ _ _ hcls' ha1 hac (fun h => hc1 h.symm) orderOf_aC
    orderOf_a₁ orderOf_cC hCa card_cent_a₁ hCc

end CFSG.Sporadic.Co1Patterson
