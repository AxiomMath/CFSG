module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Counterexample
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Defs
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Minimal
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.ClassHypB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

theorem hypB_mono {G : Type u} [Group G] [Finite G] {p : ℕ} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hX : signalizerMcBrideHypothesisB p X) : signalizerMcBrideHypothesisB p Y :=
  (isSigClass_hypBClass.{u} p).mono G hYX (A := ⊥) (by simp) hX

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem prime (h : Counterexample p A θ) : p.Prime := h.hyp.prime

theorem odd (h : Counterexample p A θ) : p ≠ 2 := h.hyp.odd

theorem elemAbelian (h : Counterexample p A θ) : IsElemAbelian p A := h.hyp.elemAbelian

theorem card (h : Counterexample p A θ) : Nat.card A = p ^ 3 := h.hyp.card

theorem isFunctor (h : Counterexample p A θ) : IsFunctor p A θ := h.hyp.isFunctor

theorem hypC (h : Counterexample p A θ) :
    ∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (θ a) := h.hyp.hypC

theorem rank_two_le (h : Counterexample p A θ) : p ^ 2 ≤ Nat.card A := by
  rw [h.card]
  exact Nat.pow_le_pow_right h.prime.pos (by norm_num)

theorem rank_three_le (h : Counterexample p A θ) : p ^ 3 ≤ Nat.card A := h.card.ge

theorem completeBelow (h : Counterexample p A θ) :
    CompleteBelow p (hypBClass.{u} p) (Nat.card G) (Nat.card A) := by
  intro H _ _ hH A' θ' hA' hcard hθ' hC'
  exact h.ih H hH A' θ' ⟨h.prime, h.odd, hA', hcard.trans h.card, hθ', hC'⟩

theorem hmin (h : Counterexample p A θ) :
    ∀ θ' : G → Subgroup G, IsFunctor p A θ' →
      (∀ a ∈ A, a ≠ 1 → signalizerMcBrideHypothesisB p (θ' a)) → size A θ' < size A θ →
        IsCompleteIn (signalizers p A θ' (signalizerMcBrideHypothesisB p)) :=
  fun _ hθ' hC' hlt => h.complete_of_size_lt ⟨h.prime, h.odd, h.elemAbelian, h.card, hθ', hC'⟩ hlt

theorem noNormalMember (h : Counterexample p A θ) {N : Subgroup G} [N.Normal]
    (hN : N ∈ Msig p A θ) : N = ⊥ :=
  eq_bot_of_normal_of_incomplete (Cl := hypBClass.{u} p) h.prime (isSigClass_hypBClass p)
    h.elemAbelian h.isFunctor h.hypC h.completeBelow h.notComplete hN

theorem locallyComplete (h : Counterexample p A θ) : IsLocallyCompleteIn (Msig p A θ) :=
  isLocallyCompleteIn_of_incomplete (Cl := hypBClass.{u} p) h.prime (isSigClass_hypBClass p)
    h.elemAbelian h.isFunctor h.hypC h.completeBelow h.notComplete

theorem generation (h : Counterexample p A θ) : sSup (Msig p A θ) ⊔ A = ⊤ :=
  sSup_signalizers_sup_eq_top (Cl := hypBClass.{u} p) h.prime (isSigClass_hypBClass p)
    h.elemAbelian h.isFunctor h.hypC h.completeBelow h.notComplete

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
