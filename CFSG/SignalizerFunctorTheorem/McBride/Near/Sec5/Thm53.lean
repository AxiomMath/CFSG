module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Dichotomy
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxA11
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec5.Thm53AuxB4

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_thetaMG_not_mem_assoc
    (h : Counterexample p A θ) :
    ∃ Y ∈ dset p A θ, thetaMG p A θ Y ∉ assoc p A θ := by
  by_contra hcon
  push Not at hcon
  exact Thm53A.false_of_forall_thetaMG_mem h hcon

theorem dset_eq_singleton
    (h : Counterexample p A θ) : dset p A θ = {⊥} := by
  obtain ⟨hbot, hMG, hLG⟩ := Thm53B.bot_facts h h.exists_thetaMG_not_mem_assoc
  have hb : Thm53B.BotData p A θ := ⟨h.hyp.nearFunctor, hbot, hLG⟩
  obtain ⟨S, hS, hSsol, hSmax⟩ := Thm53A.exists_ssol h.hyp.nearFunctor h.hyp.card.ge
  have heq := Thm53B.theta1_eq hb h hS hSmax hMG
  exact Set.eq_singleton_iff_unique_mem.mpr
    ⟨hbot, fun Y hY => Thm53B.dset_subset_bot hb h.hyp.card hSsol heq hY⟩

theorem thetaMG_not_mem_assoc
    (h : Counterexample p A θ) : thetaMG p A θ ⊥ ∉ assoc p A θ :=
  (Thm53B.bot_facts h h.exists_thetaMG_not_mem_assoc).2.1

theorem sSup_mem_assoc_or_le (h : Counterexample p A θ) {S : Set (Subgroup G)}
    (hS : S ⊆ assoc p A θ) :
    (∀ Y ∈ assoc p A θ, Y ≤ sSup S) ∨ sSup S ∈ assoc p A θ := by
  have hrank : p ^ 2 ≤ Nat.card A := by
    rw [h.hyp.card]
    exact Nat.pow_le_pow_right h.hyp.prime.pos (by norm_num)
  rcases glauberman_dichotomy (P := NearASolvable p A) h.hyp.prime h.hyp.elemAbelian hrank
    h.hyp.isFunctor h.hyp.near
    (fun X Y hYX hAY hX => nearASolvable_of_le h.hyp.prime hX hYX hAY) h.notComplete
    (fun θ' hθ' hP' hlt => h.complete_of_size_lt
      ⟨h.hyp.prime, h.hyp.odd, h.hyp.elemAbelian, h.hyp.card, hθ', hP'⟩ hlt)
    (X := sSup S) ⟨S, hS, rfl⟩ with ⟨hle, _⟩ | ⟨hmem, _⟩
  · exact Or.inl hle
  · exact Or.inr hmem

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near
