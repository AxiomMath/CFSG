module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupAlmostSimple
public import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
public import CFSG.Adapters.WholeGroupLayer
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASIn

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Fstar)

theorem centralizer_eq_bot_of_fstar_top_eq {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (hF : Fstar (⊤ : Subgroup Q) = L) (hsimple : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) : Subgroup.centralizer (L : Set Q) = ⊥ := by
  rw [fstar_top_eq_generalizedFitting] at hF
  subst hF
  exact CFSG.Adapters.centralizer_generalizedFitting_eq_bot_of_isSimpleGroup Q hsimple hnab

theorem pow_succ_le_card_of_pow_lt {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    {A : Subgroup Q} {j : ℕ} (hA : IsPGroup p A) (h : p ^ j < Nat.card A) :
    p ^ (j + 1) ≤ Nat.card A := by
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn] at h ⊢
  have hp : p.Prime := Fact.out
  exact Nat.pow_le_pow_right hp.pos ((Nat.pow_lt_pow_iff_right hp.one_lt).mp h)

theorem inFGroup_of_genEi_sup_eq_top {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q} {j : ℕ}
    (hL : L.Normal) (hsimple : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hC : Subgroup.centralizer (L : Set Q) = ⊥) (hT : ∃ T : Subgroup Q, IsSylowIn 2 T ⊤ ∧ L ⊔ T = ⊤)
    (h : ∀ T : Subgroup Q, IsSylowIn 2 T ⊤ → ∀ Ω : Set (Subgroup Q), IsOmegaColl Ω →
      (∀ A ∈ Ω, A ≤ T → 2 ^ (j + 1) ≤ Nat.card A) → genEi j T Ω ⊔ T = ⊤) :
    InFGroup j Q := by
  obtain ⟨T, hTsyl, hLT⟩ := hT
  have has := almostSimple_of_normal_simple_sup_sylow hL hsimple hnab hC hTsyl hLT
  intro S hS Ω hΩ
  have hS' : IsSylowIn 2 S ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hS
  refine (inFOmega_iff_sup_eq_top j hΩ).mpr ?_
  by_cases hsmall : ∃ A ∈ Ω, A ≤ S ∧ Nat.card A ≤ 2 ^ j
  · obtain ⟨A, hAΩ, hAS, hcard⟩ := hsmall
    have hmq : E3.mQuot A (pCoreOf 2 (⊤ : Subgroup Q)) ≤ j :=
      mQuot_pCoreOf_top_le_of_card_le has (hΩ.elemAbelian A hAΩ).isPGroup hcard
    have hIn : InCalEi j S A ⊤ := inCalEi_top_of_almostSimple has hS' (hΩ.ne_bot A hAΩ) hmq
    have htop : genEi j S Ω = ⊤ :=
      le_antisymm le_top
        (le_iSup₂_of_le A hAΩ (le_iSup_of_le hAS (le_iSup₂_of_le ⊤ hIn le_rfl)))
    rw [htop, top_sup_eq]
  · simp only [not_exists, not_and, not_le] at hsmall
    exact h S hS' Ω hΩ fun A hAΩ hAS =>
      pow_succ_le_card_of_pow_lt (hΩ.elemAbelian A hAΩ).isPGroup (hsmall A hAΩ hAS)

end CFSG.LocalAnalysis.WeakClosure81
