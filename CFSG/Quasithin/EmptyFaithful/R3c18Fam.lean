module

public import CFSG.Quasithin.Background.A318PQuotes

public section

namespace CFSG.Quasithin

namespace R3c18

@[expose] def QLiePRankFam (F : ∀ (S : Type) [Group S], Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (X : Type) [Group X] [Finite X] (S : Subgroup X) [S.Normal],
    (∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) → IsSimpleGroup ↥S → F ↥S →
    1 < CFSG.Open.pRank p S → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 →
    ∀ x : X, (∃ k : ℕ, orderOf x = p ^ k) → x ∈ S

theorem qLiePRank_iff_fam :
    QLiePRank ↔ QLiePRankFam (fun S _ => LieTwoFamily S) := Iff.rfl

theorem qLiePRankFam_mono {F F' : ∀ (S : Type) [Group S], Prop}
    (h : ∀ (S : Type) [Group S], F' S → F S) (hF : QLiePRankFam F) : QLiePRankFam F' :=
  fun p hp hp5 X _ _ S _ hC hS hF' => hF p hp hp5 X S hC hS (h _ hF')

theorem qLiePRankFam_or {F F' : ∀ (S : Type) [Group S], Prop} (hF : QLiePRankFam F)
    (hF' : QLiePRankFam F') : QLiePRankFam (fun S _ => F S ∨ F' S) :=
  fun p hp hp5 X _ _ S _ hC hS hU =>
    hU.elim (fun h => hF p hp hp5 X S hC hS h) (fun h => hF' p hp hp5 X S hC hS h)

end R3c18

end CFSG.Quasithin
