module

public import CFSG.Permutation.FiveTransitive.PrimeSupportConstraints
public import CFSG.Permutation.FiveTransitive.SupportEightInvolutionClosure

public section

namespace CFSG

namespace FiveTransitive.HighDegreeMinimalSupport

open Equiv

theorem nine_le_support
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Perm X)) (hn : 28 ≤ Fintype.card X)
    (h5 : MulAction.IsMultiplyPretransitive P X 5)
    (hnotAlt : ¬ alternatingGroup X ≤ P)
    {g : Perm X} (hg : g ∈ P) (hne : g ≠ 1) : 9 ≤ g.support.card := by
  letI : MulAction.IsMultiplyPretransitive P X 5 := h5
  have h4 : MulAction.IsMultiplyPretransitive P X 4 :=
    MulAction.isMultiplyPretransitive_of_le (G := P) (α := X) (m := 4) (n := 5)
      (by omega) (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := (MulAction.isMultiplyPretransitive_iff.mp h5)
      (⟨a, ha⟩ : Fin 5 ↪ X) (⟨b, hb⟩ : Fin 5 ↪ X)
    exact ⟨q, fun i => DFunLike.congr_fun hq i⟩
  by_contra hsmall
  by_cases heq : g.support.card = 8
  · exact hnotAlt (SupportEightInvolutionClosure.alternatingGroup_le_of_support_card_eight
      P hn h4 hg heq)
  · exact hnotAlt (PrimeSupportConstraints.alternatingGroup_le_of_nontrivial_support_le_seven
      P (by omega) hexp hg hne (by omega))

end FiveTransitive.HighDegreeMinimalSupport

end CFSG
