module

public import CFSG.Permutation.FiveTransitive.A9SmallActionArithmetic
public import CFSG.Permutation.FiveTransitive.A9SmallActionJordan
public import CFSG.Permutation.FiveTransitive.SimpleIndexBound
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.A9SmallActionIndexCore
open MulAction

theorem one_or_nine_of_ne_fourteen
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (H : Subgroup (alternatingGroup F)) (hsmall : H.index ≤ 14) (hne14 : H.index ≠ 14) :
    H.index = 1 ∨ H.index = 9 := by
  classical
  let A := alternatingGroup F
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by omega)
  have hA : Nat.card A = 181440 := by
    rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  by_cases ht : H = ⊤
  · exact Or.inl (Subgroup.index_eq_one.mpr ht)
  have hb := SimpleIndexBound.card_le_factorial_index A H ht
  have hd := H.index_dvd_card
  rw [hA] at hb hd
  have hbad (hI : H.index = 10 ∨ H.index = 12) : False := by
    let Y := A ⧸ H
    let _ : Fintype Y := Fintype.ofFinite _
    have hcore : H.normalCore = ⊥ := by
      rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exact (ht (top_le_iff.mp (h ▸ H.normalCore_le))).elim
    let f := toPermHom A Y
    have hker : f.ker = ⊥ := H.normalCore_eq_ker.symm.trans hcore
    have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
    let J := f.range
    have hJ : Nat.card J = 181440 := (Nat.card_range_of_injective hi).trans hA
    let _ : IsPretransitive J Y := by
      constructor
      intro y z
      obtain ⟨g,hg⟩ := (inferInstance : IsPretransitive A Y).exists_smul_eq y z
      exact ⟨⟨f g,⟨g,rfl⟩⟩,hg⟩
    have hY : Nat.card Y = 10 ∨ Nat.card Y = 12 := by
      rw [← H.index_eq_card]
      exact hI
    exact A9SmallActionJordan.excluded J hY hJ
  rcases A9SmallActionArithmetic.index_cases H.index hsmall hd hb with h9 | h10 | h12 | h14
  · exact Or.inr h9
  · exact (hbad (Or.inl h10)).elim
  · exact (hbad (Or.inr h12)).elim
  · exact (hne14 h14).elim

end FiveTransitive.A9SmallActionIndexCore

end CFSG
