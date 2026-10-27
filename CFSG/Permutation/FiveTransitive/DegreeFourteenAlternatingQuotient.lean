module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.DegreeFourteenAlternatingQuotient

theorem not_surjective
    {E F : Type*} [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    (hE : Nat.card E = 14) (hF : Nat.card F = 9)
    (B : Subgroup (Equiv.Perm E)) (hAlt : alternatingGroup E ≤ B)
    (tau : B →* alternatingGroup F) : ¬ Function.Surjective tau := by
  classical
  intro hsur
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup E) := alternatingGroup.isSimpleGroup (by omega)
  have hAE : Nat.card (alternatingGroup E) = 43589145600 := by
    rw [nat_card_alternatingGroup,hE]; norm_num [Nat.factorial]
  have hAF : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  let psi : alternatingGroup E →* alternatingGroup F := tau.comp (Subgroup.inclusion hAlt)
  have hk : psi.ker = ⊤ := by
    rcases (inferInstance : psi.ker.Normal).eq_bot_or_eq_top with h | h
    · have hi : Function.Injective psi := (MonoidHom.ker_eq_bot_iff psi).mp h
      have hb := Nat.card_le_card_of_injective psi hi
      rw [hAE,hAF] at hb
      omega
    · exact h
  let j : alternatingGroup E → tau.ker := fun g =>
    ⟨⟨g.val,hAlt g.property⟩,show psi g = 1 from by
      have hg : g ∈ psi.ker := by rw [hk]; trivial
      exact hg⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : tau.ker => z.val.val) h)
  have hker := Nat.card_le_card_of_injective j hj
  rw [hAE] at hker
  have hm := tau.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hsur,Subgroup.card_top,hAF] at hm
  have hb := Nat.card_le_card_of_injective B.subtype B.subtype_injective
  rw [Nat.card_perm,hE] at hb
  norm_num only [Nat.factorial] at hb
  omega

end FiveTransitive.DegreeFourteenAlternatingQuotient

end CFSG
