module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9LargeAlternatingQuotient

theorem not_surjective
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : 10 ≤ Nat.card E)
    (B : Subgroup (Equiv.Perm E)) (hAlt : alternatingGroup E ≤ B)
    (tau : B →* alternatingGroup F) : ¬ Function.Surjective tau := by
  classical
  intro htau
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup E) := alternatingGroup.isSimpleGroup (by omega)
  have hA : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hAE : 1814400 ≤ Nat.card (alternatingGroup E) := by
    rw [nat_card_alternatingGroup]
    have hh : (10 : ℕ).factorial / 2 ≤ (Nat.card E).factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le hE)
    norm_num only [Nat.factorial] at hh
    exact hh
  let f := tau.comp (Subgroup.inclusion hAlt)
  have htriv (g : alternatingGroup E) : f g = 1 := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
    · have hb := Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp h)
      rw [hA] at hb
      omega
    · have hg : g ∈ f.ker := by rw [h]; trivial
      exact hg
  let K := tau.ker.map B.subtype
  have hAK : alternatingGroup E ≤ K := by
    intro g hg
    exact ⟨⟨g,hAlt hg⟩,htriv ⟨g,hg⟩,rfl⟩
  have hl := Nat.le_of_dvd (Nat.card_pos (α := K)) (Subgroup.card_dvd_of_le hAK)
  rw [Subgroup.card_map_of_injective B.subtype_injective] at hl
  have hp := tau.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr htau,Subgroup.card_top,hA] at hp
  have hb := Nat.card_le_card_of_injective B.subtype B.subtype_injective
  have hsym := (alternatingGroup E).index_mul_card
  rw [alternatingGroup.index_eq_two] at hsym
  rw [← hsym] at hb
  omega

end FiveTransitive.A9LargeAlternatingQuotient

end CFSG
