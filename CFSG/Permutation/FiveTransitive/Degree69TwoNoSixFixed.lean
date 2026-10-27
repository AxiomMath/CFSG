module

public import CFSG.Permutation.FiveTransitive.Degree69TwoMaximal
public import CFSG.Permutation.FiveTransitive.MaximalOrderFixedLowerBound

public section

namespace CFSG

namespace FiveTransitive.Degree69TwoNoSixFixed
open MulAction Subgroup FixedNormalizerAction

theorem eq_bot_of_six_fixed
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hfix : 6 ≤ Nat.card (fixedPoints Q X)) : Q = ⊥ := by
  classical
  by_contra hne
  obtain ⟨U,hU,hUfix,hQU,hmax⟩ := MaximalOrderFixedLowerBound.exists_maximal 2 6 Q hQ hfix
  have hUcard : 1 < Nat.card U :=
    (Finite.one_lt_card_iff_nontrivial.mpr (Q.nontrivial_iff_ne_bot.mpr hne)).trans_le hQU
  have hUne : U ≠ ⊥ := by intro he; rw [he] at hUcard; simp at hUcard
  let _ : Fintype (Fixed (X := X) U) := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree69TwoMaximal.alternating_normalizer P hcard h5 hnotAlt U hU hUne hUfix hmax
  let F := Fixed (X := X) U
  change 7 ≤ Nat.card F at hF
  let N := Normalizer U
  let rho := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7)
      (by decide) (by rw [← Nat.card_eq_fintype_card]; exact (by omega))).trans
        (Subgroup.card_dvd_of_le hAlt)
  exact Degree69SevenFree.not_dvd_ambient P hcard h5 hnotAlt
    ((hd.trans (Subgroup.card_range_dvd rho)).trans (Subgroup.card_subgroup_dvd_card N))

end FiveTransitive.Degree69TwoNoSixFixed

end CFSG
