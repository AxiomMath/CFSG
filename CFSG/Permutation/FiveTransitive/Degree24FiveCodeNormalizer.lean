module

public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylowFixedPoints_eq_sylow_subgroup_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X)
    {p : ℕ}
    (S : Sylow p (fixingSubgroup P s)) :
    sylowFixedPoints X P s S =
      MulAction.fixedPoints S X := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let SP : Subgroup P := sylowImage X P s S
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  change F = MulAction.fixedPoints S X
  ext x
  rw [MulAction.mem_fixedPoints,
    MulAction.mem_fixedPoints]
  constructor
  · intro hx u
    let uH : H := u
    let uP : P := uH
    have huSP : uP ∈ SP :=
      Subgroup.mem_map_of_mem H.subtype u.prop
    let uN : N := ⟨uP, SP.le_normalizer huSP⟩
    let uSN : SN := ⟨uN, huSP⟩
    have hfix := hx uSN
    exact hfix
  · intro hx z
    obtain ⟨zH, hzS, hzEq⟩ :=
      Subgroup.mem_map.mp z.prop
    let zS : S := ⟨zH, hzS⟩
    have hfix :
        ((zH : H) : P) • x = x := by
      exact hx zS
    have hzEqP :
        ((zH : H) : P) = ((z : N) : P) :=
      hzEq
    rw [hzEqP] at hfix
    exact hfix

theorem sylow_five_card_twenty_five_local_normalizer_ge_three_hundred
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 25) :
    300 ≤
      Nat.card
        (Subgroup.normalizer
          (S : Set (fixingSubgroup P s))) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let N : Subgroup P := sylowNormalizer X P s S
  let SN : Subgroup N := sylowInNormalizer X P s S
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  let J : Subgroup (Equiv.Perm F) := ρ.range
  let NL : Subgroup H :=
    Subgroup.normalizer (S : Set H)
  change 300 ≤ Nat.card NL
  have hfixedSet :
      sylowFixedPoints X P s S =
        MulAction.fixedPoints S X :=
    sylowFixedPoints_eq_sylow_subgroup_fixedPoints
      X P s S
  have hFcard : Nat.card F = 9 := by
    change Nat.card (sylowFixedPoints X P s S) = 9
    rw [hfixedSet]
    exact
      sylow_five_card_twenty_five_fixedPoints_eq_nine
        X P hcard h5 hnotAlt s hs S hScard
  have hFtype : Fintype.card F = 9 := by
    rw [← Nat.card_eq_fintype_card]
    exact hFcard
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
  have hAlt :
      alternatingGroup F ≤
        (MulAction.toPermHom J F).range :=
    Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_nine
      J F hFtype hJ5
  have hAltDvdRange :
      Nat.card (alternatingGroup F) ∣
        Nat.card (MulAction.toPermHom J F).range :=
    Subgroup.card_dvd_of_le hAlt
  have hAltDvdJ :
      Nat.card (alternatingGroup F) ∣ Nat.card J :=
    hAltDvdRange.trans
      (Subgroup.card_range_dvd
        (MulAction.toPermHom J F))
  have hAltCard :
      Nat.card (alternatingGroup F) = 181440 := by
    letI : Nontrivial F :=
      Fintype.one_lt_card_iff_nontrivial.mp (by
        rw [hFtype]
        norm_num)
    rw [Nat.card_eq_fintype_card,
      card_alternatingGroup, hFtype]
    norm_num
  have hJlower : 181440 ≤ Nat.card J := by
    rw [← hAltCard]
    exact Nat.le_of_dvd Nat.card_pos hAltDvdJ
  have hbound :
      25 * Nat.card J ≤
        (Nat.card F).descFactorial 5 * Nat.card NL := by
    simpa only [H, N, SN, F, ρ, J, NL, hScard] using
      sylow_card_mul_fixed_action_card_le
        X P h5 s hs S
  rw [hFcard] at hbound
  norm_num [Nat.descFactorial] at hbound
  rw [Nat.card_eq_fintype_card] at hJlower ⊢
  omega

end FiveTransitive.Degree24

end CFSG
