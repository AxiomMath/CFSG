module

public import CFSG.Sporadic.J2
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem j2AutCore_card_center {J : Type} [Group J] [Finite J]
    (hJ : IsSpor J .J2) : Nat.card J = 604800 ∧ center J = ⊥ := by
  obtain ⟨eJ⟩ := id hJ
  have hcardJ : Nat.card J = 604800 := by
    rw [Nat.card_congr eJ.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  refine ⟨hcardJ, ?_⟩
  have : IsSimpleGroup J := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 eJ
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J)).resolve_right fun ht => ?_
  have hprime : (Nat.card J).Prime :=
    (@Group.is_simple_iff_prime_card J _ (center_eq_top_iff.1 ht)).1 inferInstance
  rw [hcardJ] at hprime
  norm_num at hprime

theorem mulAut_mul_conj_mul_inv {J : Type} [Group J] (s : MulAut J) (y : J) :
    s * MulAut.conj y * s⁻¹ = MulAut.conj (s y) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem mulAut_conj_injective_of_center_eq_bot {J : Type} [Group J] (h : center J = ⊥) :
    Function.Injective (MulAut.conj : J →* MulAut J) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hc : a ∈ center J := by
    rw [mem_center_iff]
    intro g
    have := congrArg (fun σ : MulAut J => σ g) ha
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * a = a * g * a⁻¹ * a := by rw [this]
      _ = a * g := by group
  rw [h, mem_bot] at hc
  exact hc

theorem exists_orderOf_eq_two_of_isPGroup {G : Type} [Group G] [Finite G] (hG : IsPGroup 2 G)
    [Nontrivial G] : ∃ g : G, orderOf g = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hG.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card G ≠ 1 := Finite.one_lt_card.ne'
    exact this (by simpa using hn)
  exact exists_prime_orderOf_dvd_card' 2 (hn ▸ dvd_pow_self 2 hn0)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
