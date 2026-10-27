module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwoCav

theorem four_dvd_ggAutomizer_of_four_action {G : Type} [Group G] [Finite G]
    {J A : Subgroup G} {g d : G} (hgJ : g ∈ J)
    (hgN : g ∈ Subgroup.normalizer (A : Set G)) (hg4 : g ^ 4 = 1)
    (hd : d ∈ A) (hmove : g ^ 2 * d * (g ^ 2)⁻¹ ≠ d) :
    4 ∣ Nat.card (ggAutomizer J A) := by
  let a : ggAutomizer J A := ⟨ggConjAut A hgN, ggConjAut_mem_ggAutomizer hgJ hgN⟩
  have ha4 : a ^ 4 = 1 := by
    apply Subtype.ext
    ext b
    change (((ggConjAut A hgN ^ 4) b : A) : G) = b
    rw [ggConjAut_pow_apply, hg4]
    simp
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have he := congrArg (fun c : ggAutomizer J A => ((c.val ⟨d, hd⟩ : A) : G)) h
    change (((ggConjAut A hgN ^ 2) ⟨d, hd⟩ : A) : G) = d at he
    rw [ggConjAut_pow_apply] at he
    exact hmove he
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho : orderOf a = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1)
      (by simpa using ha2) (by simpa using ha4)
    simpa using h
  rw [← ho]
  exact orderOf_dvd_natCard a

end CFSG.StandardType.QTwoCav

end
