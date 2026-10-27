module

public import CFSG.GroupTheory.KleinFourAutomorphism

public section

namespace CFSG.Quasithin.S153N.Bb

theorem fpf_of_moves {Vb : Type} [Group Vb] (hsq : ∀ v : Vb, v ^ 2 = 1) (Vbar : Subgroup Vb)
    (hcard : Nat.card ↥Vbar = 4) (ω : MulAut Vb) (hω3 : ∀ u : Vb, ω (ω (ω u)) = u)
    (hmem : ∀ u ∈ Vbar, ω u ∈ Vbar) (hmove : ∃ u ∈ Vbar, ω u ≠ u) :
    ∀ u ∈ Vbar, ω u = u → u = 1 := by
  have hsq' : ∀ x : ↥Vbar, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hsq (x : Vb))
  have hexp : Monoid.exponent ↥Vbar = 2 := by
    have hdvd : Monoid.exponent ↥Vbar ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one hsq'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exfalso
      have hsub : Subsingleton ↥Vbar := Monoid.exp_eq_one_iff.mp h1
      have := Nat.card_of_subsingleton (1 : ↥Vbar)
      omega
    · exact h2
  have : IsKleinFour ↥Vbar := ⟨hcard, hexp⟩
  obtain ⟨ω', hω'val⟩ : ∃ ω' : MulAut ↥Vbar, ∀ x : ↥Vbar, ((ω' x : ↥Vbar) : Vb) = ω x :=
    ⟨{ toFun := fun x => ⟨ω x, hmem x x.2⟩
       invFun := fun x => ⟨ω (ω x), hmem _ (hmem x x.2)⟩
       left_inv := fun x => Subtype.ext (hω3 x)
       right_inv := fun x => Subtype.ext (hω3 x)
       map_mul' := fun x y => Subtype.ext (map_mul ω (x : Vb) (y : Vb)) }, fun x => rfl⟩
  have hpow : ω' ^ 3 = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hω'val]
    exact hω3 x
  have hne1 : ω' ≠ 1 := by
    obtain ⟨u, hu, hmv⟩ := hmove
    intro h
    apply hmv
    have h1 := congrArg (fun f : MulAut ↥Vbar => ((f ⟨u, hu⟩ : ↥Vbar) : Vb)) h
    simpa [hω'val] using h1
  have horder : orderOf ω' = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hpow hne1
  intro u hu hωu
  by_contra hu1
  have hne : (⟨u, hu⟩ : ↥Vbar) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
  exact (CFSG.kleinFour_order_three_cycle ↥Vbar ω' horder ⟨u, hu⟩ hne).1
    (Subtype.ext (by rw [hω'val]; exact hωu))

end CFSG.Quasithin.S153N.Bb
