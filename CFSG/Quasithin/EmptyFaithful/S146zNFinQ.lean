module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinP
public import CFSG.Quasithin.EmptyFaithful.S143A6Nat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

@[expose] def IsT (g : A6) : Prop := g ^ 3 = 1 ∧ g ≠ 1 ∧ ∃ i, g.1 i = i

@[expose] def IsU (g : A6) : Prop := g ^ 3 = 1 ∧ g ≠ 1 ∧ ∀ i, g.1 i ≠ i

theorem a_fix : ∃ i, a.1 i = i := by
  refine ⟨3, ?_⟩
  show aP 3 = 3
  unfold aP
  decide

theorem aa'_nofix : ∀ i, (a * a').1 i ≠ i := by
  intro i
  show (aP * a'P) i ≠ i
  unfold aP a'P
  revert i
  decide

theorem fix_conj (k g : A6) (i : Fin 6) (h : g.1 i = i) : (k * g * k⁻¹).1 (k.1 i) = k.1 i := by
  show (k.1 * g.1 * k.1⁻¹) (k.1 i) = k.1 i
  simp [Perm.mul_apply, h]

theorem nofix_conj (k g : A6) (h : ∀ i, g.1 i ≠ i) : ∀ i, (k * g * k⁻¹).1 i ≠ i := by
  intro i hi
  apply h (k.1⁻¹ i)
  have h2 : k.1 (g.1 (k.1⁻¹ i)) = i := hi
  apply k.1.injective
  rw [h2]
  simp

theorem IsT.conj_a {g : A6} (hg : IsT g) : ∃ k : A6, k * a * k⁻¹ = g := by
  obtain ⟨h3, h1, ⟨i, hi⟩⟩ := hg
  rcases exists_conj_a_or_b g h3 h1 with h | ⟨k, hk⟩
  · exact h
  · exfalso
    subst hk
    exact nofix_conj k (a * a') aa'_nofix i hi

theorem IsU.conj_b {g : A6} (hg : IsU g) : ∃ k : A6, k * (a * a') * k⁻¹ = g := by
  obtain ⟨h3, h1, hn⟩ := hg
  rcases exists_conj_a_or_b g h3 h1 with ⟨k, hk⟩ | h
  · exfalso
    obtain ⟨i, hi⟩ := a_fix
    subst hk
    exact hn (k.1 i) (fix_conj k a i hi)
  · exact h


section Fc

variable {W : Type} [CommGroup W] [Finite W] {ρ : A6 →* MulAut W}

omit [Finite W] in
theorem fc_T (g : A6) (hg : IsT g) : fc ρ g = fc ρ a := by
  obtain ⟨k, rfl⟩ := hg.conj_a
  exact fc_conj ρ k a

omit [Finite W] in
theorem fc_U (g : A6) (hg : IsU g) : fc ρ g = fc ρ (a * a') := by
  obtain ⟨k, rfl⟩ := hg.conj_b
  exact fc_conj ρ k (a * a')

omit [Finite W] in
theorem fc_invol (g : A6) (hg1 : g ≠ 1) (hg2 : g * g = 1) : fc ρ g = fc ρ x0A6 := by
  have hx0 : x0A6 ≠ 1 := x0A6_ne_one
  obtain ⟨k, hkA, hk⟩ := CFSG.Quasithin.S143.alt6_invol_conj x0P g.1 (mem_alternatingGroup.mpr sign_x0P) g.2
    (fun h => hx0 (Subtype.ext h)) (fun h => hg1 (Subtype.ext h)) rel_x0y0.1
    (by simpa using congrArg Subtype.val hg2)
  have : (⟨k, hkA⟩ : A6) * x0A6 * (⟨k, hkA⟩ : A6)⁻¹ = g := Subtype.ext hk
  rw [← this]
  exact fc_conj ρ _ _

theorem Setup.two_le_fc (h : Setup ρ) (g : A6) (h4 : g * g * g * g = 1) : 2 ≤ fc ρ g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := fc_modEq_prime_pow ρ 2 2 (g := g) (by
    have : g ^ (2 ^ 2) = g * g * g * g := by simp [pow_succ, mul_assoc]
    rw [this, h4])
  have hpos : 0 < fc ρ g := Nat.card_pos
  rw [h.card] at hm
  unfold Nat.ModEq at hm
  omega


theorem Setup.sum_fc (h : Setup ρ) : ∑ g : A6, fc ρ g = 720 := by
  classical
  let _ : MulAction A6 W := MulAction.compHom W ρ
  have : Fintype W := Fintype.ofFinite W
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A6 W
  have h1 : ∀ g : A6, Fintype.card (MulAction.fixedBy W g) = fc ρ g := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    unfold fc
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl)
  have h2 : Fintype.card (Quotient (MulAction.orbitRel A6 W)) = 2 := by
    obtain ⟨u, hu⟩ : ∃ u : W, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : Nat.card W = 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
        exact ⟨1, fun w => hcon w⟩
      rw [h.card] at h1
      omega
    let f : W → Bool := fun w => decide (w = 1)
    have hker : MulAction.orbitRel A6 W = Setoid.ker f := by
      ext x y
      rw [MulAction.orbitRel_apply]
      show x ∈ MulAction.orbit A6 y ↔ f x = f y
      constructor
      · rintro ⟨g, hg⟩
        have hg' : ρ g y = x := hg
        by_cases hy : y = 1
        · have hx : x = 1 := by rw [← hg', hy, map_one]
          simp [f, hx, hy]
        · have hx : x ≠ 1 := fun hx => hy ((ρ g).injective (by rw [hg', hx, map_one]))
          simp [f, hx, hy]
      · intro hxy
        by_cases hy : y = 1
        · have hx : x = 1 := by simpa [f, hy] using hxy
          exact ⟨1, by simp [hx, hy]⟩
        · have hx : x ≠ 1 := by
            intro hx; simp [f, hx, hy] at hxy
          obtain ⟨g, hg⟩ := h.transitive hy hx
          exact ⟨g, hg⟩
    have hsurj : Function.Surjective f := by
      intro b
      cases b
      · exact ⟨u, by simp [f, hu]⟩
      · exact ⟨1, by simp [f]⟩
    rw [hker]
    rw [Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hsurj)]
    rfl
  have h3 : Fintype.card A6 = 360 := by
    rw [← Nat.card_eq_fintype_card, card_A6]
  simp only [h1, h2, h3] at hB
  omega

end Fc

end CFSG.Quasithin.A6Fin
