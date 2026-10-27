module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bBase

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin

theorem exists_pair_of_card_two {G : Type*} [Group G] (N : Subgroup G) (h : Nat.card N = 2) :
    ∃ z ∈ N, z ≠ 1 ∧ ∀ g ∈ N, g = 1 ∨ g = z := by
  obtain ⟨x, y, hxy, hall⟩ := Nat.card_eq_two_iff.1 h
  have hmem : ∀ g : N, g = x ∨ g = y := fun g => by
    have : g ∈ ({x, y} : Set N) := by
      rw [hall]
      exact Set.mem_univ _
    simpa using this
  have hxy' : (x : G) ≠ (y : G) := fun e => hxy (Subtype.ext e)
  rcases hmem ⟨1, N.one_mem⟩ with h1 | h1
  · have hx1 : (x : G) = 1 := (congrArg Subtype.val h1).symm
    refine ⟨(y : G), y.2, fun e => hxy' (hx1.trans e.symm), fun g hg => ?_⟩
    rcases hmem ⟨g, hg⟩ with h2 | h2
    · left
      exact (congrArg Subtype.val h2).trans hx1
    · right
      exact congrArg Subtype.val h2
  · have hy1 : (y : G) = 1 := (congrArg Subtype.val h1).symm
    refine ⟨(x : G), x.2, fun e => hxy' (e.trans hy1.symm), fun g hg => ?_⟩
    rcases hmem ⟨g, hg⟩ with h2 | h2
    · right
      exact congrArg Subtype.val h2
    · left
      exact (congrArg Subtype.val h2).trans hy1

section NoTwo

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem fix_of_nonsing (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) (z : W ≃ₗ[ZMod 2] W)
    (hz : ∀ γ ∈ orthogonalSubgroupOf q, ∀ x : W, γ (z x) = z (γ x)) {u : W} (hu : q u = 1) :
    z u = u := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [q_zero q B hq] at hu
    exact zero_ne_one hu
  have key : ∀ x : W, B (z x) u • u = B x u • z u := by
    intro x
    have h := hz (trEquiv q B hq u) (trEquiv_mem q B hq hu) x
    rw [trEquiv_apply, trEquiv_apply] at h
    simp only [map_add, map_smul, smul_eq_mul] at h
    exact add_left_cancel h
  obtain ⟨x0, hx0⟩ := exists_B_eq_one B hB q hq hu0
  have h1 := key x0
  rw [hx0, one_smul] at h1
  rcases zmod2_cases (B (z x0) u) with h | h
  · rw [h, zero_smul] at h1
    exact absurd ((z.map_eq_zero_iff).1 h1.symm) hu0
  · rw [h, one_smul] at h1
    exact h1.symm

theorem fix_all (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    [FiniteDimensional (ZMod 2) W]
    (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) (hdim : Module.finrank (ZMod 2) W = 6)
    (z : W ≃ₗ[ZMod 2] W)
    (hz : ∀ γ ∈ orthogonalSubgroupOf q, ∀ x : W, γ (z x) = z (γ x)) (x : W) :
    z x = x := by
  by_cases hx : q x = 1
  · exact fix_of_nonsing q B hq hB z hz hx
  · have hqx : q x = 0 := by
      rcases zmod2_cases (q x) with h | h
      · exact h
      · exact absurd h hx
    by_cases hx0 : x = 0
    · subst hx0
      exact z.map_zero
    · obtain ⟨y, hyB, hyq⟩ := exists_nonsing_perp B hB q hq hdim hx0 hqx
      have hxy : q (x + y) = 1 := by
        rw [hq, hqx, hyq, hyB, add_zero, zero_add]
      have hsplit : y + (x + y) = x := by
        rw [← add_assoc, add_comm y x, add_assoc, add_self_eq_zero', add_zero]
      have hzy : z y = y := fix_of_nonsing q B hq hB z hz hyq
      have hzxy : z (x + y) = x + y := fix_of_nonsing q B hq hB z hz hxy
      calc z x = z (y + (x + y)) := by rw [hsplit]
        _ = z y + z (x + y) := map_add z y (x + y)
        _ = x := by rw [hzy, hzxy, hsplit]

end NoTwo

theorem f4_no_normal_two {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hdim : Module.finrank (ZMod 2) W = 6) (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) :
    ∀ N : Subgroup (W ≃ₗ[ZMod 2] W), N ≤ orthogonalSubgroupOf q →
      (∀ γ ∈ orthogonalSubgroupOf q, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) → Nat.card N ≠ 2 := by
  intro N hN hnorm hcard
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  obtain ⟨z, hzN, hz1, hall⟩ := exists_pair_of_card_two N hcard
  have hzO : z ∈ orthogonalSubgroupOf q := hN hzN
  have hz : ∀ γ ∈ orthogonalSubgroupOf q, ∀ x : W, γ (z x) = z (γ x) := by
    intro γ hγ x
    rcases hall _ (hnorm γ hγ z hzN) with h1 | h1
    · exfalso
      apply hz1
      have h2 : z = γ⁻¹ * (γ * z * γ⁻¹) * γ := by group
      rw [h2, h1]
      group
    · have h2 : γ * z = z * γ := by
        calc γ * z = (γ * z * γ⁻¹) * γ := by group
          _ = z * γ := by rw [h1]
      exact congrArg (fun g : W ≃ₗ[ZMod 2] W => g x) h2
  apply hz1
  ext x
  show z x = x
  exact fix_all q B hq hB hdim z hz x

end CFSG.Quasithin.H13.C1294
