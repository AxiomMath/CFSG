module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private lemma fzl_card_le_fixed_sq {V : Type*} [Group V] [Finite V]
    (hc : ∀ v w : V, v * w = w * v) (hV : ∀ v : V, v * v = 1)
    (φ : V →* V) (hφ : ∀ v : V, φ (φ v) = v) :
    Nat.card V ≤ Nat.card {v : V // φ v = v} ^ 2 := by
  let ε : V →* V :=
    { toFun := fun v => v * φ v
      map_one' := by rw [map_one, mul_one]
      map_mul' := fun v w => by
        rw [map_mul]
        calc (v * w) * (φ v * φ w) = v * (w * φ v) * φ w := by simp only [mul_assoc]
          _ = v * (φ v * w) * φ w := by rw [hc w (φ v)]
          _ = (v * φ v) * (w * φ w) := by simp only [mul_assoc] }
  have hcard := Subgroup.card_ker_mul_card_range ε
  have hker : Nat.card ε.ker = Nat.card {v : V // φ v = v} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl V) ?_)
    intro v
    rw [MonoidHom.mem_ker]
    show (v * φ v = 1) ↔ φ v = v
    constructor
    · intro h
      rw [mul_eq_one_iff_eq_inv, inv_eq_of_mul_eq_one_right (hV (φ v))] at h
      exact h.symm
    · intro h; rw [h, hV v]
  have hrange : Nat.card ε.range ≤ Nat.card {v : V // φ v = v} := by
    let ψ : ε.range → {v : V // φ v = v} := fun x => ⟨x.1, by
      obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp x.2
      rw [← hv]
      show φ (v * φ v) = v * φ v
      rw [map_mul, hφ]
      exact hc (φ v) v⟩
    exact Nat.card_le_card_of_injective ψ (by
      intro x y hxy
      exact Subtype.ext (show (x : V) = (y : V) from
        congrArg (fun z : {v : V // φ v = v} => z.1) hxy))
  calc Nat.card V = Nat.card ε.ker * Nat.card ε.range := hcard.symm
    _ ≤ Nat.card {v : V // φ v = v} * Nat.card {v : V // φ v = v} := by
        rw [hker]
        exact Nat.mul_le_mul_left _ hrange
    _ = Nat.card {v : V // φ v = v} ^ 2 := by rw [pow_two]

theorem s16c1G43_d1 {L K N X X' : Subgroup G} (hXL : X ≤ L) (hX'L : X' ≤ L)
    (hKnorm : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K)
    (hNcent : ∀ n ∈ N, ∀ l ∈ L, l * n = n * l)
    (hKcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ N)
    (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXsq : ∀ x ∈ X, x * x = 1)
    (hX'sq : ∀ x ∈ X', x * x = 1)
    (hXnK : ¬ X ≤ K) (hX'nK : ¬ X' ≤ K) (hXK : 32 ≤ Nat.card ↥(X ⊓ K))
    (hBX : ∀ x ∈ X, x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ X)
    (hBX' : ∀ x ∈ X', x ∉ K → ∀ k ∈ K, ⁅k, x⁆ ∈ N → k ∈ X')
    (hC : ∀ x ∈ X, ∀ x' ∈ X', ⁅x, x'⁆ ∈ K)
    (hD : X ≠ X' → Nat.card ↥(X ⊓ X') ≤ 4) : X = X' := by
  by_contra hne
  obtain ⟨x, hxX, hxK⟩ := SetLike.not_le_iff_exists.1 hXnK
  obtain ⟨a, haX', haK⟩ := SetLike.not_le_iff_exists.1 hX'nK
  have haa : a * a = 1 := hX'sq a haX'
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  let U : Subgroup G := X ⊓ K
  have hmemU : ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
    intro u hu
    obtain ⟨huX, huK⟩ := Subgroup.mem_inf.1 hu
    have hkK : a * u * a⁻¹ ∈ K := hKnorm a (hX'L haX') u huK
    have hκK : ⁅x⁻¹, a⁻¹⁆ ∈ K := hC x⁻¹ (X.inv_mem hxX) a⁻¹ (X'.inv_mem haX')
    have hνN : ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ ∈ N := hKcomm u huK ⁅x⁻¹, a⁻¹⁆ hκK
    have h1 : ⁅a * u * a⁻¹, x⁆ = a * ⁅u, a⁻¹ * x * a⁆ * a⁻¹ := by
      simp only [commutatorElement_def]; group
    have hκ : a⁻¹ * x * a = x * ⁅x⁻¹, a⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have h2 : ⁅u, a⁻¹ * x * a⁆ = ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ := by
      rw [hκ, commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.2 (hXab u huX x hxX), one_mul,
        hNcent ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ hνN x (hXL hxX)]
      group
    have h3 : a * ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ * a⁻¹ = ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ := by
      rw [hNcent ⁅u, ⁅x⁻¹, a⁻¹⁆⁆ hνN a (hX'L haX')]
      group
    have hN : ⁅a * u * a⁻¹, x⁆ ∈ N := by
      rw [h1, h2, h3]
      exact hνN
    exact Subgroup.mem_inf.2 ⟨hBX x hxX hxK (a * u * a⁻¹) hkK hN, hkK⟩
  let φ : U →* U :=
    { toFun := fun u => ⟨a * (u : G) * a⁻¹, hmemU u u.2⟩
      map_one' := by
        apply Subtype.ext
        show a * (1 : G) * a⁻¹ = (1 : G)
        group
      map_mul' := fun u v => by
        apply Subtype.ext
        show a * ((u : G) * (v : G)) * a⁻¹ = a * (u : G) * a⁻¹ * (a * (v : G) * a⁻¹)
        group }
  have hφ : ∀ u : U, φ (φ u) = u := by
    intro u
    apply Subtype.ext
    show a * (a * (u : G) * a⁻¹) * a⁻¹ = (u : G)
    rw [hainv]
    calc a * (a * (u : G) * a) * a = (a * a) * (u : G) * (a * a) := by group
      _ = (u : G) := by rw [haa]; group
  have hUab : ∀ u v : U, u * v = v * u := by
    intro u v
    apply Subtype.ext
    show (u : G) * (v : G) = (v : G) * (u : G)
    exact hXab u (Subgroup.mem_inf.1 u.2).1 v (Subgroup.mem_inf.1 v.2).1
  have hUsq : ∀ u : U, u * u = 1 := by
    intro u
    apply Subtype.ext
    show (u : G) * (u : G) = (1 : G)
    exact hXsq u (Subgroup.mem_inf.1 u.2).1
  have hle := fzl_card_le_fixed_sq hUab hUsq φ hφ
  have h32 : 32 ≤ Nat.card {v : U // φ v = v} ^ 2 := hXK.trans hle
  have h6 : 6 ≤ Nat.card {v : U // φ v = v} := by
    by_contra h
    have hc5 : Nat.card {v : U // φ v = v} ≤ 5 := Nat.lt_succ_iff.mp (not_le.1 h)
    have hsq : Nat.card {v : U // φ v = v} ^ 2 ≤ 5 ^ 2 := Nat.pow_le_pow_left hc5 2
    have h25 : Nat.card {v : U // φ v = v} ^ 2 ≤ 25 := by
      have h5 : (5 : ℕ) ^ 2 = 25 := by decide
      simpa [h5] using hsq
    exact absurd (h32.trans h25) (by decide)
  let Fix := {v : U // φ v = v}
  have hfix_mem : ∀ v : Fix, (v.1 : G) ∈ X ⊓ X' := by
    intro v
    have hv : a * (v.1 : G) * a⁻¹ = (v.1 : G) := congrArg Subtype.val v.2
    have hcomm : (v.1 : G) * a = a * (v.1 : G) := by
      have h : a * (v.1 : G) = (v.1 : G) * a := by
        calc a * (v.1 : G) = a * (v.1 : G) * a⁻¹ * a := by group
          _ = (v.1 : G) * a := by rw [hv]
      exact h.symm
    have hvX : (v.1 : G) ∈ X := (Subgroup.mem_inf.1 v.1.2).1
    have hvK : (v.1 : G) ∈ K := (Subgroup.mem_inf.1 v.1.2).2
    refine Subgroup.mem_inf.2 ⟨hvX, ?_⟩
    refine hBX' a haX' haK (v.1 : G) hvK ?_
    rw [commutatorElement_eq_one_iff_mul_comm.2 hcomm]
    exact N.one_mem
  let ψ : Fix → ↥(X ⊓ X') := fun v => ⟨(v.1 : G), hfix_mem v⟩
  have hψinj : Function.Injective ψ := by
    intro v w hvw
    have h1 : (v.1 : G) = (w.1 : G) := congrArg (fun z : ↥(X ⊓ X') => (z : G)) hvw
    exact Subtype.ext (Subtype.ext h1)
  have hcardFix : Nat.card Fix ≤ Nat.card ↥(X ⊓ X') :=
    Nat.card_le_card_of_injective ψ hψinj
  have h6' : 6 ≤ Nat.card ↥(X ⊓ X') := h6.trans hcardFix
  exact absurd (h6'.trans (hD hne)) (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
