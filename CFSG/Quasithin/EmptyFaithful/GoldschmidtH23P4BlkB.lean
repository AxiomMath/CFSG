module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H23P4

variable {G : Type*} [Group G]

theorem card_modEq_card_fixed [Finite G] {X : Subgroup G} {y : G}
    (hX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) {k : ℕ} (hy : y ^ 5 ^ k = 1) :
    Nat.card X ≡ Nat.card ↥(X ⊓ Subgroup.centralizer {y}) [MOD 5] := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End X := fun x => ⟨y * x * y⁻¹, hX x x.2⟩
  have hf : ∀ (j : ℕ) (x : X), ((f ^ j) x : G) = y ^ j * x * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro x; simp; rfl
    | succ j ih =>
      intro x
      rw [pow_succ']
      show y * ((f ^ j) x : G) * y⁻¹ = _
      rw [ih]
      group
  have hfk : f ^ 5 ^ k = 1 := by
    funext x
    apply Subtype.ext
    rw [hf, hy]
    simp
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 5) hfk
  have hmem : ∀ x : Function.fixedPoints f, (x.1 : G) ∈ Subgroup.centralizer ({y} : Set G) := by
    intro x
    have hx : y * (x.1 : G) * y⁻¹ = x.1 := congrArg Subtype.val x.2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [mul_inv_eq_iff_eq_mul] at hx
    exact hx
  have hfix : ∀ z : ↥(X ⊓ Subgroup.centralizer {y}), f ⟨z.1, z.2.1⟩ = ⟨z.1, z.2.1⟩ := by
    intro z
    have hz := (Subgroup.mem_centralizer_iff.mp z.2.2) y rfl
    apply Subtype.ext
    show y * z.1 * y⁻¹ = z.1
    rw [mul_inv_eq_iff_eq_mul]
    exact hz
  let e : Function.fixedPoints f ≃ ↥(X ⊓ Subgroup.centralizer {y}) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, hmem x⟩
      invFun := fun z => ⟨⟨z.1, z.2.1⟩, hfix z⟩
      left_inv := fun x => rfl
      right_inv := fun z => rfl }
  have h1 : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
  have h2 : Nat.card ↥(X ⊓ Subgroup.centralizer {y}) = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  rw [h1, h2]
  exact h

theorem relIndex_modEq_one [Finite G] {Z X : Subgroup G} {y : G} (hZX : Z ≤ X)
    (hX : ∀ x ∈ X, y * x * y⁻¹ ∈ X) (hZ : ∀ x ∈ Z, y * x * y⁻¹ ∈ Z) {k : ℕ}
    (hy : y ^ 5 ^ k = 1) (hfix : ∀ x ∈ X, y * x * y⁻¹ = x → x ∈ Z) (h2 : IsPGroup 2 Z) :
    Z.relIndex X ≡ 1 [MOD 5] := by
  have hXc := card_modEq_card_fixed hX hy
  have hZc := card_modEq_card_fixed hZ hy
  have heq : X ⊓ Subgroup.centralizer {y} = Z ⊓ Subgroup.centralizer {y} := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨hx, hc⟩
      exact ⟨hfix x hx (by rw [mul_inv_eq_iff_eq_mul]; exact hc), hc⟩
    · rintro ⟨hx, hc⟩
      exact ⟨hZX hx, hc⟩
  have hcard : Nat.card X = Z.relIndex X * Nat.card Z := by
    have := Subgroup.relIndex_mul_card (H := Z) (K := X)
    rw [inf_eq_left.2 hZX] at this
    exact this.symm
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Z) 5 := by
    rw [hn]
    exact Nat.Coprime.pow_left _ (by norm_num)
  rw [heq] at hXc
  have h3 : Z.relIndex X * Nat.card Z ≡ 1 * Nat.card Z [MOD 5] := by
    rw [one_mul, ← hcard]
    exact hXc.trans hZc.symm
  exact Nat.ModEq.cancel_right_of_coprime (by simpa [Nat.gcd_comm] using hcop) h3

end CFSG.Quasithin.H23P4
