module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item219LieProof

open Subgroup

theorem dihedral_six_cube_eq : ∀ x y : DihedralGroup 6, x ^ 3 = 1 → y ^ 3 = 1 → y ≠ 1 →
    x = 1 ∨ x = y ∨ x = y ^ 2 := by
  decide

variable {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem conj_mem_powers_of_dihedral {S : Subgroup (MulAut A)} (e : S ≃* DihedralGroup 6)
    {u : S} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1) (φ : S) :
    φ⁻¹ * u * φ = 1 ∨ φ⁻¹ * u * φ = u ∨ φ⁻¹ * u * φ = u ^ 2 := by
  have hx3 : e (φ⁻¹ * u * φ) ^ 3 = 1 := by
    rw [← map_pow, show φ⁻¹ * u * φ = φ⁻¹ * u * φ⁻¹⁻¹ by rw [inv_inv], conj_pow, hu3, mul_one,
      inv_inv, inv_mul_cancel, map_one]
  have hy3 : e u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hy1 : e u ≠ 1 := fun h => hu1 (e.injective (h.trans (map_one e).symm))
  rcases dihedral_six_cube_eq _ _ hx3 hy3 hy1 with h | h | h
  · exact Or.inl (e.injective (h.trans (map_one e).symm))
  · exact Or.inr (Or.inl (e.injective h))
  · exact Or.inr (Or.inr (e.injective (h.trans (map_pow e u 2).symm)))

theorem exists_involution_fix {S : Subgroup (MulAut A)} (e : S ≃* DihedralGroup 6)
    {B : Subgroup A} (hB9 : Nat.card B = 9) (hSB : ∀ σ ∈ S, ∀ x ∈ B, σ x ∈ B)
    (hfaith : ∀ σ ∈ S, (∀ x ∈ B, σ x = x) → σ = 1) {d : A} (hdB : d ∈ B) (hd1 : d ≠ 1) :
    ∃ σ ∈ S, σ d = d ∧ σ ^ 2 = 1 ∧ σ ≠ 1 := by
  classical
  set T := MulAction.stabilizer S d with hT
  have hS12 : Nat.card S = 12 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hmul := T.card_mul_index
  rw [MulAction.index_stabilizer S d, hS12] at hmul
  have hsmul : ∀ (σ : S) (x : A), σ • x = (σ : MulAut A) x := fun _ _ => rfl
  have hcardSet : ∀ F : Subgroup A, ((F : Set A) \ {1}).ncard = Nat.card F - 1 := by
    intro F
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem F), ← Nat.card_coe_set_eq]
    rfl
  have horb : MulAction.orbit S d ⊆ (B : Set A) \ {1} := by
    rintro _ ⟨σ, rfl⟩
    change (σ : MulAut A) d ∈ (B : Set A) \ {1}
    refine ⟨hSB σ σ.2 d hdB, fun h => hd1 ?_⟩
    have h' : (σ : MulAut A) d = 1 := h
    exact (map_eq_one_iff _ (σ : MulAut A).injective).mp h'
  have hle : (MulAction.orbit S d).ncard ≤ 8 := by
    have := Set.ncard_le_ncard horb (Set.toFinite _)
    rwa [hcardSet, hB9] at this
  by_cases h2 : 2 ∣ Nat.card T
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 h2
    have hτ2 : τ ^ 2 = 1 := by rw [← hτ]; exact pow_orderOf_eq_one τ
    refine ⟨((τ : S) : MulAut A), (τ : S).2, ?_, ?_, ?_⟩
    · have h := τ.2
      rw [MulAction.mem_stabilizer_iff, hsmul] at h
      exact h
    · have h := congrArg (fun x : T => ((x : S) : MulAut A)) hτ2
      simpa using h
    · intro h
      have h1 : τ = 1 := Subtype.ext (Subtype.ext h)
      rw [h1, orderOf_one] at hτ
      norm_num at hτ
  · exfalso
    have hT3 : Nat.card T = 3 ∧ (MulAction.orbit S d).ncard = 4 := by
      have hTpos : 0 < Nat.card T := Nat.card_pos
      have hTle : Nat.card T ≤ 12 := Nat.le_of_dvd (by norm_num) ⟨_, hmul.symm⟩
      interval_cases h : Nat.card T <;> omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (by rw [hT3.1])
    have hu3 : (u : S) ^ 3 = 1 := by
      have h : u ^ 3 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
      exact congrArg Subtype.val h
    have hu1 : (u : S) ≠ 1 := by
      intro h
      have h1 : u = 1 := Subtype.ext h
      rw [h1, orderOf_one] at hu
      norm_num at hu
    have huT : (u : S) ∈ T := u.2
    have hconj : ∀ φ : S, φ⁻¹ * (u : S) * φ ∈ T := by
      intro φ
      rcases conj_mem_powers_of_dihedral e hu3 hu1 φ with h | h | h <;> rw [h]
      · exact one_mem T
      · exact huT
      · exact pow_mem huT 2
    set υ : MulAut A := ((u : S) : MulAut A) with hυ
    set F : Subgroup A := B ⊓ υ.toMonoidHom.eqLocus (MonoidHom.id A) with hF
    have horbF : MulAction.orbit S d ⊆ (F : Set A) \ {1} := by
      intro x hx
      obtain ⟨hxB, hx1⟩ := horb hx
      obtain ⟨φ, rfl⟩ := hx
      refine ⟨⟨hxB, ?_⟩, hx1⟩
      have h1 : (φ⁻¹ * (u : S) * φ) • d = d := hconj φ
      change υ (φ • d) = φ • d
      have h2 : (u : S) • (φ • d) = φ • ((φ⁻¹ * (u : S) * φ) • d) := by
        rw [mul_smul, mul_smul, smul_inv_smul]
      rw [h1] at h2
      exact h2
    have hFB : F ≤ B := inf_le_left
    have hFne : F ≠ B := by
      intro h
      apply hu1
      have h1 := hfaith υ (u : S).2 fun x hx => by
        have hx' : x ∈ F := h ▸ hx
        exact hx'.2
      exact Subtype.ext h1
    have hFdvd : Nat.card F ∣ 9 := hB9 ▸ card_dvd_of_le hFB
    have hFlt : Nat.card F < 9 := hB9 ▸ card_lt_of_lt (lt_of_le_of_ne hFB hFne)
    have hF3 : Nat.card F ≤ 3 := by
      have hFpos : 0 < Nat.card F := Nat.card_pos
      interval_cases h : Nat.card F <;> omega
    have := Set.ncard_le_ncard horbF (Set.toFinite _)
    rw [hcardSet] at this
    omega

end CFSG.RankThree.PartTwo.Sec21.Item219LieProof
