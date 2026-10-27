module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.Permutation.UnitaryThreeRecognition.Counting
public import CFSG.Permutation.UnitaryThreeRecognition.Fixed

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem count_identity [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j) :
    Nat.card Ω - (Nat.card (centQ Q j) + 1) =
      (Nat.card (centQ Q j) + 1) * Nat.card (centQ Q j) * Nat.card (ConjSwap G j a b) := by
  classical
  have hab : a ≠ b := fun h => hb h.symm
  obtain ⟨g, hga, hgb⟩ := htwo hab hb
  have hgj : g * j = j * g := by
    have hmem : g * j * g⁻¹ ∈ pairStab G a b := conj_mem_pairStab hga hgb hj
    have hsq' : g * j * g⁻¹ * (g * j * g⁻¹) = 1 := by
      calc g * j * g⁻¹ * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases hsq _ hmem hsq' with h | h
    · exfalso; apply hj1
      have := congrArg (fun z => g⁻¹ * z * g) h
      simpa [mul_assoc] using this
    · calc g * j = g * j * g⁻¹ * g := by group
        _ = j * g := by rw [h]
  have hC := hQ.card_centralizer hb hcomm hj hga hgj
  have hTpos : 0 < Nat.card (pairStab G a b) := Nat.card_pos
  have hmoved : Nat.card {x : Ω // j • x ≠ x} = Nat.card Ω - (Nat.card (centQ Q j) + 1) := by
    let : Fintype Ω := Fintype.ofFinite Ω
    have h1 := Fintype.card_subtype_compl (fun x : Ω => j • x = x)
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, hQ.card_fixedPoints hb hj] at h1
    exact h1
  have hS1 := card_swapSet_eq_pairStab_mul hab htwo j
  have hS2 := card_swapSet_eq_centralizer_mul (G := G) a b j
  have : Nat.card (pairStab G a b) * (Nat.card Ω - (Nat.card (centQ Q j) + 1)) =
      Nat.card (pairStab G a b) * ((Nat.card (centQ Q j) + 1) * Nat.card (centQ Q j) *
        Nat.card (ConjSwap G j a b)) := by
    rw [← hmoved, ← hS1, hS2, hC]; ring
  exact Nat.eq_of_mul_eq_mul_left hTpos this

omit hQ in
theorem involution_eq_of_fix_two {a b : Ω} (hab : a ≠ b)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    {j : G} (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {u v : G} (hu2 : u * u = 1) (hu1 : u ≠ 1) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    {y y' : Ω} (hyy' : y ≠ y') (huy : u • y = y) (huy' : u • y' = y') (hvy : v • y = y)
    (hvy' : v • y' = y') : u = v := by
  obtain ⟨h, hha, hhb⟩ := htwo hab hyy'
  have key : ∀ w : G, w * w = 1 → w ≠ 1 → w • y = y → w • y' = y' → h⁻¹ * w * h = j := by
    intro w hw2 hw1 hwy hwy'
    have hmem : h⁻¹ * w * h ∈ pairStab G a b := by
      refine ⟨?_, ?_⟩
      · change (h⁻¹ * w * h) • a = a
        rw [mul_smul, mul_smul, hha, hwy, inv_smul_eq_iff, hha]
      · change (h⁻¹ * w * h) • b = b
        rw [mul_smul, mul_smul, hhb, hwy', inv_smul_eq_iff, hhb]
    have hsq' : h⁻¹ * w * h * (h⁻¹ * w * h) = 1 := by
      calc h⁻¹ * w * h * (h⁻¹ * w * h) = h⁻¹ * (w * w) * h := by group
        _ = 1 := by rw [hw2]; group
    rcases hsq _ hmem hsq' with e | e
    · exfalso; apply hw1
      have := congrArg (fun z => h * z * h⁻¹) e
      simpa [mul_assoc] using this
    · exact e
  have e1 := key u hu2 hu1 huy huy'
  have e2 := key v hv2 hv1 hvy hvy'
  have := e1.trans e2.symm
  have := congrArg (fun z => h * z * h⁻¹) this
  simpa [mul_assoc] using this

omit hQ in
theorem not_fixes_of_commute [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    {j : G} (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (heven : Even (Nat.card {y : Ω // j • y = y}))
    {i : G} (hi2 : i * i = 1) (hi1 : i ≠ 1) (hij : i ≠ j) (hcij : i * j = j * i)
    {y : Ω} (hjy : j • y = y) : i • y ≠ y := by
  classical
  intro hiy
  have hab : a ≠ b := fun h => hb h.symm
  let F := {y : Ω // j • y = y}
  have hpres : ∀ z : F, j • (i • (z : Ω)) = i • (z : Ω) := by
    intro z
    rw [smul_smul, ← hcij, mul_smul, z.2]
  let fi : Function.End F := fun z => ⟨i • (z : Ω), hpres z⟩
  have hfi2 : fi ^ 2 ^ 1 = 1 := by
    funext z
    apply Subtype.ext
    change i • (i • (z : Ω)) = (z : Ω)
    rw [smul_smul, hi2, one_smul]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := fi) (p := 2) (n := 1) hfi2
  have hle : Fintype.card (Function.fixedPoints fi) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    rintro ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    apply Subtype.ext
    by_contra hne
    have hne' : (z₁ : Ω) ≠ (z₂ : Ω) := fun h => hne (Subtype.ext h)
    have h1 : i • (z₁ : Ω) = z₁ := congrArg Subtype.val hz₁
    have h2 : i • (z₂ : Ω) = z₂ := congrArg Subtype.val hz₂
    exact hij (involution_eq_of_fix_two hab htwo hsq hi2 hi1 hj2 hj1 hne' h1 h2 z₁.2 z₂.2)
  have hpos : 1 ≤ Fintype.card (Function.fixedPoints fi) := by
    have : Nonempty (Function.fixedPoints fi) := ⟨⟨⟨y, hjy⟩, Subtype.ext hiy⟩⟩
    exact Fintype.card_pos
  have hone : Fintype.card (Function.fixedPoints fi) = 1 := le_antisymm hle hpos
  rw [hone, Nat.ModEq] at hmod
  have hF : Fintype.card F = Nat.card F := (Nat.card_eq_fintype_card).symm
  rw [hF] at hmod
  obtain ⟨r, hr⟩ := heven
  change Nat.card F = r + r at hr
  rw [hr] at hmod
  omega

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
