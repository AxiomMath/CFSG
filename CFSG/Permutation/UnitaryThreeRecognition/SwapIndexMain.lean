module

public import CFSG.Permutation.UnitaryThreeRecognition.SwapIndex
public import Mathlib.GroupTheory.Sylow
public import CFSG.Permutation.UnitaryThreeRecognition.InvolutionCentralizer

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

omit [MulAction G Ω] in
theorem exists_pow_eq_involution {T : Subgroup G} {j : G}
    (hsq : ∀ t ∈ T, t * t = 1 → t = 1 ∨ t = j) {σ : G} (hσT : σ ∈ T) (hσ1 : σ ≠ 1)
    {i : ℕ} (hord : orderOf σ = 2 ^ i) : ∃ N : ℕ, σ ^ N = j := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rw [hi, pow_zero, orderOf_eq_one_iff] at hord
    exact absurd hord hσ1
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  refine ⟨2 ^ i', ?_⟩
  have hmem : σ ^ 2 ^ i' ∈ T := T.pow_mem hσT _
  have hsq' : σ ^ 2 ^ i' * σ ^ 2 ^ i' = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ', ← hord, pow_orderOf_eq_one]
  rcases hsq _ hmem hsq' with h | h
  · exfalso
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by positivity) hdvd
    have : 2 ^ (i' + 1) ≤ 2 ^ i' := this
    rw [pow_succ] at this
    have hpos : 0 < 2 ^ i' := by positivity
    omega
  · exact h

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

omit hQ in
theorem two_pow_dvd_card_fixed [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    (heven : Even (Nat.card {y : Ω // j • y = y}))
    (hmoved : ∃ x : Ω, j • x ≠ x)
    {s : G} (hsa : s • a = b) (hsb : s • b = a)
    {n : ℕ} (hn : 2 ^ n ∣ Nat.card (swapFix G a b s)) :
    2 ^ n ∣ Nat.card {y : Ω // j • y = y} := by
  classical
  have hab : a ≠ b := fun h => hb h.symm
  have hcj : ∀ s' : G, s' • a = b → s' • b = a → s' * j = j * s' := by
    intro s' hsa' hsb'
    have hmem : s' * j * s'⁻¹ ∈ pairStab G a b := conj_mem_pairStab hsa' hsb' hj
    have hsq' : s' * j * s'⁻¹ * (s' * j * s'⁻¹) = 1 := by
      calc s' * j * s'⁻¹ * (s' * j * s'⁻¹) = s' * (j * j) * s'⁻¹ := by group
        _ = 1 := by rw [hj2]; group
    rcases hsq _ hmem hsq' with h | h
    · exfalso; apply hj1
      have := congrArg (fun z => s'⁻¹ * z * s') h
      simpa [mul_assoc] using this
    · calc s' * j = s' * j * s'⁻¹ * s' := by group
        _ = j * s' := by rw [h]
  obtain ⟨x, hx⟩ := hmoved
  have hxjx : x ≠ j • x := fun h => hx h.symm
  obtain ⟨g, hgx, hgjx⟩ := htwo hxjx hab
  have hs'a : (g * j * g⁻¹) • a = b := by
    rw [mul_smul, mul_smul, show g⁻¹ • a = x by rw [inv_smul_eq_iff, hgx], hgjx]
  have hs'b : (g * j * g⁻¹) • b = a := by
    have h1 : g⁻¹ • b = j • x := by rw [inv_smul_eq_iff, hgjx]
    have : (g * j * g⁻¹) • b = g • (j • (j • x)) := by simp only [mul_smul, h1]
    rw [this, ← mul_smul j j x, hj2, one_smul, hgx]
  have hTs : swapFix G a b s = swapFix G a b (g * j * g⁻¹) := swapFix_eq hsa hsb hs'a hs'b hcomm
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₀, hS₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hn
  let S : Subgroup G := S₀.map (swapFix G a b s).subtype
  have hScard : Nat.card S = 2 ^ n := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS₀]
  have hSle : S ≤ swapFix G a b s := by
    rintro _ ⟨σ, _, rfl⟩
    exact σ.property
  let F := {y : Ω // j • y = y}
  have hcomm_conj : ∀ σ ∈ S, (g⁻¹ * σ * g) * j = j * (g⁻¹ * σ * g) := by
    intro σ hσ
    have hσs : σ ∈ swapFix G a b (g * j * g⁻¹) := hTs ▸ hSle hσ
    have h2 : (g * j * g⁻¹) * σ = σ * (g * j * g⁻¹) := (mem_swapFix.mp hσs).2
    calc (g⁻¹ * σ * g) * j = g⁻¹ * (σ * (g * j * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * j * g⁻¹) * σ) * g := by rw [h2]
      _ = j * (g⁻¹ * σ * g) := by group
  let act : MulAction S F :=
    { smul := fun σ y => ⟨(g⁻¹ * σ * g) • (y : Ω), by
        rw [smul_smul, ← hcomm_conj σ σ.property, mul_smul, y.2]⟩
      one_smul := fun y => Subtype.ext (by
        change (g⁻¹ * ((1 : S) : G) * g) • (y : Ω) = y
        simp)
      mul_smul := fun σ τ y => Subtype.ext (by
        change (g⁻¹ * ((σ * τ : S) : G) * g) • (y : Ω) =
          (g⁻¹ * (σ : G) * g) • ((g⁻¹ * (τ : G) * g) • (y : Ω))
        rw [smul_smul]
        congr 1
        simp only [Subgroup.coe_mul]
        group) }
  have hfree : ∀ y : F, stabilizer S y = ⊥ := by
    intro y
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra hσ1
    have hσy : (g⁻¹ * (σ : G) * g) • (y : Ω) = y := congrArg Subtype.val hσ
    have hσ1' : (σ : G) ≠ 1 := fun h => hσ1 (Subtype.ext h)
    have hσT : (σ : G) ∈ pairStab G a b := (hSle σ.property).1
    have hordS : orderOf σ ∣ 2 ^ n := by rw [← hScard]; exact orderOf_dvd_natCard σ
    obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hordS
    have hord : orderOf (σ : G) = 2 ^ i := by rw [Subgroup.orderOf_coe]; exact hi
    obtain ⟨N, hN⟩ := exists_pow_eq_involution hsq hσT hσ1' hord
    have hiy : (g⁻¹ * j * g) • (y : Ω) = y := by
      have hpow : (g⁻¹ * (σ : G) * g) ^ N = g⁻¹ * j * g := by
        rw [← hN]
        have := conj_pow (a := g⁻¹) (b := (σ : G)) (i := N)
        simpa using this
      have hfixpow : ∀ n : ℕ, ((g⁻¹ * (σ : G) * g) ^ n) • (y : Ω) = y := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [pow_succ, mul_smul, hσy, ih]
      rw [← hpow]
      exact hfixpow N
    have hi2 : (g⁻¹ * j * g) * (g⁻¹ * j * g) = 1 := by
      calc (g⁻¹ * j * g) * (g⁻¹ * j * g) = g⁻¹ * (j * j) * g := by group
        _ = 1 := by rw [hj2]; group
    have hi1 : g⁻¹ * j * g ≠ 1 := by
      intro h
      apply hj1
      have := congrArg (fun z => g * z * g⁻¹) h
      simpa [mul_assoc] using this
    have hij : g⁻¹ * j * g ≠ j := by
      intro h
      apply hx
      have hfx : (g⁻¹ * j * g) • x = x := by
        rw [mul_smul, mul_smul, hgx, hj.1, inv_smul_eq_iff, hgx]
      rw [h] at hfx
      exact hfx
    have hcij : (g⁻¹ * j * g) * j = j * (g⁻¹ * j * g) := by
      have h3 := hcj _ hs'a hs'b
      calc (g⁻¹ * j * g) * j = g⁻¹ * (j * (g * j * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * j * g⁻¹) * j) * g := by rw [h3]
        _ = j * (g⁻¹ * j * g) := by group
    exact not_fixes_of_commute hb htwo hsq hj2 hj1 heven hi2 hi1 hij hcij y.2 hiy
  have := card_dvd_of_stabilizer_eq_bot hfree
  rwa [hScard] at this

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
