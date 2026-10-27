module

public import CFSG.Permutation.UnitaryThreeRecognition.ZTransitive
public import CFSG.Permutation.UnitaryThreeRecognition.RootNormal

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]

namespace IsRootSubgroup

variable {Q : Subgroup G} {a : Ω} (hQ : IsRootSubgroup Q a)
include hQ

theorem centQ_commute [Finite G] [Finite Ω] {b : Ω} (hb : b ≠ a)
    (htwo : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : G, g • x = z ∧ g • y = w)
    (hfaith : ∀ g : G, (∀ x : Ω, g • x = x) → g = 1)
    (hcomm : ∀ t₁ ∈ pairStab G a b, ∀ t₂ ∈ pairStab G a b, t₁ * t₂ = t₂ * t₁)
    {j : G} (hj : j ∈ pairStab G a b) (hj2 : j * j = 1) (hj1 : j ≠ 1)
    (hsq : ∀ t ∈ pairStab G a b, t * t = 1 → t = 1 ∨ t = j)
    {p f d : ℕ} (hpp : p.Prime) (hp : 3 ≤ p) (hf : 1 ≤ f) (hpodd : Odd p) (hd : Odd d)
    (hd3 : d ≤ 3)
    (hQcard : Nat.card Q = p ^ (3 * f)) (hΩcard : Nat.card Ω = p ^ (3 * f) + 1)
    (hTcard : Nat.card (pairStab G a b) * d = p ^ (2 * f) - 1)
    {s : G} (hsa : s • a = b) (hs2 : s * s = 1)
    {x : G} (hx : x ∈ Q) {z : G} (hz : z ∈ centQ Q j) : x * z = z * x := by
  classical
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hTdvd : Nat.card (pairStab G a b) ∣ p ^ (2 * f) - 1 := ⟨d, hTcard.symm⟩
  have hZ := hQ.card_centQ_involution_eq hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hQcard
    hΩcard hTdvd
  let : Fact p.Prime := ⟨hpp⟩
  have hQp : IsPGroup p Q := IsPGroup.of_card hQcard
  let X : Set G := (centQ Q j : Set G)
  have hX : ∀ u ∈ Q, ∀ y ∈ X, u * y * u⁻¹ ∈ X := fun u hu y hy =>
    hQ.centQ_conj_mem hb htwo hfaith hcomm hj hj2 hj1 hsq hpp hp hf hpodd hd hd3 hQcard hΩcard
      hTcard hsa hs2 hu hy
  let act : MulAction Q X := conjAction Q X hX
  have h1fix : (⟨1, (centQ Q j).one_mem⟩ : X) ∈ fixedPoints Q X := by
    intro u
    apply Subtype.ext
    change (u : G) * 1 * (u : G)⁻¹ = 1
    group
  have hpX : p ∣ Nat.card X := by
    have : Nat.card X = p ^ f := hZ
    rw [this]
    exact dvd_pow_self p (by omega)
  obtain ⟨z₀, hz₀fix, hz₀ne⟩ :=
    hQp.exists_fixed_point_of_prime_dvd_card_of_fixed_point X hpX h1fix
  have hz₀1 : (z₀ : G) ≠ 1 := fun h => hz₀ne (Subtype.ext h.symm)
  have hz₀c : ∀ u ∈ Q, u * z₀ = z₀ * u := by
    intro u hu
    have h1 : ((⟨u, hu⟩ : Q) • z₀ : X) = z₀ := hz₀fix ⟨u, hu⟩
    have h2 : u * (z₀ : G) * u⁻¹ = z₀ := congrArg Subtype.val h1
    calc u * (z₀ : G) = u * z₀ * u⁻¹ * u := by group
      _ = z₀ * u := by rw [h2]
  obtain ⟨t, ht, htz⟩ := hQ.exists_conj_eq_of_mem_centQ hb htwo hfaith hcomm hj hj2 hj1 hsq hpp
    hp hf hpodd hd hQcard hΩcard hTcard hsa hs2 z₀.2 hz₀1 hz hz1
  have hx' : t⁻¹ * x * t⁻¹⁻¹ ∈ Q :=
    hQ.normal t⁻¹ ((pairStab G a b).inv_mem ht).1 x hx
  have h3 := hz₀c _ hx'
  rw [← htz]
  calc x * (t * z₀ * t⁻¹) = t * ((t⁻¹ * x * t⁻¹⁻¹) * z₀) * t⁻¹ := by group
    _ = t * (z₀ * (t⁻¹ * x * t⁻¹⁻¹)) * t⁻¹ := by rw [h3]
    _ = t * z₀ * t⁻¹ * x := by group

end IsRootSubgroup

end CFSG.UnitaryThreeRecognition
