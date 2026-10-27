module

public import CFSG.Quasithin.EmptyFaithful.S153E59O
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open scoped MatrixGroups

namespace S153E59

section PiModule

variable {G : Type} [Group G]

theorem sl2_pow_six : ∀ B : SL(2, ZMod 2), B ^ 6 = 1 := by decide +kernel

theorem sl2_pow_three_of_pow {B : SL(2, ZMod 2)} {k : ℕ} (h : B ^ 3 ^ k = 1) : B ^ 3 = 1 := by
  have h1 : orderOf B ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one h
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  have h2 : orderOf B ∣ 6 := orderOf_dvd_of_pow_eq_one (sl2_pow_six B)
  rw [hj'] at h2
  have h3 : j ≤ 1 := by
    by_contra hj1
    have hj2 : 2 ≤ j := by omega
    have : 3 ^ 2 ∣ 3 ^ j := pow_dvd_pow 3 hj2
    have := this.trans h2
    omega
  apply orderOf_dvd_iff_pow_eq_one.1
  rw [hj']
  exact pow_dvd_pow 3 (by omega) |>.trans (by simp)

open CFSG.Quasithin in
theorem centralizes_Pi {M Si S S₂ : Subgroup G} [Finite G]
    (hnat : IsSumOfNatSL2ModulesN153 1 M Si S S₂)
    {d e r : G} (hdM : d ∈ M) (hdS : d ∉ S) {k : ℕ} (hdk : d ^ 3 ^ k = 1)
    (hdSi : ∀ x ∈ Si, d * x * d⁻¹ ∈ Si)
    (hrSi : ∀ x ∈ Si, r * x * r⁻¹ ∈ Si) (hrd : r * d = d * r) (hre : r * e = e * r)
    (hrV : ∀ v ∈ S₂, r * v * r⁻¹ = v) {m : ℕ} (hr : r ^ 2 ^ m = 1)
    (hVab : ∀ v ∈ S₂, ∀ w ∈ S₂, v * w = w * v)
    (hef : ∀ v ∈ S₂, e * v * e⁻¹ = v → v = 1)
    (he : ∀ x ∈ Si, e * x * e⁻¹ * x⁻¹ ∈ S₂) :
    ∀ x ∈ Si, r * x * r⁻¹ * x⁻¹ = 1 := by
  obtain ⟨β, φ, hβs, hβk, hφs, hφk, hrel⟩ := hnat
  have hA1 : β ⟨d, hdM⟩ ≠ 1 := fun h => hdS ((hβk _).1 h)
  have hA3 : β ⟨d, hdM⟩ ^ 3 = 1 := by
    refine sl2_pow_three_of_pow (k := k) ?_
    rw [← map_pow]
    have : (⟨d, hdM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hdk)
    rw [this, map_one]
  let π : ↥Si → (Fin 2 → ZMod 2) := fun x => Multiplicative.toAdd (φ x) 0
  have hπadd : ∀ x y : ↥Si, π (x * y) = π x + π y := by
    intro x y
    simp [π, map_mul]
  have hπs : Function.Surjective π := by
    intro w
    obtain ⟨x, hx⟩ := hφs (Multiplicative.ofAdd (fun _ => w))
    exact ⟨x, by simp [π, hx]⟩
  have hπk : ∀ x : ↥Si, π x = 0 ↔ (x : G) ∈ S₂ := by
    intro x
    rw [← hφk]
    constructor
    · intro h
      have : Multiplicative.toAdd (φ x) = 0 := by
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        rw [hj]
        exact h
      exact Multiplicative.toAdd.injective this
    · intro h
      have : Multiplicative.toAdd (φ x) = 0 := by rw [h]; rfl
      simp [π, this]
  have hrel' : ∀ x : ↥Si, π ⟨d * x * d⁻¹, hdSi x x.2⟩ = β ⟨d, hdM⟩ • π x := by
    intro x
    have := hrel ⟨d, hdM⟩ x ⟨d * x * d⁻¹, hdSi x x.2⟩ rfl
    simp [π, this]
  have hA1' := commutes_of_equivariant π hπadd hπs hπk hdSi hA1 hA3 hrel' hrSi hrd hrV hr
  intro x hx
  exact comm_eq_one_of_fixed hVab hrV hef hre (he x hx) (hA1' x hx)

end PiModule

end S153E59

end CFSG.Quasithin
