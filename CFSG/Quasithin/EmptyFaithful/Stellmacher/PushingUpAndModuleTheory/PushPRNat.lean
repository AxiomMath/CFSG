module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F53Mod

variable {G : Type} [Group G]

theorem relIndex_core_eq_card (X : Subgroup G) :
    (pCoreOf 2 X).relIndex X = Nat.card (OTwoQuot X) := by
  have h1 : (pCoreOf 2 X).relIndex X = (CFSG.Open.pCore 2 ↥X).index := by
    unfold Subgroup.relIndex Subgroup.subgroupOf pCoreOf
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  rw [h1, Subgroup.index_eq_card]

section Odd

variable [Finite G] {X P Z : Subgroup G}

theorem exists_odd_notin_core (h : PushHyp X P Z)
    (hX : ∀ n : ℕ, (pCoreOf 2 X).relIndex X ≠ 2 ^ n) :
    ∃ u ∈ X, Odd (orderOf u) ∧ u ∉ pCoreOf 2 X := by
  by_contra hno
  push Not at hno
  have hL : pResidualOf 2 X ≤ pCoreOf 2 X := by
    rw [← oTwoUpper_eq_pResidualOf]
    exact (Subgroup.closure_le _).mpr fun u hu => hno u hu.1 hu.2
  have hXP : X ≤ P := by
    rw [← pResidualOf_sup_eq_of_sylow h.sylow]
    exact sup_le (hL.trans h.core_le) le_rfl
  have hPX : P = X := le_antisymm h.le_self hXP
  obtain ⟨n, hn⟩ := h.sylow.2.1.index ((pCoreOf 2 X).subgroupOf P)
  apply hX n
  have : (pCoreOf 2 X).relIndex P = 2 ^ n := hn
  rw [← this, hPX]

theorem relIndex_core_sylow_dvd (h : PushHyp X P Z) :
    ∃ n : ℕ, (pCoreOf 2 X).relIndex P = 2 ^ n ∧
      (pCoreOf 2 X).relIndex P * P.relIndex X = (pCoreOf 2 X).relIndex X ∧
      ¬ 2 ∣ P.relIndex X := by
  obtain ⟨n, hn⟩ := h.sylow.2.1.index ((pCoreOf 2 X).subgroupOf P)
  exact ⟨n, hn, Subgroup.relIndex_mul_relIndex (pCoreOf 2 X) P X h.core_le h.le_self,
    h.sylow.2.2⟩

end Odd

theorem s3_alg {Z Z₀ : Subgroup G} {d x : G} (hZ₀Z : Z₀ ≤ Z)
    (hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZe : ∀ a ∈ Z, a * a = 1)
    (hdn : d ∈ Subgroup.normalizer (Z : Set G)) (hxn : x ∈ Subgroup.normalizer (Z : Set G))
    (hd0 : ∀ k ∈ Z₀, d * k * d⁻¹ = k) (hx : ∀ z ∈ Z, x * z * x⁻¹ * z⁻¹ ∈ Z₀)
    (hx2 : ∀ z ∈ Z, (x * x) * z = z * (x * x))
    (hd3 : ∀ z ∈ Z, d ^ 3 * z = z * d ^ 3)
    (hq : ∀ z ∈ Z, (x * d * x⁻¹ * d) * z = z * (x * d * x⁻¹ * d)) :
    ∀ z ∈ Z, d * z = z * d := by
  have hcj : ∀ g ∈ Subgroup.normalizer (Z : Set G), ∀ z ∈ Z, g * z * g⁻¹ ∈ Z :=
    fun g hg z hz => (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  have hdi : d⁻¹ ∈ Subgroup.normalizer (Z : Set G) := Subgroup.inv_mem _ hdn
  have E2 : ∀ z ∈ Z, ∃ k ∈ Z₀, d⁻¹ * z * d = d * z * d⁻¹ * k := by
    intro z hz
    have huZ : d * z * d⁻¹ ∈ Z := hcj d hdn z hz
    have haZ : x * z * x⁻¹ ∈ Z := hcj x hxn z hz
    have hvZ : d⁻¹ * z * d ∈ Z := by simpa using hcj d⁻¹ hdi z hz
    have hk₁ := hx z hz
    have hζ : x⁻¹ * z * x = x * z * x⁻¹ := by
      have H := hx2 _ haZ
      calc x⁻¹ * z * x = (x * x)⁻¹ * ((x * z * x⁻¹) * (x * x)) := by group
        _ = (x * x)⁻¹ * ((x * x) * (x * z * x⁻¹)) := by rw [← H]
        _ = x * z * x⁻¹ := by group
    have hmain : x * (d * (x⁻¹ * z * x) * d⁻¹) * x⁻¹ = d⁻¹ * z * d := by
      have e1 : x * (d * (x⁻¹ * z * x) * d⁻¹) * x⁻¹ =
          (x * d * x⁻¹ * d) * (d⁻¹ * z * d) * (x * d * x⁻¹ * d)⁻¹ := by group
      rw [e1, hq _ hvZ]; group
    set k₁ : G := x * z * x⁻¹ * z⁻¹ with hk₁def
    set u : G := d * z * d⁻¹ with hu
    have hk₁Z : k₁ ∈ Z := hZ₀Z hk₁
    have hk₂ := hx k₁ hk₁Z
    have hk₃ := hx u huZ
    set k₂ : G := x * k₁ * x⁻¹ * k₁⁻¹ with hk₂def
    set k₃ : G := x * u * x⁻¹ * u⁻¹ with hk₃def
    have hk₂Z : k₂ ∈ Z := hZ₀Z hk₂
    have hk₃Z : k₃ ∈ Z := hZ₀Z hk₃
    have step1 : d * (x⁻¹ * z * x) * d⁻¹ = k₁ * u := by
      rw [hζ]
      have e : x * z * x⁻¹ = k₁ * z := by rw [hk₁def]; group
      rw [e]
      have := hd0 k₁ hk₁
      calc d * (k₁ * z) * d⁻¹ = (d * k₁ * d⁻¹) * (d * z * d⁻¹) := by group
        _ = k₁ * u := by rw [this]
    have step2 : x * (k₁ * u) * x⁻¹ = (k₂ * k₁) * (k₃ * u) := by
      have e : x * (k₁ * u) * x⁻¹ = (x * k₁ * x⁻¹) * (x * u * x⁻¹) := by group
      rw [e]
      have e2 : x * k₁ * x⁻¹ = k₂ * k₁ := by rw [hk₂def]; group
      have e3 : x * u * x⁻¹ = k₃ * u := by rw [hk₃def]; group
      rw [e2, e3]
    refine ⟨k₂ * k₁ * k₃, Z₀.mul_mem (Z₀.mul_mem hk₂ hk₁) hk₃, ?_⟩
    rw [← hmain, step1, step2]
    have c1 : k₃ * u = u * k₃ := hZc _ hk₃Z _ huZ
    calc k₂ * k₁ * (k₃ * u) = k₂ * k₁ * (u * k₃) := by rw [c1]
      _ = (k₂ * k₁ * u) * k₃ := by group
      _ = (u * (k₂ * k₁)) * k₃ := by rw [hZc _ (Z.mul_mem hk₂Z hk₁Z) _ huZ]
      _ = u * (k₂ * k₁ * k₃) := by group
  intro z hz
  obtain ⟨k, hk, hzk⟩ := E2 z hz
  have hkZ : k ∈ Z := hZ₀Z hk
  have hkk : k * k = 1 := hZe k hkZ
  have hk0 := hd0 k hk
  have hk0' := hd0 k⁻¹ (Z₀.inv_mem hk)
  have h1 : d * d * z * d⁻¹ * d⁻¹ = z * k⁻¹ := by
    have this : d * (d⁻¹ * z * d) * d⁻¹ = d * (d * z * d⁻¹ * k) * d⁻¹ := by rw [hzk]
    have e1 : d * (d⁻¹ * z * d) * d⁻¹ = z := by group
    have e2 : d * (d * z * d⁻¹ * k) * d⁻¹ = (d * d * z * d⁻¹ * d⁻¹) * (d * k * d⁻¹) := by group
    rw [e1, e2, hk0] at this
    calc d * d * z * d⁻¹ * d⁻¹ = (d * d * z * d⁻¹ * d⁻¹ * k) * k⁻¹ := by group
      _ = z * k⁻¹ := by rw [← this]
  have hu : d * z * d⁻¹ = z * k := by
    have h3 := hd3 z hz
    have e3 : d * (d * d * z * d⁻¹ * d⁻¹) * d⁻¹ = d ^ 3 * z * (d ^ 3)⁻¹ := by
      rw [show d ^ 3 = d * d * d by rw [pow_succ, pow_two]]; group
    have e4 : d ^ 3 * z * (d ^ 3)⁻¹ = z := by
      rw [h3]; group
    have e5 : d * (z * k⁻¹) * d⁻¹ = (d * z * d⁻¹) * k⁻¹ := by
      calc d * (z * k⁻¹) * d⁻¹ = (d * z * d⁻¹) * (d * k⁻¹ * d⁻¹) := by group
        _ = (d * z * d⁻¹) * k⁻¹ := by rw [hk0']
    rw [h1, e5, e4] at e3
    calc d * z * d⁻¹ = (d * z * d⁻¹ * k⁻¹) * k := by group
      _ = z * k := by rw [e3]
  have h4 : d * d * z * d⁻¹ * d⁻¹ = z := by
    have e6 : d * d * z * d⁻¹ * d⁻¹ = d * (d * z * d⁻¹) * d⁻¹ := by group
    rw [e6, hu]
    calc d * (z * k) * d⁻¹ = (d * z * d⁻¹) * (d * k * d⁻¹) := by group
      _ = z * k * k := by rw [hu, hk0]
      _ = z := by rw [mul_assoc, hkk, mul_one]
  have hk1 : k = 1 := by
    have : z * k⁻¹ = z := by rw [← h1, h4]
    have h5 : k⁻¹ = 1 := mul_left_cancel (this.trans (mul_one z).symm)
    simpa using h5
  rw [hk1, mul_one] at hu
  calc d * z = (d * z * d⁻¹) * d := by group
    _ = z * d := by rw [hu]

end CFSG.Quasithin.F53Push
