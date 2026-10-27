module

public import CFSG.Quasithin.EmptyFaithful.R3c13Def
public import CFSG.Quasithin.EmptyFaithful.R3c12Syl

public section

namespace CFSG.Quasithin.R3c13

section Gen

variable {X : Type} [Group X]

theorem klein_comm {V : Subgroup X} (hV2 : ∀ v ∈ V, v * v = 1) :
    ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := by
  intro u hu v hv
  have h1 : u * v * (u * v) = 1 := hV2 _ (V.mul_mem hu hv)
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hV2 u hu)
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hV2 v hv)
  have hinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right h1
  calc u * v = (u * v)⁻¹ := hinv.symm
    _ = v⁻¹ * u⁻¹ := mul_inv_rev _ _
    _ = v * u := by rw [hu', hv']

theorem kleinSelfCent_core (a₀ : X) (cands : List X)
    (hcands : ∀ y : X, y * y = 1 → y ≠ 1 → y ≠ a₀ → y * a₀ = a₀ * y → y ∈ cands)
    (hcent : ∀ u ∈ cands, ∀ g : X, g * a₀ = a₀ * g → g * u = u * g →
      g = 1 ∨ g = a₀ ∨ g = u ∨ g = a₀ * u)
    {V : Subgroup X} (ha₀ : a₀ ∈ V) (ha01 : a₀ ≠ 1) (hV4 : Nat.card V = 4)
    (hV2 : ∀ v ∈ V, v * v = 1) {g : X} (hg : ∀ v ∈ V, g * v = v * g) : g ∈ V := by
  obtain ⟨u, huV, hu1, hua, -⟩ := R3c12.klein_elems hV4 hV2 ha₀ ha01
  have huc : u * a₀ = a₀ * u := klein_comm hV2 u huV a₀ ha₀
  have hu := hcands u (hV2 u huV) hu1 hua huc
  rcases hcent u hu g (hg a₀ ha₀) (hg u huV) with h | h | h | h
  · rw [h]
    exact V.one_mem
  · rw [h]
    exact ha₀
  · rw [h]
    exact huV
  · rw [h]
    exact V.mul_mem ha₀ huV

theorem kleinSelfCent_of_conj (a₀ : X) (ha01 : a₀ ≠ 1) (cands : List X)
    (hconj : ∀ a : X, a ≠ 1 → a * a = 1 → ∃ ρ : X, ρ * a = a₀ * ρ)
    (hcands : ∀ y : X, y * y = 1 → y ≠ 1 → y ≠ a₀ → y * a₀ = a₀ * y → y ∈ cands)
    (hcent : ∀ u ∈ cands, ∀ g : X, g * a₀ = a₀ * g → g * u = u * g →
      g = 1 ∨ g = a₀ ∨ g = u ∨ g = a₀ * u) : KleinSelfCent X := by
  intro V hV4 hV2 g hg
  obtain ⟨a, haV, ha1⟩ : ∃ a ∈ V, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Nat.card V = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩, ⟨1⟩⟩
    omega
  obtain ⟨ρ, hρ⟩ := hconj a ha1 (hV2 a haV)
  have hρa : ρ * a * ρ⁻¹ = a₀ := by
    rw [hρ]
    group
  set V₁ : Subgroup X := V.map (MulAut.conj ρ).toMonoidHom with hV₁
  have ha₀ : a₀ ∈ V₁ := ⟨a, haV, by simpa [MulAut.conj_apply] using hρa⟩
  have hV₁4 : Nat.card V₁ = 4 := by
    rw [← hV4]
    exact (Nat.card_congr (V.equivMapOfInjective (MulAut.conj ρ).toMonoidHom
      (MulAut.conj ρ).injective).toEquiv).symm
  have hV₁2 : ∀ v ∈ V₁, v * v = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    show (MulAut.conj ρ) v * (MulAut.conj ρ) v = 1
    rw [← map_mul, hV2 v hv, map_one]
  have ha₀1 : a₀ ≠ 1 := ha01
  have hg₁ : ∀ v ∈ V₁, ρ * g * ρ⁻¹ * v = v * (ρ * g * ρ⁻¹) := by
    rintro _ ⟨v, hv, rfl⟩
    show ρ * g * ρ⁻¹ * ((MulAut.conj ρ) v) = ((MulAut.conj ρ) v) * (ρ * g * ρ⁻¹)
    simp only [MulAut.conj_apply]
    calc ρ * g * ρ⁻¹ * (ρ * v * ρ⁻¹) = ρ * (g * v) * ρ⁻¹ := by group
      _ = ρ * (v * g) * ρ⁻¹ := by rw [hg v hv]
      _ = ρ * v * ρ⁻¹ * (ρ * g * ρ⁻¹) := by group
  have hmem := kleinSelfCent_core a₀ cands hcands hcent ha₀ ha₀1 hV₁4 hV₁2 hg₁
  obtain ⟨v, hv, hvg⟩ := hmem
  have hvg' : ρ * v * ρ⁻¹ = ρ * g * ρ⁻¹ := by simpa [MulAut.conj_apply] using hvg
  have : v = g := by
    have h1 : ρ⁻¹ * (ρ * v * ρ⁻¹) * ρ = ρ⁻¹ * (ρ * g * ρ⁻¹) * ρ := by rw [hvg']
    simpa using h1
  rw [← this]
  exact hv

end Gen

end CFSG.Quasithin.R3c13
