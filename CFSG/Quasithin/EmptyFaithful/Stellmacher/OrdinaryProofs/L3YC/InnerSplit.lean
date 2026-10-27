module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

theorem S_eq_mul_centralizer_mod_normal {H : Type*} [Group H] (S L : Subgroup H)
    (N : Subgroup H)
    (hNL : ∀ x ∈ L, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hSL : ∀ s ∈ S, ∀ x ∈ L, s * x * s⁻¹ ∈ L)
    (hSN : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N)
    (hinn : ∀ s ∈ S, ∃ l ∈ L, ∀ x ∈ L, ∃ n ∈ N, s * x * s⁻¹ = l * x * l⁻¹ * n)
    (hself : ∀ l ∈ L, (∀ p ∈ S ⊓ L, ∃ q ∈ S ⊓ L, ∃ n ∈ N, l * p * l⁻¹ = q * n) →
      ∃ q ∈ S ⊓ L, ∃ n ∈ N, l = q * n) :
    ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S, (∀ x ∈ L, ∃ m ∈ N, c * x * c⁻¹ = x * m) ∧ s = p * c := by
  intro s hs
  obtain ⟨l, hl, hlx⟩ := hinn s hs
  have hlNorm : ∀ p ∈ S ⊓ L, ∃ q ∈ S ⊓ L, ∃ n ∈ N, l * p * l⁻¹ = q * n := by
    intro p hp
    obtain ⟨hpS, hpL⟩ := Subgroup.mem_inf.mp hp
    obtain ⟨n, hn, hsp⟩ := hlx p hpL
    refine ⟨s * p * s⁻¹, Subgroup.mem_inf.mpr ⟨S.mul_mem (S.mul_mem hs hpS) (S.inv_mem hs),
      hSL s hs p hpL⟩, n⁻¹, N.inv_mem hn, ?_⟩
    rw [show s * p * s⁻¹ = l * p * l⁻¹ * n from hsp]
    group
  obtain ⟨q₀, hq₀, n₀, hn₀, hl_eq⟩ := hself l hl hlNorm
  obtain ⟨hq₀S, hq₀L⟩ := Subgroup.mem_inf.mp hq₀
  refine ⟨q₀, hq₀, q₀⁻¹ * s, S.mul_mem (S.inv_mem hq₀S) hs, ?_, by group⟩
  intro x hx
  obtain ⟨nx, hnx, hsx⟩ := hlx x hx
  have h1 : x⁻¹ * n₀ * x ∈ N := by
    have := hNL x⁻¹ (L.inv_mem hx) n₀ hn₀
    simpa using this
  have h2 : q₀⁻¹ * nx * q₀⁻¹⁻¹ ∈ N := hSN q₀⁻¹ (S.inv_mem hq₀S) nx hnx
  refine ⟨(x⁻¹ * n₀ * x * n₀⁻¹) * (q₀⁻¹ * nx * q₀), N.mul_mem
    (N.mul_mem h1 (N.inv_mem hn₀)) (by simpa using h2), ?_⟩
  rw [show (q₀⁻¹ * s) * x * (q₀⁻¹ * s)⁻¹ = q₀⁻¹ * (s * x * s⁻¹) * q₀ by group, hsx, hl_eq]
  group

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

end
