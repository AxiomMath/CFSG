
module

public import CFSG.Sporadic.Schreier.J4SGLBase
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbitsBase
public meta import CFSG.Sporadic.Schreier.J4SOrbitsBase
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
open scoped Matrix

def conjOrbit (L : Subgroup J) (n : J) : Set J := {m | ∃ k ∈ L, m = k * n * k⁻¹}

theorem conj_mem_of_inv_closed {T : Set J}
    (hx : ∀ t ∈ T, x⁻¹ * t * x⁻¹⁻¹ ∈ T) (hy : ∀ t ∈ T, y⁻¹ * t * y⁻¹⁻¹ ∈ T) :
    ∀ k ∈ K, ∀ t ∈ T, k * t * k⁻¹ ∈ T := by
  intro k hk
  rw [K, ← Subgroup.closure_inv] at hk
  have hk' : k ∈ Submonoid.closure ({x, y} : Set J)⁻¹ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite]
    exact hk
  clear hk
  induction hk' using Submonoid.closure_induction with
  | mem g hg =>
    simp only [Set.mem_inv, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with h | h
    · have : g = x⁻¹ := by rw [← h, inv_inv]
      rw [this]
      exact hx
    · have : g = y⁻¹ := by rw [← h, inv_inv]
      rw [this]
      exact hy
  | one => intro t ht; rwa [one_mul, inv_one, mul_one]
  | mul g h _ _ hg hh =>
    intro t ht
    have e : g * h * t * (g * h)⁻¹ = g * (h * t * h⁻¹) * g⁻¹ := by group
    rw [e]
    exact hg _ (hh t ht)

theorem conjOrbit_eq_of_mem {m n : J} (h : m ∈ conjOrbit K n) : conjOrbit K m = conjOrbit K n := by
  obtain ⟨g, hg, rfl⟩ := h
  ext a
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g, K.mul_mem hk hg, by group⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k * g⁻¹, K.mul_mem hk (K.inv_mem hg), by group⟩

end CFSG.Sporadic.J4Schreier
