module

public import CFSG.SignalizerFunctorTheorem.NonLocal.Heisenberg
public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV

public section

open scoped commutatorElement IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.NonLocal

theorem pow_le_card_of_heisenberg {X Γ : Type*} [Group X] [Group Γ] (φ : Γ →* X)
    (V : Subgroup X) [Finite V] [IsMulCommutative V] {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (hexp : ∀ v ∈ V, v ^ s = 1)
    (hnorm : ∀ g : Γ, ∀ v ∈ V, φ g * v * (φ g)⁻¹ ∈ V)
    (A Z : Subgroup Γ) [Finite A] (hA : IsMulCommutative A) (hArp : IsPGroup r A) (hZA : Z ≤ A)
    {ι : Type*} [Finite ι] (y : ι → Γ) (hcomm : ∀ i, ∀ a ∈ A, ⁅(y i)⁻¹, a⁆ ∈ Z)
    (hZact : ∃ z ∈ Z, ∃ v ∈ V, φ z * v * (φ z)⁻¹ ≠ v)
    (hdist : ∀ (F : Type) [Field F] [CharP F s], ∀ ξ : Γ → F,
      (∀ z ∈ Z, ∀ z' ∈ Z, ξ (z * z') = ξ z * ξ z') → (∀ z ∈ Z, ξ z ≠ 0) →
      (∃ z ∈ Z, ξ z ≠ 1) → ∀ i j, i ≠ j → ∃ a ∈ A, ξ ⁅(y i)⁻¹, a⁆ ≠ ξ ⁅(y j)⁻¹, a⁆) :
    s ^ Nat.card ι ≤ Nat.card V := by
  have : Fact s.Prime := ⟨hs⟩
  have : Fact r.Prime := ⟨hr⟩
  let F := AlgebraicClosure (ZMod s)
  obtain ⟨m, ρ, hcard, hfaith⟩ := exists_rep_of_elementary_abelian φ V hs hexp hnorm F
  have hinv : (Nat.card A : F) ≠ 0 := by
    obtain ⟨k, hk⟩ := hArp.exists_card_eq
    rw [hk, Ne, CharP.cast_eq_zero_iff F s]
    intro h
    exact hrs ((Nat.prime_dvd_prime_iff_eq hs hr).mp (hs.dvd_of_dvd_pow h)).symm
  have hnt : ∃ z ∈ Z, ρ z ≠ 1 := by
    obtain ⟨z, hz, v, hv, hne⟩ := hZact
    exact ⟨z, hz, fun h => hne (hfaith z h v hv)⟩
  have hb := card_le_finrank_of_translations ρ A Z hA hinv hZA y
    (fun i a ha => hcomm i a ha) hnt (fun ξ h1 h2 h3 _ i j hij => hdist F ξ h1 h2 h3 i j hij)
  rw [Module.finrank_fin_fun] at hb
  rw [hcard]
  exact Nat.pow_le_pow_right hs.pos hb

end CFSG.SignalizerFunctorTheorem.NonLocal
