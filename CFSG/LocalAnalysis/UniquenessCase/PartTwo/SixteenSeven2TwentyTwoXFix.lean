module

public import CFSG.Quasithin.Background.E3Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {G : Type} [Group G]

theorem s16c167_twenty_two_x_triv {M : Subgroup G} {I : Fin 3 → Subgroup G}
    {ρ : ↥M →* Equiv.Perm (Fin 3)} (hinj : Function.Injective I)
    (hconj : ∀ (m : ↥M) (i : Fin 3), conjSubgroup (I i) (m : G)⁻¹ = I (ρ m i))
    {i i' : Fin 3} (hii' : i ≠ i') {g u : G} (hu : u ^ 2 = 1) (huM : g * u * g⁻¹ ∈ M)
    (h : conjSubgroup (conjSubgroup (I i) g) u = conjSubgroup (I i) g)
    (h' : conjSubgroup (conjSubgroup (I i') g) u = conjSubgroup (I i') g) :
    ∃ m : ↥M, (m : G) = g * u * g⁻¹ ∧ m ^ 2 = 1 ∧ ρ m = 1 := by
  have hperm : ∀ σ : Equiv.Perm (Fin 3), ∀ a b : Fin 3, a ≠ b → σ a = a → σ b = b → σ = 1 := by
    decide
  have hu2 : (g * u * g⁻¹) * (g * u * g⁻¹) = 1 := by
    have : (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
    rw [this, ← sq, hu]
    group
  let m : ↥M := ⟨g * u * g⁻¹, huM⟩
  have hm2 : m ^ 2 = 1 := Subtype.ext (by simpa [m, sq] using hu2)
  have hminv : (m : G)⁻¹ = (m : G) := inv_eq_of_mul_eq_one_right hu2
  have hfix : ∀ k : Fin 3, conjSubgroup (conjSubgroup (I k) g) u = conjSubgroup (I k) g →
      ρ m k = k := by
    intro k hk
    rw [conjSubgroup_conjSubgroup] at hk
    have h1 : conjSubgroup (conjSubgroup (I k) (g * u * g⁻¹)) g = conjSubgroup (I k) g := by
      rw [conjSubgroup_conjSubgroup, show g * u * g⁻¹ * g = g * u by group]
      exact hk
    have h2 : conjSubgroup (I k) (g * u * g⁻¹) = I k := by
      have := congrArg (fun C => conjSubgroup C g⁻¹) h1
      simpa only [E3.conjSubgroup_conj_inv] using this
    have h3 : I (ρ m k) = I k := by
      rw [← hconj m k, hminv]
      exact h2
    exact hinj h3
  exact ⟨m, rfl, hm2, hperm _ i i' hii' (hfix i h) (hfix i' h')⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
