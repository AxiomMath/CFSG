module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreFrob

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 Equiv
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
variable {L : Subgroup (V ≃ₗ[F] V)} {pt : Fin 6 → ℙ F V}

theorem IsSixOrbit.exists_induces [Finite F] [FiniteDimensional F V] (hF : Nat.card F = 4)
    (hV : Module.finrank F V = 3) (hO : IsSixOrbit L pt)
    (hirr : ∀ W : Submodule F V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (σ : Perm (Fin 6)) : ∃ n : gammaL F V, ∀ i, pointAct n (pt i) = pt (σ i) := by
  obtain ⟨n₀, hn₀⟩ := hO.exists_swap hF hV hirr
  by_cases hσ : σ ∈ alternatingGroup (Fin 6)
  · obtain ⟨g, -, hg⟩ := (hO.alt σ).1 hσ
    exact ⟨toGamma F V g, hg⟩
  · have hodd : Perm.sign σ = -1 := by
      rcases Int.units_eq_one_or (Perm.sign σ) with h | h
      · exact absurd (Perm.mem_alternatingGroup.2 h) hσ
      · exact h
    have hev : σ * swap 4 5 ∈ alternatingGroup (Fin 6) := by
      rw [Perm.mem_alternatingGroup, map_mul, hodd, Perm.sign_swap (by decide)]
      decide
    obtain ⟨g, -, hg⟩ := (hO.alt _).1 hev
    refine ⟨toGamma F V g * n₀, fun i => ?_⟩
    rw [pointAct_mul, hn₀]
    change lineAction F V g (pt (swap 4 5 i)) = _
    rw [hg]
    simp

end CFSG.Quasithin.D35Core
