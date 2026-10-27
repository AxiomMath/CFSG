module

public import CFSG.Quasithin.Background.Harris.R1.SignChoiceL24

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem signRels_of_choice {z : G} {σ : Ω → G} (hz : z ∈ Zs)
    {i₀ j₀ : Ω} (hij₀ : i₀ ≠ j₀) (hzcm : z = C.cm i₀ j₀) (hσ : IsSignChoice C z σ) :
    (∀ ω, σ ω * σ ω = 1) ∧ (∀ ω, z * σ ω = σ ω * z) ∧
      ∀ ω ω' : Ω, ω ≠ ω' → σ ω * σ ω' * (σ ω * σ ω') = z := by
  refine ⟨fun ω => hσ.sq_eq_one C hz ω, fun ω => ?_, fun ω ω' h => hσ.pair_sq C hz hij₀ hzcm h⟩
  exact (C.Zs_central (hσ.mem_vBeta C hz ω) hz).symm

end CFSG.Quasithin.Background.Harris.R1
