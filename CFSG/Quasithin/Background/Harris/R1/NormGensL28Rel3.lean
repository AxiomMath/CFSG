module

public import CFSG.Quasithin.Background.Harris.R1.NormGensL28

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  [Fintype Ω] [DecidableEq Ω] (C : FamCtx K1 L2 S Zs Ω)

omit [Fintype Ω] [DecidableEq Ω] in
theorem rel11_of_sign {z : G} {σ : Ω → G} (hz : z ∈ Zs)
    {i₀ j₀ : Ω} (hij₀ : i₀ ≠ j₀) (hzcm : z = C.cm i₀ j₀) (hσ : IsSignChoice C z σ)
    {a : G} (ha : a ∈ signStab C σ) (haB : a ∉ borelOf K1 S) :
    σ C.D.pt * (a * σ C.D.pt * a⁻¹) * (σ C.D.pt)⁻¹ * (a * σ C.D.pt * a⁻¹)⁻¹ = z := by
  obtain ⟨hK, hrel⟩ := ha
  have hne : C.D.pt ≠ C.D.act ⟨a, hK⟩ C.D.pt := fun h =>
    haB ((C.D.stab ⟨a, hK⟩).1 h.symm)
  obtain ⟨hsq1, -, hpair⟩ := signRels_of_choice C hz hij₀ hzcm hσ
  have hy : a * σ C.D.pt * a⁻¹ = σ (C.D.act ⟨a, hK⟩ C.D.pt) := hrel C.D.pt
  have hx : (σ C.D.pt)⁻¹ = σ C.D.pt := inv_eq_of_mul_eq_one_right (hsq1 _)
  have hy' : (σ (C.D.act ⟨a, hK⟩ C.D.pt))⁻¹ = σ (C.D.act ⟨a, hK⟩ C.D.pt) :=
    inv_eq_of_mul_eq_one_right (hsq1 _)
  rw [hy, hx, hy']
  simpa only [mul_assoc] using hpair C.D.pt (C.D.act ⟨a, hK⟩ C.D.pt) hne

end CFSG.Quasithin.Background.Harris.R1

end
