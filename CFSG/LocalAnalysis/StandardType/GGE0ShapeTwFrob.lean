module

public import CFSG.LocalAnalysis.StandardType.GGE0ShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGE0ShapeContextRankAux
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcRoots

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem twisted_frobenius_form
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    (S : LangSetup .E6 Ω 5) (hs : ∀ α, S.ρ α = -α) :
    ∃ Fr : Ω →+* Ω, (∀ c, Fr c = c ^ S.D.q) ∧ S.D.Φ = twistHom TwistTag.E6 Ω Fr := by
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  rcases hP with rfl | ⟨t, ht, rfl⟩
  ·
    exfalso
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
      ext g
      rw [hΦ g, one_mul, inv_one, mul_one]
    obtain ⟨γ, hγ, hne⟩ := no_weyl_neg_one_E6 w
    have h1 : S.ρ γ = w • γ := S.rho_eq_smul_of_frob hFr hΦ' hn hγ
    exact hne (by rw [← h1, hs γ])
  ·
    refine ⟨Fr, hFr, ?_⟩
    cases t with
    | E6 =>
        cases ht
        ext g
        rw [hΦ g]
        rfl
    | D4 => exact absurd ht (by decide)

end CFSG.StandardType
