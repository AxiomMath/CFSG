module

public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LocalAnalysis.StandardType.PhanEStdFrob

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6

variable {k : Type} [Field k] (θ : k →+* k)

@[expose] noncomputable def e6FrobData (hθ : ∀ c, θ (θ c) = c)
    {w₀ : (coxeterMatrix (e6Datum k).isFiniteType).Group}
    (hop : ∀ i, w₀ * (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem.simple i * w₀ =
      (coxeterMatrix (e6Datum k).isFiniteType).toCoxeterSystem.simple (rhoPerm i)) :
    FrobData (e6Datum k) (e6Data_valid.nm k) (e6Data_valid.torus k) w₀ where
  φ := sigma k θ
  invol := sigma_sigma θ hθ
  op := rhoPerm
  hop := hop
  pos := by
    rintro _ ⟨u, hu, rfl⟩
    exact (isTwist_sigma θ).map_posUnipotent hu
  torus := by
    rintro _ ⟨t, ht, rfl⟩
    exact (isTwist_sigma θ).map_iSup_torus ht
  n_map i := sigma_nm θ i

theorem sigma_xm_charTwo [CharP k 2] {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    sigma k θ (e6Data_valid.xm k γ c) = e6Data_valid.xm k (rho γ) (θ c) := by
  rw [sigma_xm θ hγ]
  rcases twistSign_eq_one_or γ with h | h <;> simp [h, CharTwo.neg_eq]

end CFSG.ClassicalInvolution.Phan.PhanE
