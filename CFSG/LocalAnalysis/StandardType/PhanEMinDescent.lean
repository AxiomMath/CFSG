module

public import CFSG.LocalAnalysis.StandardType.PhanEMinFrob

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Blueprint.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {k₀ k : Type} [Field k₀] [Field k]

private theorem q2nPE_minEndBC_injective {d : ℕ} {k k' : Type} [Field k] [Field k']
    (ι : k →+* k') : Function.Injective (minEndBC (d := d) ι) := by
  intro A B h
  refine minEnd_ext fun b => Finsupp.ext fun c => ?_
  have h1 := congrArg (fun f : Module.End k' (Fin d →₀ k') => f (Finsupp.single b 1) c) h
  simp only [minEndBC_single, Finsupp.mapRange_apply] at h1
  exact ι.injective h1

theorem minBC_injective' (ι : k₀ →+* k) : Function.Injective (minBC hV ι) := by
  intro g h e
  apply Subtype.ext
  apply Units.ext
  apply q2nPE_minEndBC_injective (d := D.d) ι
  exact congrArg (fun x : hV.minGroup k => ((x : (Module.End k (Fin D.d →₀ k))ˣ) :
    Module.End k (Fin D.d →₀ k))) e

theorem minBC_fixed (θ : k →+* k) (ι : k₀ →+* k) (hι : ∀ c, θ (ι c) = ι c)
    (y : hV.minGroup k₀) : minBC hV θ (minBC hV ι y) = minBC hV ι y := by
  have h : (minBC hV θ).comp (minBC hV ι) = minBC hV ι := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LieType.Steinberg.Isogeny.closure_xm_simple_eq_top hV k₀) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · show minBC hV θ (minBC hV ι (hV.xm k₀ (Pi.single i 1) c)) =
        minBC hV ι (hV.xm k₀ (Pi.single i 1) c)
      rw [minBC_xm, minBC_xm, hι c]
    · show minBC hV θ (minBC hV ι (hV.xm k₀ (-Pi.single i 1) c)) =
        minBC hV ι (hV.xm k₀ (-Pi.single i 1) c)
      rw [minBC_xm, minBC_xm, hι c]
  exact DFunLike.congr_fun h y

theorem minBC_descent_rootGroup (θ : k →+* k) (ι : k₀ →+* k)
    (hdesc : ∀ c, θ c = c → ∃ c', ι c' = c) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    {x : hV.minGroup k} (hx : x ∈ hV.rootGroup k γ) (hfix : minBC hV θ x = x) :
    x ∈ (minBC hV ι).range := by
  obtain ⟨c, rfl⟩ := (hV.mem_rootGroup k).1 hx
  have hc : θ c = c :=
    hV.xm_injective k hγ ((minBC_xm hV θ γ c).symm.trans hfix)
  obtain ⟨c', hc'⟩ := hdesc c hc
  refine MonoidHom.mem_range.2 ⟨hV.xm k₀ γ c', ?_⟩
  rw [minBC_xm, hc']

end CFSG.ClassicalInvolution.Phan.PhanE
