module

public import CFSG.LocalAnalysis.StandardType.GGFinModelBCTwGen

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section TwLong

theorem ggTwDescent_long
    (f : ℕ) (hf : 1 ≤ f) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (hρ : rho a = a) {y : ModGL (langTag .twistedE6) GGL}
    (hy : y ∈ CFSG.Blueprint.Chevalley.rootSubgroup (langTag .twistedE6) GGL a)
    (hfix : ggPhi .twistedE6 f y = y) :
    ∃ g : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))),
      g ∈ e6Data_valid.rootGroup (GaloisField 2 (2 * f)) a ∧
        sigma (GaloisField 2 (2 * f)) (frobQ 2 f) g = g ∧ ggTwPsi f g = y := by
  obtain ⟨d, hd⟩ :=
    (mem_rootSubgroup (τ := langTag .twistedE6) (R := GGL) (α := a)).1 hy
  have hfix' : ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d) =
      pinnedX (langTag .twistedE6) GGL a d := by
    rw [hd]
    exact hfix
  have hp := ggPhi_pinnedX_twistedE6 (f := f) (γ := a) ha d
  have hρ' : permLattice (TwistTag.perm .E6) a = a := hρ
  have hp' : ggPhi .twistedE6 f (pinnedX (langTag .twistedE6) GGL a d) =
      pinnedX (langTag .twistedE6) GGL a (d ^ 2 ^ f) :=
    hp.trans (congrArg (fun x => pinnedX (langTag .twistedE6) GGL x (d ^ 2 ^ f)) hρ')
  have hkey' : pinnedX (langTag .twistedE6) GGL a (d ^ 2 ^ f) =
      pinnedX (langTag .twistedE6) GGL a d :=
    hp'.symm.trans hfix'
  have hd_pow : d ^ 2 ^ f = d :=
    (pinnedX_injective (τ := langTag .twistedE6) (R := GGL) a) hkey'
  have hpow : (2 : ℕ) ^ f * 2 ^ f = 2 ^ (2 * f) := by
    rw [← pow_add, show f + f = 2 * f by omega]
  have hd2 : d ^ 2 ^ (2 * f) = d := by
    rw [← hpow, pow_mul, hd_pow, hd_pow]
  have hmem : d ∈ Set.range (ggRatEmb (2 * f)) := by
    rw [ggRatEmb_range (f := 2 * f) (by omega)]
    exact hd2
  obtain ⟨c, hc⟩ := hmem
  have hθc : frobQ 2 f c = c := by
    apply (ggRatEmb (2 * f)).injective
    rw [frobQ_apply, map_pow, hc, hd_pow]
  refine ⟨e6Data_valid.xm (GaloisField 2 (2 * f)) a c, ?_, ?_, ?_⟩
  · exact e6Data_valid.xm_mem_rootGroup (GaloisField 2 (2 * f)) a c
  · rw [ggTwSigma_xm f ha c, hρ, hθc]
  · rw [ggTwPsi_xm f ha c, hc]
    exact hd

end TwLong

end CFSG.StandardType.GGFinModel
