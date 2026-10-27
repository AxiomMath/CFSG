module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteen
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Center
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Models.Transport
public import CFSG.RankThree.PartOne.KE.TitsPlaneLocalCores

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

theorem k_catalogModels_holds :
    K_CatalogModels := by
  constructor
  · intro X _ r h
    obtain ⟨idx, ⟨e⟩, hidx⟩ := h
    obtain ⟨t, n, p, f, hp, hm⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_lieModel_char idx
    have hm' : CFSG.Models.LieModel X t n p f :=
      CFSG.Models.LieModel.of_mulEquiv e.symm hm
    have hp' : p = r := hp.trans hidx
    subst hp'
    exact ⟨t, n, f, hm'.1,
      CFSG.HardMathSupport.Timmesfeld.Tables.T1b.blueprintLieModel_of_models hm'⟩
  · intro X _ s h
    obtain ⟨e⟩ := h
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group s
    exact ⟨e.trans b.symm⟩

section TitsOddPrimes


theorem k_titsOddPrimes_holds : K_TitsOddPrimes := by
  intro X _ _ hT hC q hq hq2 hdvd
  haveI : (CFSG.Open.genFittingFStar X).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal X
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1
    (CFSG.Blueprint.LieModel.reeTitsModel hT (by decide)).2
  have hinj : Function.Injective (MulAut.conjNormal (H := CFSG.Open.genFittingFStar X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro g hg
    have hg1 : MulAut.conjNormal (H := CFSG.Open.genFittingFStar X) g = 1 := hg
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hgh : g * h * g⁻¹ = h := by
      have h2 := congrArg (fun σ : MulAut ↥(CFSG.Open.genFittingFStar X) =>
        ((σ ⟨h, hh⟩ : ↥(CFSG.Open.genFittingFStar X)) : X)) hg1
      simpa [MulAut.conjNormal_apply] using h2
    calc h * g = (g * h * g⁻¹) * g := by rw [hgh]
      _ = g * h := by group
  have hcard : q ∣ 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 13 := by
    have h1 := Subgroup.card_dvd_of_injective _ hinj
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      CFSG.RankThree.PartOne.KE.card_mulAut_titsD] at h1
    exact hdvd.trans (h1.trans (by norm_num))
  rcases (Nat.Prime.dvd_mul hq).1 hcard with h1 | h1
  · rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hq).1 h2 with h3 | h3
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h3))
          hq2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 (hq.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h1))

end TitsOddPrimes

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
