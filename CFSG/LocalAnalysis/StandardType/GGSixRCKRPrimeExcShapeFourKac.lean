module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourCount
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.GGFinModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem kacCount_E8_four_ne48 : ∀ C : Finset (Option (Fin Tag.E8.rank)), C.card = 4 →
    kacCount .E8 ![2, 3, 4, 6, 5, 4, 3, 2] C ≠ 48 := by
  decide +kernel

theorem rck_natCast_ne_zero_GGL {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (p : GGL) ≠ 0 := by
  intro h
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).1 h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm

theorem rckExc_kac_comp
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E8.rank → GGLˣ}
    (hpa : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a)) :
    ∃ (v : WeylGroup Tag.E8) (C : Finset (Option (Fin Tag.E8.rank))),
      componentRoots (rootCharHom a) i = (fun α => v • α) '' kacE8.rootsOf (C : Set _) ∧
        compRank (componentRoots (rootCharHom a) i) = C.card ∧
        (componentRoots (rootCharHom a) i).ncard = kacCount Tag.E8 kacE8.θ C := by
  obtain ⟨v, μ, -, hall⟩ := exists_pinnedT_of_pos (K := kacE8) hp.pos
    (rck_natCast_ne_zero_GGL hp hp2) facts_E8 hpa
  obtain ⟨x, C, -, -, hroots, hrank, hncard⟩ := hall i
  exact ⟨v, C, hroots, hrank, hncard⟩

theorem rckExc_not_shape_F4
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E8.rank → GGLˣ}
    (hpa : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 4 ∧
      (componentRoots (rootCharHom a) i).ncard = 48) := by
  rintro ⟨hr, hc⟩
  obtain ⟨v, C, -, hrank, hncard⟩ := rckExc_kac_comp hp hp2 hpa i
  exact kacCount_E8_four_ne48 C (hrank.symm.trans hr) (hncard.symm.trans hc)

end CFSG.StandardType.RCKRP
