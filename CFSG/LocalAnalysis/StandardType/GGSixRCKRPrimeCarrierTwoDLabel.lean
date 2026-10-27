module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDFourGraph
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDLabel
public import CFSG.Blueprint.LieModelAPI
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.PsuGoodAux.Descent
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Defs
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Layer
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.Models
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenAsm
public import CFSG.HardMathSupport.Solomon.Coordinator.LBIInput6_1Main
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame.SuN
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcActOuterPerfTwoDRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S4S.I145GW
public import CFSG.LocalAnalysis.GLTheoremA.S4S.KData
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
public import CFSG.Models.Transport
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Spin CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.LocalAnalysis.GLTheoremA.T171Sh


private theorem rckTwoD_forkLabelling_reindex
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} {δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ)}
    (e : simpleRoots Ψ ≃ Fin 4)
    (he : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      CartanMatrix.D 4 (e β) (e γ))
    (σ : Equiv.Perm (Fin 4)) (hσ : ∀ j, δ (e.symm j) = e.symm (σ j))
    (π : Equiv.Perm (Fin 4))
    (hπ : ∀ i j, d4Fun (π i) (π j) = d4Fun i j)
    (hinter : ∀ j, σ (π j) = π (Equiv.swap (2 : Fin 4) 3 j)) :
    ∃ ε : simpleRoots Ψ ≃ Fin 4, CompsPTwoDLabel.IsForkLabelling Ψ δ ε := by
  let ε : simpleRoots Ψ ≃ Fin 4 := e.trans π.symm
  have hM : ∀ β γ : simpleRoots Ψ, corootPair (β : Fin τ.rank → ℤ) γ =
      cartanD 4 (ε β) (ε γ) := by
    intro β γ
    rw [he]
    have h := hπ (π.symm (e β)) (π.symm (e γ))
    simpa only [ε, Equiv.trans_apply, Equiv.apply_symm_apply, cartanD_eq, d4Fun] using h
  have hδ : ∀ j, δ (ε.symm j) = ε.symm (Equiv.swap (2 : Fin 4) 3 j) := by
    intro j
    change δ (e.symm (π j)) = e.symm (π (Equiv.swap (2 : Fin 4) 3 j))
    rw [hσ, hinter]
  exact ⟨ε, CompsPTwoDLabel.isForkLabelling_of_swap ε hM 2 3 (by decide) (by decide) hδ⟩

theorem rckTwoD_forkLabelling_four
    {τ : Tag} {Ψ : Set (Fin τ.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    (hsl : ∀ β ∈ Ψ, iform β β = 2) (hrank : compRank Ψ = 4)
    (hcard : Ψ.ncard = 2 * compRank Ψ * (compRank Ψ - 1))
    (δ : (Fin τ.rank → ℤ) →+ (Fin τ.rank → ℤ))
    (hiso : ∀ x y, iform (δ x) (δ y) = iform x y)
    (hmaps : ∀ γ ∈ Ψ, δ γ ∈ Ψ) (hpos : ∀ γ ∈ posRoots Ψ, δ γ ∈ posRoots Ψ)
    (hinvol : ∀ γ ∈ Ψ, δ (δ γ) = γ)
    (hne : ∃ β ∈ simpleRoots Ψ, δ β ≠ β) :
    ∃ ε : simpleRoots Ψ ≃ Fin 4, CompsPTwoDLabel.IsForkLabelling Ψ δ ε := by
  obtain ⟨e, σ, he, hσ, hσM, hσ2, hσne⟩ :=
    exists_graphCoordinates_of_rankFour hΨ hsl hrank hcard δ hiso hmaps hpos hinvol hne
  rcases d4_perm_cases hσM hσ2 with hid | h02 | h03 | h23
  · exact False.elim (hσne (Equiv.ext hid))
  · have hs : σ = Equiv.swap (0 : Fin 4) 2 := Equiv.ext h02
    exact rckTwoD_forkLabelling_reindex e he σ hσ (Equiv.swap (0 : Fin 4) 3)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
      (by rw [hs]; decide +kernel)
  · have hs : σ = Equiv.swap (0 : Fin 4) 3 := Equiv.ext h03
    exact rckTwoD_forkLabelling_reindex e he σ hσ (Equiv.swap (0 : Fin 4) 2)
      (by intro i j; fin_cases i <;> fin_cases j <;> decide +kernel)
      (by rw [hs]; decide +kernel)
  · have hs : σ = Equiv.swap (2 : Fin 4) 3 := Equiv.ext h23
    exact rckTwoD_forkLabelling_reindex e he σ hσ 1
      (by intro i j; rfl) (by rw [hs]; decide +kernel)

end CFSG.StandardType.RCKRP
