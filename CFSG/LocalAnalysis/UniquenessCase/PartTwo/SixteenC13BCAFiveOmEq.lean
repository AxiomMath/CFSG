module

public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin.G11.P3Ortho.Om4

theorem s16c13bcA_card_sl2_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 60 := by
  classical
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [Matrix.card_SL_field, Fin.prod_univ_two, hq]
  norm_num

theorem s16c13bcA_omega_equiv_apply {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    ∃ ε : ↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
        (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K),
      ∀ (γ : ↥(StatedOmega (StatedQuadPlus 2 K))) (v : Fin 2 ⊕ Fin 2 → K),
        toMat K (((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) K) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
          ((ε γ).1 : Matrix (Fin 2) (Fin 2) K) * toMat K v *
            (((ε γ).2⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  let e1 := (Ψ K).subgroupMap (StatedOmega (StatedQuadPlus 2 K))
  let e2 := MulEquiv.subgroupCongr
    (show (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom = (rho' K).range by
      rw [map_statedOmega, commutator_eq_range h4])
  let e3 := (MonoidHom.ofInjective (rho'_injective (K := K))).symm
  refine ⟨e1.trans (e2.trans e3), fun γ v => ?_⟩
  have hρ : rho' K ((e1.trans (e2.trans e3)) γ) = Ψ K (γ : GL (Fin 2 ⊕ Fin 2) K) := by
    have h1 := MonoidHom.apply_ofInjective_symm (rho'_injective (K := K)) (e2 (e1 γ))
    exact h1
  have h2 := Ψ_apply K (γ : GL (Fin 2 ⊕ Fin 2) K) (toMat K v)
  rw [LinearEquiv.symm_apply_apply] at h2
  rw [← h2, ← hρ]
  rfl

theorem s16c13bcA_card_omega_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) : Nat.card ↥(StatedOmega (StatedQuadPlus 2 K)) = 3600 := by
  obtain ⟨ε, -⟩ := s16c13bcA_omega_equiv_apply hK.ge
  rw [Nat.card_congr ε.toEquiv, Nat.card_prod, s16c13bcA_card_sl2_four hK]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
