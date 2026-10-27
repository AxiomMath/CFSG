module

public import CFSG.RankThree.PartOne.KE.EvenE7E8QPlusWeyl
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KLCE.A2Sector
public import CFSG.RankThree.Chevalley.SteinbergBTTrialitySplitPrimePlane
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCalculus
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.SteinbergBT.TrialityPlane
open CFSG.ComponentClassification.UnbalancedCatalog

section Lattice

@[expose] def g2NegWord : List (Fin Tag.G2.rank) := [g2ia, g2ir, g2ia, g2ir, g2ia, g2ir]

theorem g2_foldr : ∀ k : Fin Tag.G2.rank,
    g2NegWord.foldr (reflect .G2) (Pi.single k 1) = -Pi.single k 1 := by
  unfold g2NegWord g2ia g2ir
  decide +kernel

@[expose] def g2W : WeylGroup Tag.G2 := (coxeterSystem Tag.G2).wordProd g2NegWord

theorem g2W_smul_single (k : Fin Tag.G2.rank) :
    g2W • (Pi.single k 1 : Fin Tag.G2.rank → ℤ) = -Pi.single k 1 := by
  rw [g2W, wordProd_smul]
  exact g2_foldr k

theorem g2W_smul (v : Fin Tag.G2.rank → ℤ) : g2W • v = -v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h : ∀ i, g2W • (v i • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) =
      -(v i • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := fun i => by
    rw [smul_comm g2W (v i), g2W_smul_single, smul_neg]
  calc g2W • v = g2W • ∑ i, v i • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) := by rw [← hv]
    _ = -∑ i, v i • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) := by
        rw [Finset.smul_sum]
        simp only [h, Finset.sum_neg_distrib]
    _ = -v := by rw [← hv]

theorem g2W_mul_self : g2W * g2W = 1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, g2W_smul_single, smul_neg, g2W_smul_single, neg_neg, one_smul]

end Lattice

section Rep

variable (M : Type) [Field M]

@[expose] def g2Rep : ModGL Tag.G2 M := canonicalRep (coxeterSystem Tag.G2) M g2W

variable {M}

theorem g2Rep_mem_monomial : g2Rep M ∈ monomialSubgroup Tag.G2 M :=
  canonicalRep_mem_monomialSubgroup M g2W

theorem g2Rep_mem_adjointGroup : g2Rep M ∈ adjointGroup Tag.G2 M :=
  canonicalRep_mem_adjointGroup _ M g2W

theorem weylQuotientHom_g2Rep :
    weylQuotientHom Tag.G2 M ⟨g2Rep M, g2Rep_mem_monomial⟩ = g2W :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep g2W)

theorem weylQuotientHom_g2Rep_smul (u : Fin Tag.G2.rank → ℤ) :
    weylQuotientHom Tag.G2 M ⟨g2Rep M, g2Rep_mem_monomial⟩ • u = -u := by
  rw [weylQuotientHom_g2Rep, g2W_smul]

variable [CharP M 2]

theorem g2Rep_mul_self : g2Rep M * g2Rep M = 1 := by
  rw [g2Rep, ← qplus_canonicalRep_mul, g2W_mul_self, canonicalRep_one]

theorem g2Rep_conj_pinnedX {α : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) (c : M) :
    g2Rep M * pinnedX Tag.G2 M α c * (g2Rep M)⁻¹ = pinnedX Tag.G2 M (-α) c := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  rw [g2Rep, canonicalRep_mul_pinnedX_mul_inv_of_two h2 g2W hα c, g2W_smul]

end Rep

end CFSG.RankThree.PartOne.TCX.G2
