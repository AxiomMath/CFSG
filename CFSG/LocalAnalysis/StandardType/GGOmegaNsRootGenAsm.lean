module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenFrame
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenCoherent
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsmA
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenGenA
import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenAsmB
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentType
import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.GroupTheory.WeirSylow.OrthogonalTypes
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
import CFSG.Holt.Fixed
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLInner
import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.RankThree.PartOne.FOC.CompCommutator
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open QuadraticMap CFSG.RankThree.Classical2 CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

theorem ggTorusModelAt_of_selfCentralizing (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ) {E : Subgroup ↥(orthDerived Q)}
    (hE : CFSG.Open.IsElemAbelian p E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    GGTorusModelAt p E := by
  obtain ⟨k, U, e, hF, hcase⟩ :=
    exists_planeFrame_of_selfCentralizing hQ hp hp2 hpq hdim (by omega) hE hsc
  rcases hcase with ⟨hk, htop⟩ | ⟨hk, f, f', hf, hf', hQf, hQf', hff'⟩
  · obtain ⟨e', u, c, t, hC, -⟩ := exists_coherentFrame hF hp hp2 hpq (by omega)
    exact ggTorusModelAt_of_coherentFrame_of_iSup_pairBlock hQ hp hp2 hpq hF4 hdim hℓ hk hC
      fun x₀ => iSup_pairBlock_ne_eq_top hQ hp hp2 hpq hF4 (by omega) hC htop x₀
  · obtain ⟨e', u, c, t, hC, -⟩ := exists_coherentFrame hF hp hp2 hpq (by omega)
    exact ggTorusModelAt_of_coherentFrame_hyp hQ hp hp2 hpq hF4 hdim hℓ hk hC hf hf' hQf hQf'
      hff'

theorem ggTorusRootGenAvoidKG_orthDerived (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {ℓ : ℕ}
    (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ)
    (hinj : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* ↥(orthDerived Q)),
      Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        Function.Injective ψ) (r : ℕ) :
    GGTorusRootGenAvoidKG p r ↥(orthDerived Q)
      (Set.range (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q))) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (by rw [hdim]; omega)
  have hZ : Subgroup.center ↥(orthDerived Q) = ⊥ := by
    refine CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ (exists_threeSingular hQ hdim ?_)
    by_cases hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q
    · exact Or.inl ⟨hplus, by omega⟩
    · exact Or.inr ⟨hplus, hℓ⟩
  exact ggTorusRootGenAvoidKG_of_scTorusModel hp hinj hZ (fun _ h => h)
    fun E hE _ _ hsc => ggTorusModelAt_of_selfCentralizing hQ hp hp2 hpq hF4 hdim hℓ hE hsc

end CFSG.StandardType.OmNsRootGen

end
