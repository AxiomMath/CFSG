module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideOrthElt
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem odt_center_projOrthDerived {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Subgroup.center (CFSG.RankThree.Classical2.ProjOrthDerived Q) = ⊥ := by
  obtain ⟨-, -, -, hsimple, hnonab, -⟩ :=
    CFSG.RankThree.Classical.orthogonal_high_Witt_derived_quotient_and_odd_lifts hQ hT
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (CFSG.RankThree.Classical2.ProjOrthDerived Q)) with h | h
  · exact h
  · exfalso
    obtain ⟨c, d, hcd⟩ := hnonab
    exact hcd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top d) c)

private theorem odt_dich_of_model {t : StatedLieTag}
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) {L N : ℕ} {R : Type} [Group R]
    (hR : StatedClassicalModel R t L 2 N) (lab : LargeEvenLabel)
    (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideDich lab (LargeEvenInnSet R) := by
  obtain ⟨K, _, _, V, _, _, _, Q, hQ, hT, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.exists_projOrth_model_card ht hR
  have hcenterT : Subgroup.center (CFSG.RankThree.Classical2.ProjOrthDerived Q) = ⊥ :=
    odt_center_projOrthDerived hQ hT
  have hZ : Subgroup.center R = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : e x ∈ Subgroup.center (CFSG.RankThree.Classical2.ProjOrthDerived Q) := by
      rw [← Subgroup.map_center_eq e]
      exact ⟨x, hx, rfl⟩
    rw [hcenterT, Subgroup.mem_bot] at hx'
    exact e.injective (by rw [hx', map_one])
  exact ggNbrLSideDich_of_elt (fun _ h => h) hZ
    (ggNbrLSideOrth_elt hQ hT hcard e hDet hO lab)

theorem ggNbrLSideOrthogonalData_holds (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideOrthogonalData := by
  refine ⟨?_, ?_⟩
  · intro ℓ n K _ _ hlam hℓ4 _ hK
    exact odt_dich_of_model (Or.inr (Or.inl rfl))
      (statedClassicalModel_omegaPlus ℓ n hK ⟨Nat.prime_two, hlam.1, hℓ4⟩)
      ⟨.D, ℓ, n⟩ hDet hO
  · intro ℓ n K _ _ b c hlam hℓ4 _ hK hbc
    exact odt_dich_of_model (Or.inr (Or.inr rfl))
      (statedClassicalModel_omegaMinus ℓ n hK b c hbc ⟨Nat.prime_two, hlam.1, hℓ4⟩)
      ⟨.twD, ℓ, n⟩ hDet hO

end CFSG.StandardType

end
