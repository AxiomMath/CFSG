module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordSplit
public import CFSG.LocalAnalysis.StandardType.GGB48OmLift
public import CFSG.LocalAnalysis.StandardType.GGHalfRowData
public import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.StandardType.GGSpinInnerAction

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.Universal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

namespace A8Coord

private theorem om1_spinLift {G : Type} [Group G] {N : Subgroup G}
    (hZ : Subgroup.center ↥N = ⊥)
    (hL : StatedClassicalModel (↥N ⧸ Subgroup.center ↥N) .POmegaMinus 4 2 3) :
    ∃ φ : spinGroup (Spin.quadMinus 4 (GaloisField 2 3) (minusCoeffs 2 3).1
      (minusCoeffs 2 3).2) →* G, Function.Injective φ ∧ φ.range = N := by
  let S := spinGroup (Spin.quadMinus 4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2)
  have hS : StatedClassicalModel (S ⧸ Subgroup.center S) .POmegaMinus 4 2 3 :=
    CFSG.LieType.Universal.Spin.statedClassicalModel_spin_quadMinus (K := GaloisField 2 3)
      (n := 4) (b := (minusCoeffs 2 3).1) (c := (minusCoeffs 2 3).2) (p := 2) (f := 3)
      (by simp only [StatedLieAdmissible]; norm_num)
      (GaloisField.card 2 3 (by norm_num)) (minusCoeffs_irr 2 3)
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hL hS
  have hZs : Subgroup.center S = ⊥ :=
    PsiDiag.SpinM.center_eq_bot (K := GaloisField 2 3) (n := 4)
      (b := (minusCoeffs 2 3).1) (c := (minusCoeffs 2 3).2) (minusCoeffs_irr 2 3) le_rfl
  let qN : (↥N ⧸ Subgroup.center ↥N) ≃* ↥N :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let qS : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZs).trans QuotientGroup.quotientBot
  let ψ : S ≃* ↥N := qS.symm.trans (e.symm.trans qN)
  let φ : spinGroup (Spin.quadMinus 4 (GaloisField 2 3) (minusCoeffs 2 3).1
      (minusCoeffs 2 3).2) →* G := N.subtype.comp ψ.toMonoidHom
  refine ⟨φ, ?_, ?_⟩
  · exact N.subtype_injective.comp ψ.injective
  · apply le_antisymm
    · rintro x ⟨y, rfl⟩
      exact (ψ y).2
    · intro x hx
      obtain ⟨y, hy⟩ := ψ.surjective ⟨x, hx⟩
      exact ⟨y, by
        show N.subtype (ψ y) = x
        rw [hy]
        rfl⟩

theorem ggA8Nbr_omLift
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus 4 2 3) :
    ∃ φ : ↥omΩ →* G, Function.Injective φ ∧ φ.range = L := by
  have hqs : CFSG.Assembly.IsQuasisimple L := isQuasisimple_of_largeEvenMarking hInnL
  have hY : CFSG.IsQuasisimple ↥L := (TableBSymp.isQuasisimple_iff ↥L).mp hqs
  haveI : Group.IsPerfect ↥L := hY.1
  have hZ : Subgroup.center ↥L = ⊥ := HalfRowData.center_eq_bot_of_pomegaMinus_two hmod
  obtain ⟨φs, hinj, hrange⟩ := om1_spinLift hZ hmod
  let S := spinGroup (Spin.quadMinus 4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2)
  let πe : S ≃* matrixDerived omQ :=
    MulEquiv.ofBijective
      (AutOm.spinModelMinus (n := 4) (K := GaloisField 2 3)
        (b := (minusCoeffs 2 3).1) (c := (minusCoeffs 2 3).2) le_rfl (minusCoeffs_irr 2 3))
      ⟨AutOm.spinModelMinus_injective le_rfl (minusCoeffs_irr 2 3),
        AutOm.spinModelMinus_surjective le_rfl (minusCoeffs_irr 2 3)⟩
  let e : S ≃* ↥omΩ := πe.trans (CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv omQ)
  let φ : ↥omΩ →* G := φs.comp e.symm.toMonoidHom
  refine ⟨φ, hinj.comp e.symm.injective, ?_⟩
  rw [← hrange]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨e s, by simp [φ]⟩

theorem ggA8Nbr_omInner
    (hMp : GGInnerDiagMpInput) {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hInnL : GGInnerDiagOn Bs L)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaMinus 4 2 3) :
    ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ := by
  have hqs : CFSG.Assembly.IsQuasisimple L := isQuasisimple_of_largeEvenMarking hInnL
  have hY : CFSG.IsQuasisimple ↥L := (TableBSymp.isQuasisimple_iff ↥L).mp hqs
  haveI : Group.IsPerfect ↥L := hY.1
  have hZ : Subgroup.center ↥L = ⊥ := HalfRowData.center_eq_bot_of_pomegaMinus_two hmod
  obtain ⟨φ, hinj, hrange⟩ := om1_spinLift hZ hmod
  exact ggSpinMinusInnerAction_of_mp (n := 4) (f := 3) hMp le_rfl (by norm_num) hInnL φ hinj
    hrange

end A8Coord

end CFSG.StandardType

end
