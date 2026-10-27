module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.H13.U4ParPointStable
public import CFSG.Quasithin.H13.U4ParLineQuot
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU4
public import CFSG.ClassicalGroups.Unitary.ComponentBorelUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UnitaryParabolicGen
import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieLab
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MaxParabolicTransport
import CFSG.Quasithin.Background.RonanF918Four

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin (perfectCore)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem map_parP2_of_map_hypUnitriangular {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 m K) (hm : 2 ≤ m) {θ : MulAut (hypSU h 2 0)}
    (hθ : (hypUnitriangular h 2 0).map θ.toMonoidHom = hypUnitriangular h 2 0) :
    (CFSG.Quasithin.H13.U4Par.parP2 h).map θ.toMonoidHom = CFSG.Quasithin.H13.U4Par.parP2 h := by
  have hN := UnitaryHigher.normalizer_hypUnitriangular h (r := 2) (ε := 0) (by norm_num)
    (by norm_num)
  have hB : (hypBorel h 2 0).map θ.toMonoidHom = hypBorel h 2 0 := by
    rw [← hN, Subgroup.map_equiv_normalizer_eq, hθ]
  have hP := CFSG.Quasithin.H13.U4Par.map_parP_of_map_hypUnitriangular h hm hθ
  have hco : IsCoatom ((CFSG.Quasithin.H13.U4Par.parP2 h).map θ.toMonoidHom) :=
    CFSG.Quasithin.H13.F431.Un.OL5.lab5_isCoatom_map θ
      (CFSG.Quasithin.H13.U4Par.isCoatom_parP2 h)
  have hB2 : hypBorel h 2 0 ≤ CFSG.Quasithin.H13.U4Par.parP2 h :=
    hN ▸ (CFSG.Quasithin.H13.Sec53F.Unit.u4_yamStd h).le₁
  have hBle : hypBorel h 2 0 ≤ (CFSG.Quasithin.H13.U4Par.parP2 h).map θ.toMonoidHom := by
    rw [← hB]
    exact Subgroup.map_mono hB2
  rcases CFSG.Quasithin.H13.U4Par.eq_parP_or_eq_parP2 h hco hBle with h1 | h1
  · exact absurd (Subgroup.map_injective θ.injective (h1.trans hP.symm)).symm
      (CFSG.Quasithin.H13.U4Par.parP_ne_parP2 h)
  · exact h1

theorem k_U4ParabolicGen_holds :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsU4 X n →
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ Y₁ Y₂ : Subgroup X,
        ⁅Y₁, Y₁⁆ = Y₁ ∧ ⁅Y₂, Y₂⁆ = Y₂ ∧ IsL2 (Bar2 Y₁) n ∧ IsL2 (Bar2 Y₂) (2 * n) ∧
        Y₁ ⊔ Y₂ ⊔ S = ⊤ ∧
        ∀ α : MulAut X, S.map α.toMonoidHom = S →
          Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂ := by
  intro X _ _ n hn hU4 S hS
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.U4Par.exists_hypSU_equiv_of_lieModel hU4
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI := CFSG.Quasithin.H13.U4Par.isSimpleGroup_hypSU h
  have hY := CFSG.Quasithin.H13.Sec53F.Unit.u4_yamStd h
  obtain ⟨φ, hφ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.exists_mulEquiv_map_eq_of_isSylowIn
      (p := 2) e hY.sylow hS
  set P := CFSG.Quasithin.H13.U4Par.parP h
  set P2 := CFSG.Quasithin.H13.U4Par.parP2 h
  set U := hypUnitriangular h 2 0
  have hsol : Group.IsSolvable ↥(P ⊓ P2) := by
    rw [CFSG.Quasithin.H13.Sec53F.Unit.parP_inf_parP2 h]
    exact isSolvable_hypBorel h (by norm_num) (by norm_num)
  have hgen : perfectCore P ⊔ perfectCore P2 = ⊤ :=
    sup_perfectCore_eq_top_of_yamStd hY hsol
      (CFSG.Quasithin.H13.U4Par.hypUnitriangular_le_perfectCore_parP h hn)
      (CFSG.Quasithin.H13.U4Par.hypUnitriangular_le_perfectCore_parP2 h hn)
  have hperf : ∀ A : Subgroup ↥(hypSU h 2 0),
      ⁅(perfectCore A).map φ.toMonoidHom, (perfectCore A).map φ.toMonoidHom⁆ =
        (perfectCore A).map φ.toMonoidHom := fun A => by
    rw [← Subgroup.map_commutator, CFSG.Quasithin.perfectCore_perfect]
  have hinv : ∀ α : MulAut X, S.map α.toMonoidHom = S → ∀ A : Subgroup ↥(hypSU h 2 0),
      (∀ θ : MulAut ↥(hypSU h 2 0), U.map θ.toMonoidHom = U → A.map θ.toMonoidHom = A) →
      ((perfectCore A).map φ.toMonoidHom).map α.toMonoidHom =
        (perfectCore A).map φ.toMonoidHom := by
    intro α hα A hA
    have hθU : U.map ((φ.trans α).trans φ.symm).toMonoidHom = U := by
      apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
      rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.map_map_trans_symm, hφ, hα]
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.map_map_trans_symm,
      CFSG.Quasithin.map_perfectCore, hA _ hθU]
  refine ⟨(perfectCore P).map φ.toMonoidHom, (perfectCore P2).map φ.toMonoidHom, hperf P,
    hperf P2, ?_, ?_, ?_, fun α hα => ⟨hinv α hα P fun θ hθ =>
      CFSG.Quasithin.H13.U4Par.map_parP_of_map_hypUnitriangular h hn hθ, hinv α hα P2 fun θ hθ =>
      map_parP2_of_map_hypUnitriangular h hn hθ⟩⟩
  · obtain ⟨e2⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_map φ (perfectCore P)
    exact LieModel.of_mulEquiv e2.symm
      (CFSG.Quasithin.H13.U4Par.lieModel_modO2_perfectCore_parP h hn)
  · obtain ⟨e2⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_map φ (perfectCore P2)
    exact LieModel.of_mulEquiv e2.symm (CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (CFSG.Quasithin.H13.U4Par.isPSL_modO2_perfectCore_parP2 h))
  · rw [← hφ, ← Subgroup.map_sup, ← Subgroup.map_sup, hgen, top_sup_eq,
      Subgroup.map_top_of_surjective _ φ.surjective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
