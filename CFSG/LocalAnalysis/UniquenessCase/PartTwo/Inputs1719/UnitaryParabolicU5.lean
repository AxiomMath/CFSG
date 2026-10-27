module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.H13.U5ParPointStable
public import CFSG.Quasithin.H13.U5ParLineQuot
public import CFSG.ClassicalGroups.Unitary.ComponentBorelUnitary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UnitaryParabolicGen
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieRed
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

theorem isSU3_modO2_perfectCore_u5PtP {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    UC22.IsSU3 (CFSG.Quasithin.ModO2 (perfectCore (CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h))) f := by
  haveI := h.finite
  have h2f : (2 : ℕ) < 2 ^ f := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  obtain ⟨hq, -⟩ := CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le
    (s := 1) (ε := 1) h (by norm_num) (by intro hc; simp only [Prod.mk.injEq] at hc; omega)
  obtain ⟨e1⟩ := CFSG.Quasithin.H13.U5Par.nonempty_modO2_perfectCore_u5PtP_equiv h hf
  let eQ := e1.trans (CFSG.LocalAnalysis.EvenBN.U5.N₂equiv h).symm
  have hq' : CFSG.IsQuasisimple ↥(hypSU h 1 1) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hq
  refine ⟨(CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp
    (CFSG.IsQuasisimple.of_mulEquiv eQ hq'), ?_⟩
  obtain ⟨eZ⟩ := uc22p20p_quotCenter_equiv eQ
  have hZ := CFSG.Quasithin.H13.P31X.u3_hypScalars_eq_center h hf
  let eC : (↥(hypSU h 1 1) ⧸ Subgroup.center ↥(hypSU h 1 1)) ≃* hypPSU h 1 1 :=
    QuotientGroup.quotientMulEquivOfEq hZ.symm
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let eP : hypPSU h 1 1 ≃* StatedProj (StatedSU 3 (2 ^ f) K) :=
    hypPSUEquivStatedProj (r := 1) (ε := 1) h hR (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, ← pow_mul, Nat.mul_comm]
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, ?_, le_rfl, ?_⟩, K, inferInstance, h.finite, hKcard,
    ⟨eZ.trans (eC.trans eP)⟩⟩
  · omega
  · intro hc; simp only [Prod.mk.injEq] at hc; omega

theorem map_u5LnP_of_map_hypProjUnitriangular {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) {θ : MulAut (hypPSU h 2 1)}
    (hθ : (hypProjUnitriangular h 2 1).map θ.toMonoidHom = hypProjUnitriangular h 2 1) :
    (CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h).map θ.toMonoidHom =
      CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h := by
  have hg : θ ∈ CFSG.Quasithin.autStab (hypProjUnitriangular h 2 1) :=
    (CFSG.Quasithin.H13.F431.AG.mem_autStab_iff_map_eq θ _).2 hθ
  have hY := CFSG.Quasithin.H13.Sec53F.Unit.u5_yamStd (h := h)
  have hP := CFSG.Quasithin.H13.U5Par.map_u5PtP_of_map_hypProjUnitriangular h hf hθ
  rcases CFSG.Quasithin.H13.F431.Un.OL5.lab5_map_eq h hg hY.coatom₁ hY.le₁ with h1 | h1
  · exact absurd (Subgroup.map_injective θ.injective (h1.trans hP.symm)).symm
      CFSG.Quasithin.H13.Sec53F.Unit.u5PtP_ne_u5LnP
  · exact h1

theorem k_U5ParabolicGen_holds :
    ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 2 ≤ n → IsU5 X n →
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∃ Y₁ Y₂ : Subgroup X,
        ⁅Y₁, Y₁⁆ = Y₁ ∧ ⁅Y₂, Y₂⁆ = Y₂ ∧ UC22.IsSU3 (Bar2 Y₁) n ∧ IsL2 (Bar2 Y₂) (2 * n) ∧
        Y₁ ⊔ Y₂ ⊔ S = ⊤ ∧
        ∀ α : MulAut X, S.map α.toMonoidHom = S →
          Y₁.map α.toMonoidHom = Y₁ ∧ Y₂.map α.toMonoidHom = Y₂ := by
  intro X _ _ n hn hU5 S hS
  obtain ⟨K, _, h, ⟨e⟩⟩ := CFSG.Quasithin.H13.F431.Un.OL5.exists_model5 hU5
  haveI := CFSG.Quasithin.H13.Sec53F.Unit.finite_hypPSU_five h
  haveI := CFSG.Quasithin.H13.Sec53F.Unit.isSimpleGroup_hypPSU_five h
  have hY := CFSG.Quasithin.H13.Sec53F.Unit.u5_yamStd (h := h)
  obtain ⟨φ, hφ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.exists_mulEquiv_map_eq_of_isSylowIn
      (p := 2) e.symm hY.sylow hS
  set P := CFSG.Quasithin.H13.Sec53F.Unit.u5PtP h
  set P2 := CFSG.Quasithin.H13.Sec53F.Unit.u5LnP h
  set U := hypProjUnitriangular h 2 1
  have hsol : Group.IsSolvable ↥(P ⊓ P2) := by
    rw [CFSG.Quasithin.H13.Sec53F.Unit.u5PtP_inf_u5LnP]
    exact isSolvable_hypProjBorel h (by norm_num) (by norm_num)
  have hgen : perfectCore P ⊔ perfectCore P2 = ⊤ :=
    sup_perfectCore_eq_top_of_yamStd hY hsol
      (CFSG.Quasithin.H13.Sec53F.Unit.U_le_perfectCore_u5PtP hn)
      (CFSG.Quasithin.H13.Sec53F.Unit.U_le_perfectCore_u5LnP hn)
  have hperf : ∀ A : Subgroup (hypPSU h 2 1),
      ⁅(perfectCore A).map φ.toMonoidHom, (perfectCore A).map φ.toMonoidHom⁆ =
        (perfectCore A).map φ.toMonoidHom := fun A => by
    rw [← Subgroup.map_commutator, CFSG.Quasithin.perfectCore_perfect]
  have hinv : ∀ α : MulAut X, S.map α.toMonoidHom = S → ∀ A : Subgroup (hypPSU h 2 1),
      (∀ θ : MulAut (hypPSU h 2 1), U.map θ.toMonoidHom = U → A.map θ.toMonoidHom = A) →
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
      CFSG.Quasithin.H13.U5Par.map_u5PtP_of_map_hypProjUnitriangular h hn hθ, hinv α hα P2
      fun θ hθ => map_u5LnP_of_map_hypProjUnitriangular h hn hθ⟩⟩
  · obtain ⟨e2⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_map φ (perfectCore P)
    exact uc22p20p_isSU3_of_mulEquiv e2.symm (isSU3_modO2_perfectCore_u5PtP h hn)
  · obtain ⟨e2⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.nonempty_bar2_map φ (perfectCore P2)
    exact LieModel.of_mulEquiv e2.symm (CFSG.Quasithin.RonanF918.lieModel_of_isPSL
      (CFSG.Quasithin.H13.U5Par.isPSL_modO2_perfectCore_u5LnP h hn))
  · rw [← hφ, ← Subgroup.map_sup, ← Subgroup.map_sup, hgen, top_sup_eq,
      Subgroup.map_top_of_surjective _ φ.surjective]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
