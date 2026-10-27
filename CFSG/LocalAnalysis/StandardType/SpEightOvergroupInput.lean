module

public import CFSG.LocalAnalysis.StandardType.SpEightOvergroups
public import CFSG.LocalAnalysis.StandardType.SpTwoThreeFixedPoints
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcGenuine
public import CFSG.LocalAnalysis.StandardType.SylowOvergroupReduction

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.Open CFSG.Blueprint.EvenSource

namespace SpEight

theorem nonempty_mulEquiv_statedProj_zmod_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {r : ℕ} {K : Type} [Group K] (e : K ≃* StatedProj (StatedSp r F)) :
    Nonempty (K ≃* StatedProj (StatedSp r (ZMod 2))) := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  let σ : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF'
  exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr (ι := Fin r ⊕ Fin r) σ.symm)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp σ.symm r)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars σ.symm))⟩

theorem nonempty_mulEquiv_matrixOrthogonal_of_fixedClosure_le {K : Type} [Group K]
    (e : K ≃* StatedProj (StatedSp 4 (ZMod 2))) (E : Subgroup (MulAut K))
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2) (hne : ggFixedClosure E ≠ ⊤)
    {Y : Subgroup K} (hDY : ggFixedClosure E ≤ Y) (hY : Y ≠ ⊤) :
    Nonempty (↥Y ≃* ↥(matrixOrthogonal Q0)) := by
  have hF : Nat.card (ZMod 2) = 2 := by simp
  have hinj : Function.Injective (proj 4 (ZMod 2)) :=
    CFSG.RankThree.PartOne.proj_injective_sp (f := 1) (by simpa using hF) le_rfl (by omega)
  let φ : StatedSp 4 (ZMod 2) ≃* K :=
    (MulEquiv.ofBijective (proj 4 (ZMod 2)) ⟨hinj, proj_surjective⟩).trans e.symm
  have hin : ∀ α : MulAut K, ∃ k : K, α = MulAut.conj k := by
    intro α
    obtain ⟨g, hg⟩ := SpTwoThree.all_inner_statedProj hF (by norm_num) (MulAut.congr e α)
    obtain ⟨k, hk⟩ := (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e α).mp ⟨g, hg.symm⟩
    exact ⟨k, hk.symm⟩
  obtain ⟨E1, hE1card, hE1comm, hE1exp, hD, -⟩ := SpTwoThree.exists_subgroup_of_all_inner φ
    (fun a ha => SpTwoThree.eq_one_of_forall_commute hF (by omega) a ha) hin E hE
  have hE1card9 : Nat.card E1 = 9 := by rw [hE1card, hcard]; norm_num
  have hne1 : Subgroup.closure
      {g : StatedSp 4 (ZMod 2) | ∃ x ∈ E1, x ≠ 1 ∧ g * x = x * g} ≠ ⊤ := by
    intro h
    apply hne
    rw [hD, h]
    exact Subgroup.map_top_of_surjective _ φ.surjective
  have hDY' : Subgroup.closure {g : StatedSp 4 (ZMod 2) | ∃ x ∈ E1, x ≠ 1 ∧ g * x = x * g} ≤
      Y.comap φ.toMonoidHom := by
    rw [← Subgroup.map_le_iff_le_comap, ← hD]
    exact hDY
  have hY' : Y.comap φ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hY
    rw [eq_top_iff]
    intro k _
    obtain ⟨g, rfl⟩ := φ.surjective k
    have : g ∈ Y.comap φ.toMonoidHom := by rw [h]; trivial
    exact this
  obtain ⟨e2⟩ := nonempty_mulEquiv_matrixOrthogonal_of_closure_le hE1comm hE1exp hE1card9 hne1
    hDY' hY'
  exact ⟨(φ.symm.subgroupMap Y).trans
    ((MulEquiv.subgroupCongr (Subgroup.comap_equiv_eq_map_symm φ Y).symm).trans e2)⟩

end SpEight

theorem ggSeitzExcSpEightOvergroupInput_holds : GGSeitzExcSpEightOvergroupInput := by
  rintro K _ _ d q hq2 hq1 hd he E hE hcard hne Y hDY hY -
  obtain ⟨e⟩ := he
  obtain ⟨-, F, _, _, hF, ⟨e'⟩⟩ :=
    (ggLieModel_symplectic_two d q hq2 hq1 4 (by norm_num) hd e).statedClassicalModel
      (by decide)
  obtain ⟨e''⟩ := SpEight.nonempty_mulEquiv_statedProj_zmod_two (by simpa using hF) e'
  obtain ⟨c⟩ := SpEight.nonempty_mulEquiv_matrixOrthogonal_of_fixedClosure_le e'' E hE hcard hne
    hDY hY
  haveI := SpEight.isSimpleGroup_commutator_matrixOrthogonal
  let c' := SylowOvergroup.commutatorEquiv c
  exact ⟨c'.isSimpleGroup,
    LieModel.of_mulEquiv c'.symm SpEight.lieModel_commutator_matrixOrthogonal⟩

end CFSG.StandardType
