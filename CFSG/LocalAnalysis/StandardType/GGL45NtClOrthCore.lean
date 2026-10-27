module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClOrthModel
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial Matrix

theorem ntCore_omegaPlus {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ} (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) :
    GGL45NtCore p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) := by
  have hm3 : 3 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  set Θ := RecipeFieldOmega.plusEquiv (K := K) hm1 with hΘ
  have hI : (MulAut.congr Θ) ''
      LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) =
      LargeEvenInnSet
        (ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
          (ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus m K)) := by
    ext x
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← RecipeFieldOmega.coe_inner_eq_innSet]
      exact (RecipeFieldOmega.mem_innSet_iff_congr Θ φ).1 hφ
    · intro hx
      rw [← RecipeFieldOmega.coe_inner_eq_innSet] at hx
      refine ⟨(MulAut.congr Θ).symm x, ?_, ?_⟩
      · rw [RecipeFieldOmega.mem_innSet_iff_congr Θ, MulEquiv.apply_symm_apply]
        exact hx
      · exact (MulAut.congr Θ).apply_symm_apply x
  refine ntCore_of_mulEquiv Θ (LargeEvenInnSet _)
    (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) ?_
  rw [hI]
  obtain ⟨hnd, hT⟩ :=
    ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadPlus m K hm3
  have hAP :=
    ComponentClassification.CatalogueBOrthogonalPointData.coordinate_plus_point_action_properties m K hm3
  refine ntCore_omega_model hm1 hp hp2
    (ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus m K) hnd hT hAP
    ((MulAut.congr Θ) ''
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))) ?_ ?_
  · rintro f ⟨φ, hφ, rfl⟩
    obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hφ
    have hσ' : MulAut.congr Θ φ = AutOm.fieldAutP m σ := by rw [hΘ]; exact hσ
    refine ⟨CFSG.RankThree.PartOne.KCOrthogonalSubfield.fieldPair
      (ComponentClassification.CatalogueBOrthogonalPointData.coordinateQuadPlus m K) σ
      (CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap m σ), ?_, ?_⟩
    · intro v
      rw [AutOm.coordinateSemilinearMap_fieldPair]
      exact CFSG.SeitzReduction.E7Pilot.coordinateQuadPlus_fieldMap m σ v
    · rw [hσ']
      exact (AutOm.fieldAutP_apply m σ).symm
  · rintro f ⟨φ, hφ, rfl⟩ hfinn
    obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_field hm1 hφ
    have hσ' : MulAut.congr Θ φ = AutOm.fieldAutP m σ := by rw [hΘ]; exact hσ
    rw [hσ'] at hfinn
    rw [← RecipeFieldOmega.coe_inner_eq_innSet] at hfinn
    have hσ1 : σ = 1 := AutOm.eq_one_of_mem_inner_plusCompl hm3 (Or.inl rfl) hfinn
    have h1 : AutOm.fieldAutP m (1 : K ≃+* K) = 1 := map_one (AutOm.fieldAutP m)
    rw [hσ', hσ1, h1]

private theorem cOG2_mono {p : ℕ} {R : Type} [Group R] {I F F' : Set (MulAut R)}
    (hFF' : F ⊆ F') (h : GGL45NtCore p R I F') : GGL45NtCore p R I F := by
  intro hRsimple hRnonab Ebar f' hEab hcard hEbarI hf'p hconj hcomm hSat
  obtain ⟨f, hfF', u, huI, hford, hf'eq⟩ := hconj
  exact h hRsimple hRnonab Ebar f' hEab hcard hEbarI hf'p
    ⟨f, hFF' hfF', u, huI, hford, hf'eq⟩ hcomm hSat

theorem ntCore_omegaMinus {K : Type} [Field K] [Fintype K] [CharP K 2] {m p : ℕ} (hm : 3 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGL45NtCore p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _)
      (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  have hn4 : 4 ≤ m + 1 := by omega
  have hn : 1 ≤ m + 1 := by omega
  have hb : b ≠ 0 := CFSG.RankThree.PartOne.AUTSL.ne_zero_of_irreducible_tail b c hbc
  let Θ := RecipeFieldOmega.minusEquiv (n := m + 1) hn4 b c
  let τ := AutOm.frobAut hn4 hbc
  let Q := CFSG.RankThree.PartOne.AUTSL.Qm (m + 1) hn4 b c
  obtain ⟨f₀, -, hfcard⟩ := FiniteField.card K 2
  have hf : Nat.card K = 2 ^ (f₀ : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hfcard
  have hf1 : 1 ≤ (f₀ : ℕ) := Nat.one_le_iff_ne_zero.mpr (ne_of_gt f₀.pos)
  obtain ⟨hnd, hT3⟩ :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      (m + 1) K b c hn4 hbc
  have hAP :=
    CFSG.ComponentClassification.CatalogueBOrthogonalPointData.coordinate_minus_point_action_properties
      (m + 1) K b c hn4 hbc
  refine ntCore_of_mulEquiv (Θ := Θ) _ _ ?_
  have hI : (MulAut.congr Θ) ''
        LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) =
      LargeEvenInnSet
        (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) := by
    ext x
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      rw [← RecipeFieldOmega.coe_inner_eq_innSet
        (R := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q)]
      exact (RecipeFieldOmega.mem_innSet_iff_congr Θ φ).1 hφ
    · intro hx
      rw [← RecipeFieldOmega.coe_inner_eq_innSet
        (R := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q)] at hx
      exact ⟨(MulAut.congr Θ).symm x,
        (RecipeFieldOmega.mem_innSet_iff_congr Θ _).2 (by
          rw [MulEquiv.apply_symm_apply]
          exact hx),
        by rw [MulEquiv.apply_symm_apply]⟩
  have hFsub : (MulAut.congr Θ) ''
        LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))) ⊆
      Set.range (fun k : ℕ => τ ^ k) := by
    rintro f ⟨φ, hφ, rfl⟩
    obtain ⟨k, hk⟩ := RecipeFieldOmega.congr_minusEquiv_of_mem_phi (n := m + 1) hn4 hbc hφ
    exact ⟨k, hk.symm⟩
  rw [hI]
  refine cOG2_mono hFsub (ntCore_omega_model (n := m + 1) hn hp hp2 Q
    hnd hT3 hAP (Set.range (fun k : ℕ => τ ^ k)) ?_ ?_)
  · rintro f ⟨k, rfl⟩
    refine ⟨(CFSG.RankThree.PartOne.AUTSL.frobPair (m + 1) hn b c hb) ^ k, ?_, ?_⟩
    · rw [SubmonoidClass.coe_pow]
      exact (RecipeFieldOmega.isIsoPair_frobPair (n := m + 1) hn hb).pow k
    · change CFSG.RankThree.PartOne.AUTSL.conjAct Q
        ((CFSG.RankThree.PartOne.AUTSL.frobPair (m + 1) hn b c hb) ^ k) = τ ^ k
      rw [map_pow]
      rfl
  · rintro f ⟨k, rfl⟩ hfI
    have hmem : τ ^ k ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner
          (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q) ⊓
          Subgroup.zpowers τ := by
      refine ⟨?_, Subgroup.npow_mem_zpowers _ k⟩
      have hcoe := hfI
      rw [← RecipeFieldOmega.coe_inner_eq_innSet
        (R := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived Q)] at hcoe
      exact hcoe
    rw [AutOm.inner_inf_zpowers_frobAut hn4 hbc hf hf1, Subgroup.mem_bot] at hmem
    exact hmem

end CFSG.HardMathSupport.C14Cl
