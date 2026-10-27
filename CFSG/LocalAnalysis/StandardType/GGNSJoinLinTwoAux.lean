module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusLinIrred
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB1

public section

namespace CFSG.StandardType

open Polynomial CFSG CFSG.Assembly
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem nsLT2_map_ggAutFixedSubgroup {R R' : Type*} [Group R] [Group R']
    (e : R ≃* R') (σ : MulAut R) :
    (ggAutFixedSubgroup σ).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.congr e σ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup]
    have hy' : σ y = y := (mem_ggAutFixedSubgroup σ y).mp hy
    simp [MulAut.congr_apply, hy']
  · intro hx
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hx
    have hx' : e (σ (e.symm x)) = x := by simpa [MulAut.congr_apply] using hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hx'

theorem nsLT2_primary_factor_classification {N : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2) {g : GL (Fin N) F} (hg : g ^ 3 = 1)
    {h : F[X]} (hh : h ∈ primaryFactors (glA g : Module.End F (Fin N → F))) :
    h = X - C 1 ∨ h = X ^ 2 + X + 1 := by
  have hpk : (3 : F) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h0
    omega
  have hA : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Fˣ) := by
    rw [map_one]
    exact hg
  have hmin : minpoly F (glA g : Module.End F (Fin N → F)) ∣ X ^ 3 - C (1 : F) := by
    refine minpoly.dvd F _ ?_
    have h1 : ((glA g : LinearMap.GeneralLinearGroup F (Fin N → F)) :
        Module.End F (Fin N → F)) = Matrix.toLin' (g : Matrix (Fin N) (Fin N) F) := rfl
    rw [map_sub, map_pow, aeval_X, aeval_C, h1, ← Matrix.toLin'_pow,
      ← Units.val_pow_eq_pow_val, hg]
    rw [show ((1 : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 from rfl,
      Matrix.toLin'_one, map_one]
    exact sub_self (1 : Module.End F (Fin N → F))
  have hdvd : h ∣ X ^ 3 - C (1 : F) := (mem_primaryFactors.mp hh).2.2.trans hmin
  exact CFSG.HardMathSupport.Curtis.Coordinator.eq_X_sub_one_or_eq_quad_of_dvd hF
    (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh)
    (CFSG.RankThree.PartOne.KCPrimary.monic_of_mem_primaryFactors hh) hdvd

theorem nsLT2_component_label_of_order_three {N : ℕ} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hF : Nat.card F = 2) {g : GL (Fin N) F} (hg : g ^ 3 = 1)
    {T : Subgroup (projectiveSL N F)}
    (hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N F g))) :
    ∃ (m j : ℕ), 2 ≤ m ∧ j ≤ 2 ∧
      GGHasLabel ⟨.A, m - 1, j⟩ (↥T ⧸ Subgroup.center ↥T) ∧
      LargeEvenInLambda2 ⟨.A, m - 1, j⟩ := by
  have hpk : (3 : F) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ 3 := (CharP.cast_eq_zero_iff F 2 3).mp h0
    omega
  have hA : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Fˣ) := by
    rw [map_one]
    exact hg
  obtain ⟨h, hTeq⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components hpk hA T hT
  obtain ⟨⟨h0, hmem⟩, hgood⟩ := h
  change IsGoodFactor g h0 at hgood
  have hsq := squarefree_minpoly_glA hpk hA
  have hcls : h0 = X - C 1 ∨ h0 = X ^ 2 + X + 1 :=
    nsLT2_primary_factor_classification hF hg hmem
  haveI : Fact (Irreducible h0) :=
    ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem⟩
  haveI : Finite (AdjoinRoot h0) := Module.finite_of_finite F
  have hcardE : Nat.card (AdjoinRoot h0) = 2 ^ h0.natDegree :=
    CFSG.HardMathSupport.Curtis.Coordinator.natCard_adjoinRoot_of_card_eq_two hF
      (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem)
  have hj1 : 1 ≤ h0.natDegree :=
    (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hmem).natDegree_pos
  have hdeg : h0.natDegree = 1 ∨ h0.natDegree = 2 := by
    rcases hcls with hcl | hcl
    · left
      rw [hcl]
      exact natDegree_X_sub_C 1
    · right
      rw [hcl]
      compute_degree!
  have hm : 2 ≤ primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 := by
    rcases hgood with h3 | ⟨h2, -⟩ <;> omega
  have hm2E : primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 = 2 →
      4 ≤ Nat.card (AdjoinRoot h0) := by
    intro hm2
    rcases hgood with h3 | ⟨-, h4⟩
    · omega
    · exact h4
  have hne2 : (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0,
      2 ^ h0.natDegree) ≠ (2, 2) := by
    intro hpair
    have hm2 : primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 = 2 := by
      simpa using congrArg Prod.fst hpair
    have h2j : 2 ^ h0.natDegree = 2 := by
      simpa using congrArg Prod.snd hpair
    have h4 := hm2E hm2
    rw [hcardE, h2j] at h4
    omega
  have hne3 : (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0,
      2 ^ h0.natDegree) ≠ (2, 3) := by
    intro hpair
    have h3 : 2 ^ h0.natDegree = 3 := by
      simpa using congrArg Prod.snd hpair
    rcases hdeg with hd | hd <;> rw [hd] at h3 <;> norm_num at h3
  have hS : CFSG.Open.IsComponentOf ((specialFactor g h0).map (proj N F))
      (fixSubgroup (conjAut N F g)) := by
    rw [← hTeq]
    exact hT
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor
      (A := g) hsq hmem
  obtain ⟨f, hf, hker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_surjective_ker_le_center_map_proj e
  have hperfSL : Group.IsPerfect
      (Matrix.SpecialLinearGroup (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0))
        (AdjoinRoot h0)) := by
    by_cases hm2 : primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 = 2
    · rw [hm2]
      exact CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _
        (hm2E hm2)
    · exact CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by omega)
  obtain ⟨eQ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f hf hperfSL hker
  have hmodel : CFSG.Open.StatedClassicalModel
      (↥((specialFactor g h0).map (proj N F)) ⧸
        Subgroup.center ↥((specialFactor g h0).map (proj N F))) .PSL
      (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0) 2 h0.natDegree := by
    refine ⟨⟨Nat.prime_two, hj1, hm, hne2, hne3⟩,
      AdjoinRoot h0, inferInstance, inferInstance, hcardE, ?_⟩
    exact ⟨eQ.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj _ (AdjoinRoot h0))⟩
  have hmodel' : CFSG.Open.StatedClassicalModel
      (↥((specialFactor g h0).map (proj N F)) ⧸
        Subgroup.center ↥((specialFactor g h0).map (proj N F))) .PSL
      (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 - 1 + 1) 2 h0.natDegree := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤
      primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0)]
  have hhasS : GGHasLabel
      ⟨.A, primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 - 1, h0.natDegree⟩
      (↥((specialFactor g h0).map (proj N F)) ⧸
        Subgroup.center ↥((specialFactor g h0).map (proj N F))) :=
    ggHasLabel_typeA (n := primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 - 1)
      (f := h0.natDegree) hmodel'
  have hΛ : LargeEvenInLambda2
      ⟨.A, primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 - 1, h0.natDegree⟩ :=
    largeEvenInLambda2_typeA (n := primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0 - 1)
      (f := h0.natDegree) hmodel'
  refine ⟨primaryMultiplicity (glA g : Module.End F (Fin N → F)) h0, h0.natDegree, hm,
    ?_, ?_, hΛ⟩
  · rcases hdeg with hd | hd <;> omega
  · rw [hTeq]
    exact hhasS

theorem nsLT2_iso_n_le {lab : LargeEvenLabel} {r j : ℕ} (hj : j ≤ 2)
    (h : GGLabelIso lab ⟨.A, r, j⟩) : lab.n ≤ 2 := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]
    exact hj
  · exact absurd h.2.1 (by simp)
  · obtain ⟨-, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h2
    obtain ⟨-, hjn⟩ := h2
    omega
  · exact absurd h.2 (by simp)
  · exact absurd h.2 (by simp)
  · exact absurd h.2 (by simp)
  · obtain ⟨-, h2⟩ := h
    simp only [LargeEvenLabel.mk.injEq] at h2
    obtain ⟨-, hjn⟩ := h2
    omega
  · exact absurd h.1 (by simp)

end CFSG.StandardType

end
