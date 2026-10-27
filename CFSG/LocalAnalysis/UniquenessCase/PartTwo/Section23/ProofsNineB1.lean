module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKOut
public import CFSG.GroupTheory.Fitting.LayerContainment
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem shape_barImage_of_mem_calC {D : Data G} {Ch : Choice2011 G}
    (h8 : S23_8 D Ch) {c : Ctx23L D Ch} (h1930 : H1930 D) {X : Subgroup G}
    (hX : X ∈ calC D.M) :
    (∃ a : ℕ, IsL2 (barImage D.M X) a ∨ IsSz (barImage D.M X) a) ∨
      ((∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ IsL2Odd (barImage D.M X) q) ∨
        IsJ1 (barImage D.M X)) := by
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hX
  rcases (h8 h1930 c X hX).2 with ⟨a, -, hL2 | hSz⟩ | ⟨hrest, -⟩
  · exact Or.inl ⟨a, Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)⟩
  · exact Or.inl ⟨a, Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e hSz)⟩
  · rcases hrest with ⟨q, hq, hq2, hL2⟩ | hJ | ⟨a, hL2⟩
    · exact Or.inr (Or.inl ⟨q, hq, hq2, CFSG.Blueprint.LieModel.of_mulEquiv e hL2⟩)
    · obtain ⟨f⟩ := hJ
      exact Or.inr (Or.inr ⟨e.symm.trans f⟩)
    · exact Or.inl ⟨2 * a, Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e hL2)⟩

theorem s23_9_B1_of (D : Data G) (Ch : Choice2011 G) (h8 : S23_8 D Ch)
    (hA : S23_9_StepA D Ch) (hOut : KOut23) : S23_9_B1 D Ch := by
  intro h1930 c h3
  dsimp only
  let K : Subgroup G := Hinf (D.M ⊓ c.L)
  let Kbar : Subgroup (Bar2 D.M) := barImage D.M K
  have hKM : K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  have hKperf : ⁅K, K⁆ = K := uc22p21c_Hinf_perfect (D.M ⊓ c.L)
  have hKbarperf : ⁅Kbar, Kbar⁆ = Kbar := by
    dsimp only [Kbar, K]
    unfold barImage
    rw [← Subgroup.map_commutator, CFSG.GroupTheory.commutator_subgroupOf_eq hKM hKM,
      hKperf]
  letI : Group.IsPerfect Kbar := Subgroup.isPerfect_iff.mpr hKbarperf
  have hKF : ⁅Kbar, CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥ := by
    simpa only [Kbar, K] using hA h1930 c h3
  refine le_layer_of_perfect_of_centralizes_fitting_of_component_sup_centralizer Kbar hKF ?_
  intro C hC
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
  rw [← hXC]
  have hXnorm : (X.subgroupOf D.M).Normal := (h8 h1930 c X hX).1
  have hMnorm : D.M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX.1.le).mp hXnorm
  have hCnorm : (barImage D.M X).Normal := uc22p22u_barImage_normal hMnorm
  haveI : (barImage D.M X).Normal := hCnorm
  have hshape := shape_barImage_of_mem_calC (c := c) h8 h1930 hX
  exact le_sup_centralizer_of_perfect_of_perfect_aut_inner
    (Subgroup.le_normalizer_of_normal (H := barImage D.M X))
    (fun P hP => hOut ↥(barImage D.M X) hshape P hP)

end CFSG.LocalAnalysis.UniquenessCase.UC22
