module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorusOnFamilies
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusBorel
public import CFSG.GroupTheory.SylowTwoEquiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

theorem isMulCommutative_normalizerQuotient_tailUnipotent_minus {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} {r : ℕ} (hr : 3 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsMulCommutative
      (normalizerQuotient
        ((tailUnipotent r (minusTailForm K b c)).subgroupOf
          (orthElementaryGroup (quadTail r (minusTailForm K b c))))) := by
  let E := orthElementaryGroup (quadTail r (minusTailForm K b c))
  let U : Subgroup E := (tailUnipotent r (minusTailForm K b c)).subgroupOf E
  let B : Subgroup E := (tailBorel r (minusTailForm K b c)).subgroupOf E
  change IsMulCommutative (normalizerQuotient U)
  have hN : Subgroup.normalizer (U : Set E) = B :=
    (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (K := K) (A := Fin 2 → K)
      (r := r) (qA := minusTailForm K b c) hr (anisotropic_minusTailForm hirr)
      (nondegenerate_minusTailForm hirr) (Or.inr finrank_fin_two_fun)).2.1
  refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_subgroupOf]
  change (Subgroup.normalizer (U : Set E)).subtype ⁅x, y⁆ ∈ U
  rw [map_commutatorElement (Subgroup.normalizer (U : Set E)).subtype]
  rw [Subgroup.mem_subgroupOf]
  change E.subtype ⁅(Subgroup.normalizer (U : Set E)).subtype x,
    (Subgroup.normalizer (U : Set E)).subtype y⁆ ∈ tailUnipotent r (minusTailForm K b c)
  rw [map_commutatorElement E.subtype]
  refine commutator_mem_tailUnipotent (b := b) (c := c) (r := r) hr hirr ?_ ?_
  · have hxB : (x : E) ∈ B := by
      rw [← hN]
      exact x.2
    exact hxB
  · have hyB : (y : E) ∈ B := by
      rw [← hN]
      exact y.2
    exact hyB

theorem k_BorelSimple_POmegaMinus : KBorelSimple .POmegaMinus := by
  intro Y _ _ m f hadm hY S hS
  have hm4 : 4 ≤ m := by
    have h := hadm
    simpa only [CFSG.Open.StatedLieAdmissible] using h.2.2
  have hf1 : 1 ≤ f := by
    have h := hadm
    simpa only [CFSG.Open.StatedLieAdmissible] using h.2.1
  obtain ⟨-, hmodel⟩ := hY.statedClassicalModel (t := .POmegaMinus) (by decide)
  obtain ⟨K, hKfield, hKfinite, hKcard, b, c, hirr, ⟨e⟩⟩ := hmodel
  have hchar : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two hf1 hKcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus m K b c)) = ⊥ :=
    statedScalars_subgroupOf_statedOmega_quadMinus_projective_eq_bot (F := K)
  let eProj : StatedProj (StatedOmega (StatedQuadMinus m K b c)) ≃*
      StatedOmega (StatedQuadMinus m K b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eTail : StatedOmega (StatedQuadMinus m K b c) ≃*
      orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c)) :=
    tailOmegaEquiv (minusTailIsometry m K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus m K b c)
      (CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus (n := m) hm4 hirr)
  let eYE : Y ≃* orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c)) :=
    e.trans (eProj.trans eTail)
  have : Finite (orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c))) :=
    Finite.of_equiv Y eYE.toEquiv
  have hcomm : IsMulCommutative
      (normalizerQuotient
        ((tailUnipotent (m - 1) (minusTailForm K b c)).subgroupOf
          (orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c))))) :=
    isMulCommutative_normalizerQuotient_tailUnipotent_minus (K := K) (b := b) (c := c)
      (r := m - 1) (by omega) hirr
  have hSylTail : IsSylowTwoOf
      ((tailUnipotent (m - 1) (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail (m - 1) (minusTailForm K b c)))) ⊤ := by
    obtain ⟨⟨S₀, hS₀⟩, -, -, -⟩ :=
      orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) (K := K) (A := Fin 2 → K)
        (r := m - 1) (qA := minusTailForm K b c) (by omega)
        (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
        (Or.inr finrank_fin_two_fun)
    rw [← hS₀]
    exact ⟨le_top, S₀.isPGroup', by
      rw [show ((S₀ : Subgroup (orthElementaryGroup (quadTail (m - 1)
        (minusTailForm K b c)))).subgroupOf ⊤).index =
          (S₀ : Subgroup (orthElementaryGroup (quadTail (m - 1)
            (minusTailForm K b c)))).index from Subgroup.relIndex_top_right _]
      exact S₀.not_dvd_index⟩
  have hSmap : IsSylowTwoOf (S.map eYE.toMonoidHom) ⊤ := by
    simpa using CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eYE hS
  obtain ⟨e₁⟩ := normalizerQuotient_equiv_of_isSylowTwoOf eYE hS hSmap
  obtain ⟨e₂⟩ :=
    normalizerQuotient_equiv_of_isSylowTwoOf (MulEquiv.refl _) hSmap hSylTail
  exact CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv e₁.symm
    (CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv e₂.symm hcomm)

theorem k_BorelTorusAbelian_POmegaMinus_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_POmegaMinus :=
  k_BorelTorusAbelian_of_simple_of_centerTwo .POmegaMinus (by decide)
    k_BorelSimple_POmegaMinus (k_BorelTorusAbelian_centerTwo_of_griess hN)

theorem k_BorelTorusAbelian_OmegaMinusEight_of_griess
    (hN : CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20rNativeGriess) :
    K_BorelTorusAbelian_OmegaMinusEight :=
  k_BorelTorusAbelian_OmegaMinusEight_of_family (k_BorelTorusAbelian_POmegaMinus_of_griess hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
