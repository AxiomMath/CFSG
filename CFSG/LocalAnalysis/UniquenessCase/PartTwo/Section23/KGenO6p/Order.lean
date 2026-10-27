module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionBasic
import CFSG.LocalAnalysis.ComponentInitial.BabyPrereqOrthLinePrimitive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalPointCount
import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusPiecesOrders
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Assembly.QuasithinDefs
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCoresForms
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactPiece
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.G11Stmts
import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M24
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import CFSG.Walter.JRFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalPointAction
open CFSG.SeitzReduction.F4Pilot

private theorem kg6_ordSL_four (q : ℕ) :
    ordSL 4 q = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  simp [ordSL, Finset.prod_Icc_succ_top, mul_assoc]

private theorem kg6_stab_card {q N s : ℕ} (hq : 2 ≤ q)
    (hN : (q - 1) * N = (q ^ 3 - 1) * (q ^ 2 + 1))
    (hs : s * N = q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1)))) :
    s = q ^ 6 * (q - 1) * (q ^ 2 - 1) ^ 2 := by
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
  have hu : 0 < u := by omega
  have e1 : u + 1 - 1 = u := by omega
  have e2 : (u + 1) ^ 2 - 1 = u * (u + 2) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e3 : (u + 1) ^ 3 - 1 = u * (u ^ 2 + 3 * u + 3) := by
    apply Nat.sub_eq_of_eq_add; ring
  have e4 : (u + 1) ^ 4 - 1 = u * (u + 2) * ((u + 1) ^ 2 + 1) := by
    apply Nat.sub_eq_of_eq_add; ring
  rw [e1, e3] at hN
  rw [e2, e3, e4] at hs
  rw [e1, e2]
  have hN' : N = (u ^ 2 + 3 * u + 3) * ((u + 1) ^ 2 + 1) := by
    have : u * N = u * ((u ^ 2 + 3 * u + 3) * ((u + 1) ^ 2 + 1)) := by rw [hN]; ring
    exact Nat.eq_of_mul_eq_mul_left hu this
  subst hN'
  have hpos : 0 < (u ^ 2 + 3 * u + 3) * ((u + 1) ^ 2 + 1) := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [hs]
  ring

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_lineStab_omegaPlusSix (hK : 4 ≤ Nat.card K) :
    Nat.card ↥(CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.lineStab
        (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1)) =
      Nat.card K ^ 6 * (Nat.card K - 1) * (Nat.card K ^ 2 - 1) ^ 2 := by
  classical
  obtain ⟨hQ, hT⟩ := regular_quadPlus (n := 3) (K := K) le_rfl
  haveI htrans := (CFSG.LocalAnalysis.ComponentInitial.orthogonal_singular_line_primitive
    (quadPlus 3 K) hQ hT).1
  set e₀ : Fin 3 ⊕ Fin 3 → K := Pi.single (Sum.inl 0) 1 with he₀def
  have he0 : e₀ ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by simpa [e₀] using congr_fun h (Sum.inl 0)
    exact one_ne_zero h1
  have hQe0 : quadPlus 3 K e₀ = 0 := by
    rw [quadPlus_apply]
    simp [e₀, Pi.single_apply]
  set pt : Points (quadPlus 3 K) := pointMk e₀ he0 hQe0 with hpt
  have hmap : (StatedOmega (StatedQuadPlus 3 K)).map
      (toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom = elementaryGroup (quadPlus 3 K) := by
    rw [statedOmega_quadPlus_eq_map (n := 3) le_rfl, Subgroup.map_map]
    have : (toLinEquiv (Fin 3 ⊕ Fin 3) K).toMonoidHom.comp
        (toLinEquiv (Fin 3 ⊕ Fin 3) K).symm.toMonoidHom = MonoidHom.id _ := by
      ext x; simp
    rw [this, Subgroup.map_id]
  let ψ : ↥(StatedOmega (StatedQuadPlus 3 K)) ≃* ↥(elementaryGroup (quadPlus 3 K)) :=
    ((toLinEquiv (Fin 3 ⊕ Fin 3) K).subgroupMap (StatedOmega (StatedQuadPlus 3 K))).trans
      (MulEquiv.subgroupCongr hmap)
  have hψ : ∀ γ : ↥(StatedOmega (StatedQuadPlus 3 K)),
      ((ψ γ : ↥(elementaryGroup (quadPlus 3 K))) : (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) =
        toLinEquiv (Fin 3 ⊕ Fin 3) K (γ : GL (Fin 3 ⊕ Fin 3) K) := fun γ => rfl
  have hstab : (CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.lineStab
        (StatedOmega (StatedQuadPlus 3 K)) e₀).map ψ.toMonoidHom =
      MulAction.stabilizer ↥(elementaryGroup (quadPlus 3 K)) pt := by
    ext g
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      obtain ⟨c, hc⟩ := hγ
      rw [MulAction.mem_stabilizer_iff]
      refine smul_pointMk_of_apply_eq_smul he0 he0 hQe0 hQe0 (a := c) ?_
      rw [MulEquiv.coe_toMonoidHom, hψ, toLinEquiv_apply]
      exact hc
    · intro hg
      obtain ⟨γ, rfl⟩ := ψ.surjective g
      refine ⟨γ, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff] at hg
      have h1 : ψ γ • pt = pointMk (((ψ γ : ↥(elementaryGroup (quadPlus 3 K))) :
          (Fin 3 ⊕ Fin 3 → K) ≃ₗ[K] (Fin 3 ⊕ Fin 3 → K)) e₀) _ _ := smul_pointMk (ψ γ) e₀ he0 hQe0
      rw [hg] at h1
      obtain ⟨a, ha⟩ := (pointMk_eq_iff _ he0 _ hQe0).1 h1.symm
      exact ⟨a, by rw [ha, hψ, toLinEquiv_apply]⟩
  have hindex : (MulAction.stabilizer ↥(elementaryGroup (quadPlus 3 K)) pt).index =
      Nat.card (Points (quadPlus 3 K)) :=
    MulAction.index_stabilizer_of_transitive _ pt
  have hcardE : Nat.card ↥(MulAction.stabilizer ↥(elementaryGroup (quadPlus 3 K)) pt) *
      Nat.card (Points (quadPlus 3 K)) = Nat.card ↥(elementaryGroup (quadPlus 3 K)) := by
    rw [← hindex]
    exact Subgroup.card_mul_index _
  have hcardΓ : Nat.card ↥(elementaryGroup (quadPlus 3 K)) =
      Nat.card K ^ 6 * ((Nat.card K ^ 2 - 1) * ((Nat.card K ^ 3 - 1) * (Nat.card K ^ 4 - 1))) := by
    rw [← Nat.card_congr ψ.toEquiv, natCard_statedOmega_quadPlus_three hK, kg6_ordSL_four]
  have hpts : Nat.card (Points (quadPlus 3 K)) =
      Nat.card ↑(CFSG.LocalAnalysis.ComponentInitial.singularLinesIn (quadPlus 3 K) ⊤) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun L => by
      simp [CFSG.LocalAnalysis.ComponentInitial.singularLinesIn]))
  have hN : (Nat.card K - 1) * Nat.card (Points (quadPlus 3 K)) =
      (Nat.card K ^ 3 - 1) * (Nat.card K ^ 2 + 1) := by
    rw [hpts]
    exact (CFSG.LocalAnalysis.ComponentInitial.orthogonal_geometry_split_point_count K 3).1
  have hcard : Nat.card ↥(CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.lineStab
      (StatedOmega (StatedQuadPlus 3 K)) e₀) =
      Nat.card ↥(MulAction.stabilizer ↥(elementaryGroup (quadPlus 3 K)) pt) := by
    rw [← hstab, Subgroup.card_map_of_injective ψ.injective]
  rw [hcard]
  exact kg6_stab_card (by omega) hN (hcardE.symm ▸ hcardΓ)

theorem prime_dvd_sq_sub_one_of_dvd_card_lineStab {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : p ∣ Nat.card ↥(CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD.lineStab
        (StatedOmega (StatedQuadPlus 3 K)) (Pi.single (Sum.inl 0) 1))) :
    p ∣ Nat.card K ^ 2 - 1 := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [card_lineStab_omegaPlusSix h4] at h
  have hpq : ¬ p ∣ Nat.card K := by
    intro hdvd
    rw [hK] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact absurd (hp.dvd_of_dvd_pow h2) hpq
    · obtain ⟨u, hu⟩ : ∃ u, Nat.card K = u + 1 := ⟨Nat.card K - 1, by omega⟩
      have e1 : Nat.card K - 1 = u := by omega
      have e2 : Nat.card K ^ 2 - 1 = u * (u + 2) := by
        rw [hu]; apply Nat.sub_eq_of_eq_add; ring
      rw [e1] at h2
      rw [e2]
      exact Dvd.dvd.mul_right h2 _
  · exact hp.dvd_of_dvd_pow h1

end CFSG.LocalAnalysis.UniquenessCase.UC22.KGenO6pProof
