module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDefs
public import CFSG.RankThree.PartOne.KF.R6LeviA
public import CFSG.RankThree.PartOne.KF.R56Final
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadDiag
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KTorusU5Lines
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
import CFSG.ClassicalInvolution.Phan.CenterScalars
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeUC.Asc1930
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.S12.InputsKF2
public import CFSG.RankThree.PartOne.S12.Sec1322Inputs
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate43
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.HardMathSupport.GuralnickMalle.CyclicTwo
import CFSG.HardMathSupport.GuralnickMalle.FGeneral
import CFSG.HardMathSupport.GuralnickMalle.Prop24General
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.LieType.Universal.Unitary (SU equivStatedSU SUid SUid_eq_statedSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open CFSG.RankThree.PartOne (suQ)
open CFSG.RankThree.PartOne.KFU (diagU dvec5 diagU_val diagU_dvec5_mem_SU
  fix_of_diagU_mem_SU5 mem_torus6_iff torus6 torus6_pow_eq_one)
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar (suToStated wittMat coe_suToStated)
open CFSG.ClassicalGroups.Unitary (IsUnitaryInvolution isUnitaryInvolution_unitaryInvolution)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem center_scalars_statedSU (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Subgroup.center (StatedSU 5 (2 ^ 2) K) =
      (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K) := by
  have hbar : IsUnitaryInvolution (unitaryInvolution K 2 2) :=
    isUnitaryInvolution_unitaryInvolution hK
  have hS : StatedSU 5 (2 ^ 2) K = SUid (unitaryInvolution K 2 2) 5 :=
    (SUid_eq_statedSU hK 5).symm
  rw [hS]
  exact CFSG.ClassicalInvolution.Phan.center_SUid_eq hbar (by norm_num)

omit [Finite K] [CharP K 2] in
private theorem card_scalars_five (hK : Nat.card K = (2 ^ 2) ^ 2) :
    Nat.card ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)) = 5 := by
  rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (n := 5) (by norm_num)).2.2]
  norm_num

private theorem exists_proj_automorphism_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ θbar : StatedProj (StatedSU 5 (2 ^ 2) K) ≃* StatedProj (StatedSU 5 (2 ^ 2) K),
      ∀ x : ↥(SU (unitaryInvolution K 2 2) 5),
        θbar (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
          (StatedSU 5 (2 ^ 2) K)) (suToStated (p := 2) (f := 2) hK 5 x)) = suQ 5 hK x := by
  classical
  let ψ : ↥(SU (unitaryInvolution K 2 2) 5) ≃* StatedSU 5 (2 ^ 2) K :=
    suToStated (p := 2) (f := 2) hK 5
  let θ : StatedSU 5 (2 ^ 2) K ≃* StatedSU 5 (2 ^ 2) K :=
    ψ.symm.trans (equivStatedSU hK 5)
  let N : Subgroup (StatedSU 5 (2 ^ 2) K) :=
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)
  have hN : N = Subgroup.center (StatedSU 5 (2 ^ 2) K) := (center_scalars_statedSU hK).symm
  have hNmap : N.map θ = N := by
    rw [hN, Subgroup.map_center_eq θ, ← hN]
  refine ⟨QuotientGroup.congr N N θ hNmap, fun x => ?_⟩
  change (QuotientGroup.congr N N θ hNmap) (QuotientGroup.mk (ψ x)) = suQ 5 hK x
  rw [QuotientGroup.congr_mk (e := θ) (he := hNmap) (x := ψ x)]
  have hθ : θ (ψ x) = equivStatedSU hK 5 x := by
    simp [θ, ψ]
  rw [hθ]
  rfl

private theorem card_zpowers_diagU_u5 {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    Nat.card (zpowers x₃) = 3 := by
  have hx3T : x₃ ∈ torus6 (unitaryInvolution K 2 2) 3 :=
    mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩
  have hx33 : x₃ ^ 3 = 1 := torus6_pow_eq_one hx3T
  have hx3ne : x₃ ≠ 1 := by
    intro h
    have hmat : ((diagU (dvec5 ζ ζ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 := by
      rw [← hx₃, h]
      simp
    have h00 := congrFun (congrFun hmat 0) 0
    simp [diagU_val, dvec5] at h00
    exact h1 h00
  rw [Nat.card_zpowers, orderOf_eq_prime hx33 hx3ne]

private theorem quotient_line_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₃)) ≠ ⊥ ∧
      Nat.card (zpowers (suQ 5 hK x₃)) = 3 := by
  classical
  have hζ : unitaryInvolution K 2 2 (ζ : K) = ζ := by
    have hmem : (diagU (dvec5 ζ ζ) : GL (Fin 5) K) ∈ SU (unitaryInvolution K 2 2) 5 := by
      rw [← hx₃]
      exact x₃.2
    exact (fix_of_diagU_mem_SU5 (unitaryInvolution K 2 2) hmem).1
  have hζinv : unitaryInvolution K 2 2 ((ζ⁻¹ : Kˣ) : K) = ((ζ⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hζ]
  let x₄ : ↥(SU (unitaryInvolution K 2 2) 5) :=
    ⟨diagU (dvec5 ζ ζ⁻¹), diagU_dvec5_mem_SU (unitaryInvolution K 2 2) hζ hζinv⟩
  have hx₄ : (x₄ : GL (Fin 5) K) = diagU (dvec5 ζ ζ⁻¹) := rfl
  have hline := (u5_line_le_kOf hK h1 h3 hx₃ hx₄).1
  have hB4 : F08.NotationB8103 (⊤ : Subgroup (StatedProj (StatedSU 5 (2 ^ 2) K)))
      ((torus6 (unitaryInvolution K 2 2) 3).map (suQ 5 hK)) 2
      (zpowers (suQ 5 hK x₄)) :=
    (u5_notationB_torus_iff hK h1 h3 hx₃ hx₄).mpr (Or.inr rfl)
  have hcard4 : Nat.card (zpowers (suQ 5 hK x₄)) = 3 := hB4.1
  have hne4 : zpowers (suQ 5 hK x₄) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard4
    omega
  have hK0 : F08.KOf8103 ⊤ (zpowers (suQ 5 hK x₃)) ≠ ⊥ := by
    intro hbot
    exact hne4 (le_bot_iff.mp (hbot ▸ hline))
  have hB3 : Nat.card (zpowers (suQ 5 hK x₃)) = 3 :=
    ((u5_notationB_torus_iff hK h1 h3 hx₃ hx₄).mpr (Or.inl rfl)).1
  exact ⟨hK0, hB3⟩

omit [Finite K] [CharP K 2] in
private theorem card_fiber_dvec5 (a : K) (ha : a ≠ a⁻¹) :
    Nat.card {i : Fin 5 // (![a, a, 1, a⁻¹, a⁻¹] : Fin 5 → K) i = a} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin 5 =>
      (![a, a, 1, a⁻¹, a⁻¹] : Fin 5 → K) i = a) = {0, 1} := by
    have ha1 : a ≠ 1 := fun h => ha (by rw [h, inv_one])
    ext i
    fin_cases i
    · simp
    · simp
    · simp [ha1.symm]
    · simp [ha.symm]
    · simp [ha.symm]
  rw [h]
  decide

omit [Finite K] [CharP K 2] in
private theorem card_fiber_dvec5_inv (a : K) (ha : a ≠ a⁻¹) :
    Nat.card {i : Fin 5 // (![a, a, 1, a⁻¹, a⁻¹] : Fin 5 → K) i = a⁻¹} = 2 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h : (Finset.univ.filter fun i : Fin 5 =>
      (![a, a, 1, a⁻¹, a⁻¹] : Fin 5 → K) i = a⁻¹) = {3, 4} := by
    have ha1 : a ≠ 1 := fun h => ha (by rw [h, inv_one])
    have ha1inv : a⁻¹ ≠ 1 := fun h => ha1 (by rw [← inv_inv a, h, inv_one])
    ext i
    fin_cases i
    · simp [ha]
    · simp [ha]
    · simp [ha1inv.symm]
    · simp
    · simp
  rw [h]
  decide

private theorem radSetup_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1)
    (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    RadSetup 1 (suToStated (p := 2) (f := 2) hK 5 x₃) (ζ : K) := by
  classical
  set a : K := (ζ : K) with ha
  have hζne : a ≠ 1 := fun h => h1 (Units.ext h)
  have hζ3 : a ^ 3 = 1 := by
    rw [ha, ← Units.val_pow_eq_pow_val, h3, Units.val_one]
  have hζinv : ζ ≠ ζ⁻¹ := by
    intro h
    have h2 : ζ ^ 2 = 1 := by
      have := congrArg (fun u : Kˣ => u * ζ) h
      simpa [pow_two] using this
    apply h1
    calc ζ = ζ ^ 3 * (ζ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, one_mul]
  have hainv : a ≠ a⁻¹ := by
    rw [ha]
    intro h
    apply hζinv
    apply Units.ext
    simpa only [Units.val_inv_eq_inv_val] using h
  have hd : ((diagU (dvec5 ζ ζ) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      diagonal ![a, a, 1, a⁻¹, a⁻¹] := by
    rw [diagU_val]
    congr 1
    funext i
    fin_cases i <;> simp [dvec5, ha]
  have hmat : (((suToStated (p := 2) (f := 2) hK 5 x₃ : StatedSU 5 (2 ^ 2) K) :
      GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (wittMat (p := 2) (f := 2) hK 5 : Matrix (Fin 5) (Fin 5) K) *
        diagonal ![a, a, 1, a⁻¹, a⁻¹] *
        ((wittMat (p := 2) (f := 2) hK 5)⁻¹ : GL (Fin 5) K) := by
    rw [coe_suToStated]
    simp only [Units.val_mul]
    rw [hx₃, hd]
  have hfr : Module.finrank K (eigSU (suToStated (p := 2) (f := 2) hK 5 x₃) a) = 2 := by
    rw [finrank_eigSU_of_conj_diagonal (P := wittMat (p := 2) (f := 2) hK 5)
      (d := ![a, a, 1, a⁻¹, a⁻¹]) hmat a]
    exact card_fiber_dvec5 a hainv
  have hfr' : Module.finrank K (eigSU (suToStated (p := 2) (f := 2) hK 5 x₃) a⁻¹) = 2 := by
    rw [finrank_eigSU_of_conj_diagonal (P := wittMat (p := 2) (f := 2) hK 5)
      (d := ![a, a, 1, a⁻¹, a⁻¹]) hmat a⁻¹]
    exact card_fiber_dvec5_inv a hainv
  have hx33 : x₃ ^ 3 = 1 :=
    torus6_pow_eq_one (mem_torus6_iff.mpr ⟨ζ, ζ, h3, h3, hx₃⟩)
  have hb3 : (suToStated (p := 2) (f := 2) hK 5 x₃) ^ 3 = 1 := by
    have h := map_pow (suToStated (p := 2) (f := 2) hK 5).toMonoidHom x₃ 3
    rw [hx33, map_one] at h
    exact h.symm
  exact ⟨even_two, le_rfl, hζne, hζ3, hb3, hfr, hfr'⟩

private theorem exists_quot_line_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    ∃ θbar : StatedProj (StatedSU 5 (2 ^ 2) K) ≃* StatedProj (StatedSU 5 (2 ^ 2) K),
      θbar (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K))
          (suToStated (p := 2) (f := 2) hK 5 x₃)) = suQ 5 hK x₃ ∧
        Nat.card (zpowers (suToStated (p := 2) (f := 2) hK 5 x₃)) = 3 ∧
        Nat.card (zpowers (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
          (StatedSU 5 (2 ^ 2) K)) (suToStated (p := 2) (f := 2) hK 5 x₃))) = 3 ∧
        (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
          (StatedSU 5 (2 ^ 2) K))).ker ≤ Subgroup.center (StatedSU 5 (2 ^ 2) K) ∧
        Nat.Coprime (Nat.card (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
          (StatedSU 5 (2 ^ 2) K))).ker) 6 := by
  classical
  let ψ : ↥(SU (unitaryInvolution K 2 2) 5) ≃* StatedSU 5 (2 ^ 2) K :=
    suToStated (p := 2) (f := 2) hK 5
  let N : Subgroup (StatedSU 5 (2 ^ 2) K) :=
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 2) K)
  let π : StatedSU 5 (2 ^ 2) K →* StatedProj (StatedSU 5 (2 ^ 2) K) :=
    QuotientGroup.mk' N
  obtain ⟨θbar, hθbar⟩ := exists_proj_automorphism_u5 hK
  have hθπ : θbar (π (ψ x₃)) = suQ 5 hK x₃ := by
    change θbar (QuotientGroup.mk' N (suToStated (p := 2) (f := 2) hK 5 x₃)) =
      suQ 5 hK x₃
    exact hθbar x₃
  have hcardψ : Nat.card (zpowers (ψ x₃)) = 3 := by
    have hmap : zpowers (ψ x₃) = (zpowers x₃).map ψ.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hmap, Subgroup.card_map_of_injective ψ.injective, card_zpowers_diagU_u5 h1 h3 hx₃]
  have hcardπ : Nat.card (zpowers (π (ψ x₃))) = 3 := by
    have hmap : (zpowers (π (ψ x₃))).map θbar.toMonoidHom = zpowers (suQ 5 hK x₃) := by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hθπ]
    calc Nat.card (zpowers (π (ψ x₃)))
        = Nat.card ((zpowers (π (ψ x₃))).map θbar.toMonoidHom) :=
          (Subgroup.card_map_of_injective θbar.injective).symm
      _ = Nat.card (zpowers (suQ 5 hK x₃)) := by rw [hmap]
      _ = 3 := (quotient_line_u5 hK h1 h3 hx₃).2
  have hkerN : π.ker = N := QuotientGroup.ker_mk' N
  refine ⟨θbar, hθπ, hcardψ, hcardπ, ?_, ?_⟩
  · change π.ker ≤ _
    rw [hkerN, center_scalars_statedSU hK]
  · change Nat.Coprime (Nat.card π.ker) 6
    rw [hkerN, card_scalars_five hK]
    norm_num

private theorem kOf_ne_bot_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    F08.KOf8103 ⊤ (zpowers (suToStated (p := 2) (f := 2) hK 5 x₃)) ≠ ⊥ := by
  classical
  obtain ⟨hKsuQ, -⟩ := quotient_line_u5 hK h1 h3 hx₃
  obtain ⟨θbar, hθπ, hcardψ, hcardπ, hkerπ, hcopπ⟩ := exists_quot_line_u5 hK h1 h3 hx₃
  have hkerθ : θbar.toMonoidHom.ker ≤
      Subgroup.center (StatedProj (StatedSU 5 (2 ^ 2) K)) := by
    rw [MonoidHom.ker_eq_bot θbar.toMonoidHom θbar.injective]
    exact bot_le
  have hcopθ : Nat.Coprime (Nat.card θbar.toMonoidHom.ker) 6 := by
    rw [MonoidHom.ker_eq_bot θbar.toMonoidHom θbar.injective, Subgroup.card_bot]
    norm_num
  have hKpi : F08.KOf8103 ⊤ (zpowers (QuotientGroup.mk' ((StatedScalars (Fin 5) K).subgroupOf
      (StatedSU 5 (2 ^ 2) K)) (suToStated (p := 2) (f := 2) hK 5 x₃))) ≠ ⊥ := by
    intro hbot
    apply hKsuQ
    have hmap := kOf8103_map_of_central θbar.toMonoidHom θbar.surjective hkerθ hcopθ hcardπ
    rw [MonoidHom.map_zpowers] at hmap
    simp only [MulEquiv.coe_toMonoidHom] at hmap
    rw [hθπ] at hmap
    rw [hmap, hbot, Subgroup.map_bot]
  intro hbot
  apply hKpi
  have hmap := kOf8103_map_of_central _ (QuotientGroup.mk'_surjective _) hkerπ hcopπ hcardψ
  rw [MonoidHom.map_zpowers] at hmap
  rw [hmap, hbot, Subgroup.map_bot]

private theorem radicalFacts_quotient_u5 (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ}
    (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1) {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)}
    (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ))
    (h : RadicalFacts (StatedSU (2 * 2 + 1) (2 ^ 2) K)
      (zpowers (suToStated (p := 2) (f := 2) hK 5 x₃))) :
    RadicalFacts (StatedProj (StatedSU 5 (2 ^ 2) K)) (zpowers (suQ 5 hK x₃)) := by
  classical
  obtain ⟨θbar, hθπ, hcardψ, hcardπ, hkerπ, hcopπ⟩ := exists_quot_line_u5 hK h1 h3 hx₃
  have hradπ := RadicalFacts.map_of_central _ (QuotientGroup.mk'_surjective _) hkerπ hcopπ
    hcardψ h
  rw [MonoidHom.map_zpowers] at hradπ
  have hradθ := RadicalFacts.of_mulEquiv θbar hcardπ hradπ
  rw [MonoidHom.map_zpowers] at hradθ
  simp only [MulEquiv.coe_toMonoidHom] at hradθ
  rw [hθπ] at hradθ
  exact hradθ

theorem u5_radicalFacts (hK : Nat.card K = (2 ^ 2) ^ 2) {ζ : Kˣ} (h1 : ζ ≠ 1) (h3 : ζ ^ 3 = 1)
    {x₃ : ↥(SU (unitaryInvolution K 2 2) 5)} (hx₃ : (x₃ : GL (Fin 5) K) = diagU (dvec5 ζ ζ)) :
    RadicalFacts (StatedProj (StatedSU 5 (2 ^ 2) K)) (zpowers (suQ 5 hK x₃)) := by
  classical
  have h : UnitaryFieldData 2 2 K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq (f := 2) hK (by norm_num)
  have hS := radSetup_u5 hK h1 h3 hx₃
  have hK₀ := kOf_ne_bot_u5 hK h1 h3 hx₃
  have hrad : RadicalFacts (StatedSU (2 * 2 + 1) (2 ^ 2) K)
      (zpowers (suToStated (p := 2) (f := 2) hK 5 x₃)) := hS.radicalFacts h hK₀
  exact radicalFacts_quotient_u5 hK h1 h3 hx₃ hrad

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
