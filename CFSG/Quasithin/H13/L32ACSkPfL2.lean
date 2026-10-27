module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus
public import CFSG.Quasithin.H13.KGFact22TorL2
public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.H13.L32A5Props
public import CFSG.Quasithin.H13.L32ACSk6
public import CFSG.Quasithin.H13.L32AHStr
public import CFSG.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32NSet14Gen
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem6
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.Schreier.MathieuOddCore
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CPrime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralAut
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular upperTriangular
  normalizer_unitriangular exists_sylow_unitriangular mul_apply_self_of_isUpperTriangular
  coe_inv_apply_self_of_isUpperTriangular coe_inv_isUpperTriangular
  mem_upperTriangular_iff_isUpperTriangular)
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply exists_conj_mul_slFieldAut)
open Matrix

section Linear

variable {K : Type} [Field K] {n : ℕ}

theorem comm_mem_unitriangular {a b : SpecialLinearGroup (Fin n) K}
    (ha : a ∈ upperTriangular n K) (hb : b ∈ upperTriangular n K) :
    a * b * a⁻¹ * b⁻¹ ∈ unitriangular n K := by
  have ha' := mem_upperTriangular_iff_isUpperTriangular.mp ha
  have hb' := mem_upperTriangular_iff_isUpperTriangular.mp hb
  have hai := coe_inv_isUpperTriangular ha'
  have hbi := coe_inv_isUpperTriangular hb'
  refine ⟨mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb), fun i => ?_⟩
  show ((a * b * a⁻¹ * b⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = 1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul,
    mul_apply_self_of_isUpperTriangular ((ha'.mul hb').mul hai) hbi,
    mul_apply_self_of_isUpperTriangular (ha'.mul hb') hai,
    mul_apply_self_of_isUpperTriangular ha' hb']
  have h1 := coe_inv_apply_self_of_isUpperTriangular ha' i
  have h2 := coe_inv_apply_self_of_isUpperTriangular hb' i
  linear_combination ((b : Matrix (Fin n) (Fin n) K) i i *
    ((b⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i) * h1 + h2

theorem comm_mem_unitriangular' :
    ∀ a ∈ Subgroup.normalizer ((unitriangular n K : Subgroup _) :
        Set (SpecialLinearGroup (Fin n) K)),
      ∀ b ∈ Subgroup.normalizer ((unitriangular n K : Subgroup _) :
        Set (SpecialLinearGroup (Fin n) K)), a * b * a⁻¹ * b⁻¹ ∈ unitriangular n K := by
  intro a ha b hb
  rw [normalizer_unitriangular] at ha hb
  exact comm_mem_unitriangular ha hb

end Linear

section L2

variable {K : Type} [Field K]

local notation "SL₂" => SpecialLinearGroup (Fin 2) K

theorem map_slFieldAut_unitriangular (σ : K ≃+* K) :
    (unitriangular 2 K).map (slFieldAut K σ).toMonoidHom = unitriangular 2 K := by
  have key : ∀ τ : K ≃+* K, ∀ u ∈ unitriangular 2 K, slFieldAut K τ u ∈ unitriangular 2 K := by
    intro τ u hu
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [slFieldAut_apply, hu.1 i j hij, map_zero]
    · rw [slFieldAut_apply, hu.2 i, map_one]
  refine le_antisymm ?_ fun u hu => ⟨slFieldAut K σ⁻¹ u, key _ u hu, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact key σ u hu
  · change slFieldAut K σ (slFieldAut K σ⁻¹ u) = u
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]

theorem slFieldAut_tT (σ : K ≃+* K) (a : Kˣ) :
    slFieldAut K σ (KG22.tT a) = KG22.tT (Units.map σ.toRingHom.toMonoidHom a) := by
  ext i j
  rw [slFieldAut_apply]
  fin_cases i <;> fin_cases j <;>
    simp [KG22.tT_apply, KG22.coe_diag2, Units.val_inv_eq_inv_val, map_inv₀]

theorem tT_mem_unitriangular_iff (a : Kˣ) : KG22.tT a ∈ unitriangular 2 K ↔ a = 1 := by
  constructor
  · intro h
    have h1 := h.2 0
    simp only [KG22.tT_apply, KG22.coe_diag2, diagonal_apply_eq, Matrix.cons_val_zero] at h1
    exact Units.ext h1
  · rintro rfl
    rw [map_one]
    exact one_mem _

theorem tT_range_le_normalizer :
    (KG22.tT : Kˣ →* SL₂).range ≤
      Subgroup.normalizer ((unitriangular 2 K : Subgroup SL₂) : Set SL₂) := by
  rintro _ ⟨a, rfl⟩
  rw [normalizer_unitriangular]
  exact KG22.tT_mem_upperTriangular a

theorem comap_centMod_sl2 (σ : K ≃+* K) :
    (centMod (unitriangular 2 K) (slFieldAut K σ)).comap KG22.tT = unitsFix σ := by
  ext a
  rw [Subgroup.mem_comap, mem_centMod, slFieldAut_tT, ← map_inv, ← map_mul,
    tT_mem_unitriangular_iff, mem_unitsFix]
  refine ⟨fun h => ?_, fun h => ⟨tT_range_le_normalizer ⟨a, rfl⟩, ?_⟩⟩
  · have h1 := congrArg Units.val (mul_inv_eq_one.mp h.2)
    exact h1
  · exact mul_inv_eq_one.mpr (Units.ext h)

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem centMod_sl2 (M : SL₂) (σ : K ≃+* K)
    (h : (unitriangular 2 K).map (MulAut.conj M * slFieldAut K σ).toMonoidHom =
      unitriangular 2 K) :
    centMod (unitriangular 2 K) (MulAut.conj M * slFieldAut K σ) =
      centMod (unitriangular 2 K) (slFieldAut K σ) :=
  centMod_conj_mul_eq comm_mem_unitriangular' (map_slFieldAut_unitriangular σ) h

theorem n4At_sl2 : N4At SL₂ (unitriangular 2 K) := by
  intro α _ hαU hcent
  obtain ⟨M, σ, rfl⟩ := exists_conj_mul_slFieldAut α
  rw [centMod_sl2 M σ hαU] at hcent
  have hσ : σ = 1 := by
    rw [← unitsFix_eq_top_iff, ← comap_centMod_sl2, eq_top_iff]
    intro a _
    exact hcent (tT_range_le_normalizer ⟨a, rfl⟩)
  left
  rw [hσ, map_one, mul_one]
  exact ⟨M, rfl⟩

theorem n2At_sl2 : N2At SL₂ (unitriangular 2 K) := by
  intro α _ hαU hidx
  obtain ⟨M, σ, rfl⟩ := exists_conj_mul_slFieldAut α
  rw [centMod_sl2 M σ hαU] at hidx
  have h1 := index_comap_le (unitriangular 2 K) (slFieldAut K σ) KG22.tT tT_range_le_normalizer
  rw [comap_centMod_sl2, hidx] at h1
  rcases eq_one_or_card_eq_four_of_index_unitsFix_le_three h1 with hσ | h4
  · rw [hσ, map_one, centMod_one, Subgroup.relIndex_self] at hidx
    omega
  · left
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
      inferInstance, by rw [h4]; norm_num, ⟨?_⟩⟩
    exact ((K1.statedProjEquivProjectiveSL 2 K).trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)).symm

theorem isSylowTwoOf_unitriangular_two : IsSylowTwoOf (unitriangular 2 K) ⊤ := by
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := K) 2 (n := 2) (by norm_num)
  rw [← hP]
  exact isSylowTwoOf_sylow P

end L2

theorem n2Model_n4Model_of_isPSL2 {M : Type} [Group M] {n : ℕ} (hn : 1 < n)
    (h : IsPSL 2 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  let e' : M ≃* SpecialLinearGroup (Fin 2) K := e.trans ((K1.statedProjEquivProjectiveSL 2 K).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K))
  exact ⟨(N2Model.of_at isSylowTwoOf_unitriangular_two n2At_sl2).of_mulEquiv e'.symm,
    (N4Model.of_at isSylowTwoOf_unitriangular_two n4At_sl2).of_mulEquiv e'.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
