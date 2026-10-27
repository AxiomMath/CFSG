module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.Quasithin.H13.L32ACSk10
public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTorus
public import CFSG.RankThree.PartTwo.KFacts.AutG2
public import CFSG.LieType.Chevalley.BorelSelfNormalizer
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.LieType.Chevalley.ChevalleySplitBN
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.LangRootArithmetic
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
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
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
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartTwo.KFacts (g2FieldHom coe_g2FieldHom g2_automorphism_normal_form)

section G2

variable {K : Type} [Field K]

local notation "U₂" => Subgroup.subgroupOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K)

local notation "N₂" => Subgroup.normalizer
  ((Subgroup.subgroupOf (posUnipotent Tag.G2 K) (adjointGroup Tag.G2 K) :
    Subgroup (adjointGroup Tag.G2 K)) : Set (adjointGroup Tag.G2 K))


theorem mem_normalizer_g2U_iff
    (g : adjointGroup Tag.G2 K) :
    g ∈ N₂ ↔
      (g : ModGL Tag.G2 K) ∈ borelGroup Tag.G2 K := by
  rw [mem_normalizer_subgroupOf_iff posUnipotent_le_adjointGroup, ← (borel_self_normalizers
    Tag.G2 K).1, Subgroup.mem_inf]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem g2_comm_mem :
    ∀ a ∈ N₂,
      ∀ b ∈ N₂,
        a * b * a⁻¹ * b⁻¹ ∈ U₂ := by
  intro a ha b hb
  rw [mem_normalizer_g2U_iff] at ha hb
  obtain ⟨hab, -, hHN, -, hHU, -⟩ := triangular_borel_structure.{0, 0} Tag.G2 K
  rw [← SetLike.mem_coe, hHU] at ha hb
  exact mul_mul_inv_mul_inv_mem_of_mem_mul hHN hab ha hb

theorem rootDiagUnit_mem_g2
    (a : Fin Tag.G2.rank → Kˣ) :
    rootDiagUnit Tag.G2 a ∈ adjointGroup Tag.G2 K ∧
      rootDiagUnit Tag.G2 a ∈ torusGroup Tag.G2 K := by
  obtain ⟨⟨B, hB, -⟩, h⟩ := G2_F4_root_character_diagonals_inner Tag.G2 (Or.inl rfl) K
  obtain ⟨-, hH, hC, -⟩ := h B hB a
  exact ⟨hC, hH⟩

@[expose] noncomputable def g2Torus
    (K : Type) [Field K] : (Fin Tag.G2.rank → Kˣ) →* adjointGroup Tag.G2 K :=
  (rootDiagUnitHom Tag.G2 K).codRestrict _ fun a => (rootDiagUnit_mem_g2 a).1

theorem coe_g2Torus
    (a : Fin Tag.G2.rank → Kˣ) : (g2Torus K a : ModGL Tag.G2 K) = rootDiagUnit Tag.G2 a :=
  rfl

theorem g2Torus_mem_normalizer :
    (g2Torus K).range ≤ N₂ := by
  rintro _ ⟨a, rfl⟩
  rw [mem_normalizer_g2U_iff, coe_g2Torus]
  exact (le_sup_left : torusGroup Tag.G2 K ≤ borelGroup Tag.G2 K) (rootDiagUnit_mem_g2 a).2

theorem g2Torus_mem_g2U_iff
    (a : Fin Tag.G2.rank → Kˣ) : g2Torus K a ∈ U₂ ↔ a = 1 := by
  constructor
  · intro h
    have h1 : rootDiagUnit Tag.G2 a ∈ torusGroup Tag.G2 K ⊓ posUnipotent Tag.G2 K :=
      ⟨(rootDiagUnit_mem_g2 a).2, h⟩
    rw [(triangular_borel_structure.{0, 0} Tag.G2 K).2.2.2.1, Subgroup.mem_bot] at h1
    exact rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
  · rintro rfl
    rw [map_one]
    exact one_mem _

theorem g2FieldHom_g2Torus
    (σ : K ≃+* K)
    (a : Fin Tag.G2.rank → Kˣ) :
    g2FieldHom K σ (g2Torus K a) =
      g2Torus K (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) := by
  apply Subtype.ext
  rw [coe_g2FieldHom, coe_g2Torus, coe_g2Torus, units_map_entrywiseHom_rootDiagUnit_ringEquiv]

theorem comap_centMod_g2
    (σ : K ≃+* K) :
    (centMod (U₂) (g2FieldHom K σ)).comap (g2Torus K) =
      Subgroup.pi Set.univ fun _ => unitsFix σ := by
  ext a
  rw [Subgroup.mem_comap, mem_centMod, g2FieldHom_g2Torus, ← map_inv, ← map_mul,
    g2Torus_mem_g2U_iff]
  simp only [Subgroup.mem_pi, Set.mem_univ, true_implies, mem_unitsFix]
  refine ⟨fun h i => ?_, fun h => ⟨g2Torus_mem_normalizer ⟨a, rfl⟩, ?_⟩⟩
  · have h1 := congrFun h.2 i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_eq_one] at h1
    exact congrArg Units.val h1
  · funext i
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply, mul_inv_eq_one]
    exact Units.ext (h i)

theorem centMod_g2
    (g : adjointGroup Tag.G2 K)
    (σ : K ≃+* K)
    (h : (U₂).map (MulAut.conj g * g2FieldHom K σ).toMonoidHom = U₂) :
    centMod (U₂) (MulAut.conj g * g2FieldHom K σ) = centMod (U₂) (g2FieldHom K σ) := by
  have hφ : (U₂).map (g2FieldHom K σ).toMonoidHom =
      U₂ := by
    have := (exactNormalAut_mem (τ := Tag.G2) (K := K) 1 σ 0).1
    exact this
  exact centMod_conj_mul_eq g2_comm_mem hφ h

theorem n4At_g2
    [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) : N4At (adjointGroup Tag.G2 K) (U₂) := by
  intro α _ hαU hcent
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨g, σ, rfl⟩ := (g2_automorphism_normal_form hK3 hK4).1 α
  rw [centMod_g2 g σ hαU] at hcent
  have hσ : σ = 1 := by
    rw [← unitsFix_eq_top_iff, eq_top_iff]
    intro t _
    have h1 : (fun _ => t : Fin Tag.G2.rank → Kˣ) ∈
        (centMod (U₂) (g2FieldHom K σ)).comap (g2Torus K) :=
      hcent (g2Torus_mem_normalizer ⟨_, rfl⟩)
    rw [comap_centMod_g2] at h1
    exact h1 ⟨0, Tag.G2.rank_pos⟩ (Set.mem_univ _)
  left
  rw [hσ, map_one, mul_one]
  exact ⟨g, rfl⟩

theorem n2At_g2
    [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) : N2At (adjointGroup Tag.G2 K) (U₂) := by
  intro α _ hαU hidx
  exfalso
  have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; decide
  obtain ⟨g, σ, rfl⟩ := (g2_automorphism_normal_form hK3 hK4).1 α
  rw [centMod_g2 g σ hαU] at hidx
  have := finite_modGL (τ := Tag.G2) (K := K)
  have h1 := index_comap_le (U₂) (g2FieldHom K σ) (g2Torus K) g2Torus_mem_normalizer
  rw [comap_centMod_g2, hidx] at h1
  have hσ := eq_one_of_index_pi_unitsFix_le_three (by rw [Fintype.card_fin]; decide) h1
  rw [hσ, map_one, centMod_one, Subgroup.relIndex_self] at hidx
  omega

theorem isSylowTwoOf_g2U
    [Finite K] [CharP K 2] :
    IsSylowTwoOf (U₂) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := Tag.G2) (K := K)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.G2).length
  obtain ⟨⟨P, hP⟩, -⟩ := exceptional_ordinary_Sylow_opposition Tag.G2 K 2 w₀ hw₀
  rw [← hP]
  exact isSylowTwoOf_sylow P

theorem n2Model_n4Model_of_isG2
    {M : Type} [Group M]
    {n : ℕ} (hn : 1 < n) (h : IsG2 2 n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have := finite_modGL (τ := Tag.G2) (K := K)
  let e' : M ≃* adjointGroup Tag.G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  exact ⟨(N2Model.of_at isSylowTwoOf_g2U (n2At_g2 hK4)).of_mulEquiv e'.symm,
    (N4Model.of_at isSylowTwoOf_g2U (n4At_g2 hK4)).of_mulEquiv e'.symm⟩

end G2

end CFSG.Quasithin.H13.L32A.C.SkPf
