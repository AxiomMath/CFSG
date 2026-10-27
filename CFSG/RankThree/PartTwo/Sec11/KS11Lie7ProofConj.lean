module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2Minus
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding.PairNormalForm
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAlignCores
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.KE.A1Centralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.RF4 CFSG.Quasithin.G2U CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.QuadraticSL2 CFSG.RankThree.Classical
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.HighestRoot
  CFSG.HardMathSupport.Seitz.G2Anisotropic.UnitaryEmbedding

section Pinned

variable {K : Type} [Field K]

theorem mem_g2ShortSL2_of_rootSL2 {y : adjointGroup .G2 K} {A : SL2 K}
    (h : (y : ModGL .G2 K) = rootSL2 .G2 K g2v A) : y ∈ KS11Lie4Proof.g2ShortSL2 K := by
  show (y : ModGL .G2 K) ∈ rootSubgroup .G2 K g2δ ⊔ rootSubgroup .G2 K (-g2δ)
  rw [show (g2δ : Fin Tag.G2.rank → ℤ) = g2v from rfl, ← range_rootSL2_of_isRoot isRoot_g2v, h]
  exact ⟨A, rfl⟩

theorem mem_g2LongSL2_of_rootSL2 {y : adjointGroup .G2 K} {A : SL2 K}
    (h : (y : ModGL .G2 K) = rootSL2 .G2 K g2a A) : y ∈ KS11Lie4Proof.g2LongSL2 K := by
  show (y : ModGL .G2 K) ∈ rootSubgroup .G2 K g2e0 ⊔ rootSubgroup .G2 K (-g2e0)
  rw [show (g2e0 : Fin Tag.G2.rank → ℤ) = g2a from g2a_eq_single.symm,
    ← range_rootSL2_of_isRoot isRoot_g2a, h]
  exact ⟨A, rfl⟩

end Pinned

section Model

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Algebra K K₂] [Finite K₂]
  {σ : K₂ ≃+* K₂}

theorem nonempty_qPlusModel (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K) :
    Nonempty (QPlusModel K σ) := by
  by_cases h2 : ringChar K = 2
  · have : CharP K 2 := ringChar.of_eq h2
    exact QPlusModel.nonempty_of_charTwo hdeg hσ
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' (K := K)
    have hpeq : p = ringChar K := CharP.eq K hcp (ringChar.charP K)
    have hp2 : p ≠ 2 := fun h => h2 (hpeq ▸ h)
    have hpo : Odd p := hp.eq_two_or_odd'.resolve_left hp2
    have hodd : Odd (Nat.card K) := by
      rw [Nat.card_eq_fintype_card, hcard]
      exact hpo.pow
    exact QPlusModel.nonempty_of_odd hodd hdeg hσ

theorem mem_g2ShortSL2_of_twist (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {y : adjointGroup .G2 K} {C : SL2 K₂}
    (h : twistEmb (K := K) M.g y = rootSL2 .G2 K₂ g2v C) : y ∈ KS11Lie4Proof.g2ShortSL2 K := by
  obtain ⟨A, hA⟩ := exists_rootSL2_of_baseChange hdeg hσ (M.baseChange_eq_of_twist_v h)
  exact mem_g2ShortSL2_of_rootSL2 hA

theorem mem_g2LongSL2_of_twist (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) {y : adjointGroup .G2 K} {C : SL2 K₂}
    (h : twistEmb (K := K) M.g y = rootSL2 .G2 K₂ g2a C) : y ∈ KS11Lie4Proof.g2LongSL2 K := by
  obtain ⟨A, hA⟩ := exists_rootSL2_of_baseChange hdeg hσ (M.baseChange_eq_of_twist_a h)
  exact mem_g2LongSL2_of_rootSL2 hA

theorem exists_conj_of_cubeTuple3 (M : QPlusModel K σ)
    (hdeg : Module.finrank K K₂ = 2) (hσ : ∀ c, σ c = c ^ Nat.card K) {ζ : K₂ˣ}
    (hζ : orderOf ζ = 3) {n : adjointGroup .G2 K}
    (hnm : twistEmb (K := K) M.g n ∈ monomialSubgroup .G2 K₂)
    (hnw : weylQuotientHom .G2 K₂ ⟨_, hnm⟩ = rho0) {y : adjointGroup .G2 K} {i j : Fin 3}
    (hy : twistEmb (K := K) M.g y = rootDiagUnit .G2 (cubeTuple3 ζ i j)) :
    ∃ g : adjointGroup .G2 K, g * y * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K ∨
      g * y * g⁻¹ ∈ KS11Lie4Proof.g2LongSL2 K := by
  by_cases hi : i = 0
  · subst hi
    obtain ⟨C, hC⟩ := rootDiagUnit_cubeTuple3_zero_mem_v (ζ := ζ) (L := K₂) j
    refine ⟨1, Or.inl ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_g2ShortSL2_of_twist M hdeg hσ (hy.trans hC)
  · obtain ⟨k, hk⟩ := fin3_shear i j hi
    have hkn : Fin.ofNat 3 k.val = k := Fin.ext (by simp [Fin.ofNat, Nat.mod_eq_of_lt k.2])
    have hψ : twistEmb (K := K) M.g (n ^ k.val * y * (n ^ k.val)⁻¹) =
        rootDiagUnit .G2 (cubeTuple3 ζ i i) := by
      rw [map_mul, map_mul, map_inv, map_pow, hy, conj_pow_cubeTuple3 hζ hnm hnw i j k.val, hkn,
        hk]
    obtain ⟨C, hC⟩ := rootDiagUnit_cubeTuple3_diag_mem_a (L := K₂) hζ i
    exact ⟨n ^ k.val, Or.inr (mem_g2LongSL2_of_twist M hdeg hσ (hψ.trans hC))⟩

theorem exists_central_order_three {G : Type*} [Group G] [Finite G]
    (P : Sylow 3 G) {x : G} (hxP : x ∈ P) (hx1 : x ≠ 1) :
    ∃ e ∈ P, (∀ y ∈ P, y * e = e * y) ∧ e ^ 3 = 1 ∧ e ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial (P : Subgroup G) :=
    ⟨⟨⟨x, hxP⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
  have hPg : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hcnt := hPg.center_nontrivial
  have hcp : IsPGroup 3 (Subgroup.center (P : Subgroup G)) := hPg.to_subgroup _
  obtain ⟨m, hm0, hmcard⟩ := hcp.nontrivial_iff_card.mp hcnt
  have hdvd : 3 ∣ Nat.card (Subgroup.center (P : Subgroup G)) := by
    rw [hmcard]
    exact dvd_pow_self 3 hm0.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hc3 : c ^ 3 = 1 := by
    have h := pow_orderOf_eq_one c
    rwa [hc] at h
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hc
    exact absurd hc (by norm_num)
  refine ⟨((c : P) : G), (c : P).2, fun y hy => ?_, ?_, ?_⟩
  · have h := (Subgroup.mem_center_iff.mp c.2) ⟨y, hy⟩
    exact congrArg Subtype.val h
  · have h := congrArg (fun u : Subgroup.center (P : Subgroup G) => ((u : P) : G)) hc3
    simpa using h
  · intro h
    apply hc1
    apply Subtype.ext
    apply Subtype.ext
    exact h

theorem exists_conj_short_or_long
    (M : QPlusModel K σ) (hdeg : Module.finrank K K₂ = 2)
    (hσ : ∀ c, σ c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) {z : adjointGroup .G2 K}
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) :
    ∃ g : adjointGroup .G2 K, g * z * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K ∨
      g * z * g⁻¹ ∈ KS11Lie4Proof.g2LongSL2 K := by
  have : Finite (Module.End K₂ (RootModule .G2 K₂)) := Module.finite_of_finite K₂
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  have : Finite (adjointGroup .G2 K) := inferInstance
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three_of_finrank hdeg h3
  obtain ⟨P₀, n, hE, hnP, hnm, hnw⟩ := M.exists_sylow_E0G hdeg hσ hζ
  have hzp : IsPGroup 3 (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  obtain ⟨x₁, hx₁⟩ := KS11Lie4Proof.exists_conj_le_sylow' P₀ _ hzp
  set z₁ := x₁ * z * x₁⁻¹ with hz₁
  have hz₁P : z₁ ∈ P₀ := hx₁ ⟨z, Subgroup.mem_zpowers z, rfl⟩
  have hz₁1 : z₁ ≠ 1 := fun h => hz1 (by simpa [hz₁] using h)
  have hz₁3 : z₁ ^ 3 = 1 := by simp [hz₁, conj_pow, hz3]
  suffices hsuff : ∃ g : adjointGroup .G2 K, g * z₁ * g⁻¹ ∈ KS11Lie4Proof.g2ShortSL2 K ∨
      g * z₁ * g⁻¹ ∈ KS11Lie4Proof.g2LongSL2 K by
    obtain ⟨g, hg⟩ := hsuff
    refine ⟨g * x₁, ?_⟩
    have e : g * x₁ * z * (g * x₁)⁻¹ = g * z₁ * g⁻¹ := by rw [hz₁]; group
    rw [e]
    exact hg
  obtain ⟨e, heP, hec, he3, he1⟩ := exists_central_order_three P₀ hz₁P hz₁1
  by_cases hez : e ∈ Subgroup.zpowers z₁
  ·
    have hord : orderOf z₁ = 3 := orderOf_eq_prime hz₁3 hz₁1
    have hordE : orderOf e = 3 := orderOf_eq_prime he3 he1
    have hle : Subgroup.zpowers e ≤ Subgroup.zpowers z₁ :=
      (Subgroup.zpowers_le (G := adjointGroup .G2 K)).mpr hez
    have heq : Subgroup.zpowers e = Subgroup.zpowers z₁ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordE])
    obtain ⟨k, hk⟩ : z₁ ∈ Subgroup.zpowers e := by rw [heq]; exact Subgroup.mem_zpowers z₁
    have hzc : ∀ x ∈ P₀, x * z₁ = z₁ * x := by
      intro x hx
      rw [← hk]
      exact (Commute.zpow_right (show Commute x e from hec x hx) k).eq
    obtain ⟨j, -, hψ⟩ := M.central_mem_E0 hσ h3 hζ hE hnP hnm hnw hzc hz₁1 hz₁3
    exact exists_conj_of_cubeTuple3 M hdeg hσ hζ hnm hnw hψ
  ·
    have hcomm : z₁ * e = e * z₁ := hec z₁ hz₁P
    obtain ⟨E, hzE, -, hEel, hEcard⟩ := exists_plane_of_pair hcomm hz₁3 he3 hz₁1 hez
    have := hEel
    obtain ⟨y, hyΓ, hy⟩ := M.exists_conj_plane_to_torsion hdeg hσ h3 E hEcard
    obtain ⟨y₀, rfl⟩ := M.exists_twistEmb_eq hyΓ
    have hz₂E : twistEmb (K := K) M.g (y₀ * z₁ * y₀⁻¹) ∈ torusTorsion K₂ 3 := by
      have : (MulAut.conj (twistEmb (K := K) M.g y₀)).toMonoidHom (twistEmb (K := K) M.g z₁) ∈
          (E.map (twistEmb (K := K) M.g)).map
            (MulAut.conj (twistEmb (K := K) M.g y₀)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzE)
      rw [hy] at this
      simpa [MulAut.conj_apply, map_mul, map_inv] using this
    obtain ⟨i, j, hψ⟩ := exists_cubeTuple3_of_mem_torusTorsion hζ hz₂E
    obtain ⟨g, hg⟩ := exists_conj_of_cubeTuple3 M hdeg hσ hζ hnm hnw hψ
    refine ⟨g * y₀, ?_⟩
    have e : g * y₀ * z₁ * (g * y₀)⁻¹ = g * (y₀ * z₁ * y₀⁻¹) * g⁻¹ := by group
    rw [e]
    exact hg

end Model

theorem g2ThreeConjSL2Minus_holds :
    KS11Lie4Proof.G2ThreeConjSL2Minus := by
  intro K _ _ h3 _ z hz3 hz1
  obtain ⟨K₂, _, _, hdeg, σ, hσ⟩ := exists_quadratic_frobenius_all K
  have : Finite K₂ := (quadratic_frobenius hdeg σ hσ).1
  obtain ⟨M⟩ := nonempty_qPlusModel hdeg hσ
  exact exists_conj_short_or_long M hdeg hσ h3 hz3 hz1

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
