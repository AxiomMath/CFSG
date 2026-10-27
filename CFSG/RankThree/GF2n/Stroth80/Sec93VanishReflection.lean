module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishRank
public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishDickson
public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishTau
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Quasithin.G11.P3Ortho.Om4
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem Ψ_mem_determinantIsometries {K : Type} [Field K] {A : GL (Fin 2 ⊕ Fin 2) K}
    (h : ∀ v, StatedQuadPlus 2 K ((A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      StatedQuadPlus 2 K v) : Ψ K A ∈ DeterminantIsometries K := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro Y
  have hY : Y.det = StatedQuadPlus 2 K ((toMat K).symm Y) := by
    rw [← det_toMat, LinearEquiv.apply_symm_apply]
  rw [determinantForm_apply, determinantForm_apply, Ψ_apply, det_toMat, h, hY]

theorem rank_toLin'_sub_id_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : GL (Fin 2 ⊕ Fin 2) K}
    (hXiso : ∀ v, StatedQuadPlus 2 K ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      StatedQuadPlus 2 K v)
    (hXX : ∀ v, (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v)
    (hXne : ∃ v, (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ≠ v)
    (hns : ∀ v, StatedQuadPlus 2 K ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v) = 0 →
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v = 0) :
    Module.finrank K (LinearMap.range (Matrix.toLin'
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - LinearMap.id)) = 1 := by
  have hq : ⇑(quadPlus 2 K) = StatedQuadPlus 2 K := coe_quadPlus 2 K
  have hle := rank_le_one_of_nonsingular_image (polarBilin (quadPlus 2 K)) (StatedQuadPlus 2 K)
    (fun a v => by
      rw [← hq, QuadraticMap.map_smul, smul_eq_mul]
      ring)
    (fun v w => by
      rw [← hq, QuadraticMap.map_add (quadPlus 2 K) v w, polarBilin_apply_apply])
    (fun v => by
      rw [polarBilin_apply_apply, polar_self, CharTwo.two_nsmul])
    (Matrix.toLin' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
    (fun v => by rw [Matrix.toLin'_apply]; exact hXiso v)
    (fun v => by simp only [Matrix.toLin'_apply]; exact hXX v)
    (fun v => by simp only [Matrix.toLin'_apply]; exact hns v)
  obtain ⟨v, hv⟩ := hXne
  set g : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K) :=
    Matrix.toLin' (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hg
  have hpos : 0 < Module.finrank K (LinearMap.range (g - LinearMap.id)) := by
    apply Submodule.one_le_finrank_iff.mpr
    intro h
    apply hv
    have hmem : (g - LinearMap.id : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K)) v ∈
        LinearMap.range (g - LinearMap.id) := LinearMap.mem_range_self _ v
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, hg, Matrix.toLin'_apply, LinearMap.id_apply,
      sub_eq_zero] at hmem
    exact hmem
  omega

theorem exists_conj_notMem_of_reflection {K : Type} [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) (X : GL (Fin 2 ⊕ Fin 2) K)
    (hXiso : ∀ v, StatedQuadPlus 2 K ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      StatedQuadPlus 2 K v)
    (hXX : ∀ v, (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
      ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) = v)
    (hXne : ∃ v, (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ≠ v)
    (hns : ∀ v, StatedQuadPlus 2 K ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v) = 0 →
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v + v = 0)
    (A : Subgroup (GL (Fin 2 ⊕ Fin 2) K)) (hAΩ : A ≤ StatedOmega (StatedQuadPlus 2 K))
    (hAnorm : ∀ g ∈ StatedOmega (StatedQuadPlus 2 K), ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hA0 : A ≠ ⊥) (hAΩ' : A ≠ StatedOmega (StatedQuadPlus 2 K)) :
    ∃ a ∈ A, X * a * X⁻¹ ∉ A := by
  by_contra hcon
  push Not at hcon
  have hrank := rank_toLin'_sub_id_eq_one hXiso hXX hXne hns
  have hXΩ : X ∉ StatedOmega (StatedQuadPlus 2 K) := by
    intro hX
    have h := even_finrank_of_mem_statedOmega h4 hX
    rw [hrank] at h
    exact Nat.not_even_one h
  have hXX1 : (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro w
    rw [Matrix.toLin'_mul, Matrix.toLin'_one]
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearMap.id_apply]
    exact hXX w
  have hXinv : X⁻¹ = X := inv_eq_of_mul_eq_one_right (Units.ext hXX1)
  have hΨiso : Ψ K X ∈ DeterminantIsometries K := Ψ_mem_determinantIsometries hXiso
  have hrange : (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom = (rho' K).range :=
    map_statedOmega.trans (commutator_eq_range h4)
  have hΨX : Ψ K X ∉ (rho' K).range := by
    rw [← hrange]
    intro h
    obtain ⟨y, hy, hyX⟩ := Subgroup.mem_map.mp h
    have hyX' : y = X := (Ψ K).injective hyX
    exact hXΩ (hyX' ▸ hy)
  rcases mem_specialImage_or_mul_tau (⟨Ψ K X, hΨiso⟩ : DeterminantIsometries K) with h | h
  · obtain ⟨z, hz⟩ := h
    exact hΨX ⟨z, congrArg Subtype.val hz⟩
  obtain ⟨z, hz⟩ := h
  have hz' : rho' K z = Ψ K X * (tau (K := K)).val := congrArg Subtype.val hz
  have hτ : (tau (K := K)).val = (Ψ K X)⁻¹ * rho' K z := by
    rw [hz', inv_mul_cancel_left]
  have hΨinv : (Ψ K X)⁻¹ = Ψ K X := by rw [← map_inv, hXinv]
  set N : Subgroup (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
    A.map (Ψ K).toMonoidHom with hN
  have hNJ : N ≤ (rho' K).range := by
    rw [← hrange]
    exact Subgroup.map_mono hAΩ
  have hnorm : ∀ g ∈ (rho' K).range, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    rw [← hrange] at hg
    obtain ⟨ω, hω, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨ω * a * ω⁻¹, hAnorm ω hω a ha, ?_⟩
    simp
  have htau : ∀ n ∈ N, (tau (K := K)).val * n * ((tau (K := K)).val)⁻¹ ∈ N := by
    intro n hn
    have hn' : rho' K z * n * (rho' K z)⁻¹ ∈ N := hnorm _ ⟨z, rfl⟩ n hn
    obtain ⟨a, ha, hafe⟩ := Subgroup.mem_map.mp hn'
    have hcalc : (Ψ K X)⁻¹ * rho' K z * n * ((Ψ K X)⁻¹ * rho' K z)⁻¹ =
        (Ψ K X)⁻¹ * (rho' K z * n * (rho' K z)⁻¹) * ((Ψ K X)⁻¹)⁻¹ := by group
    rw [hτ, hcalc, ← hafe]
    refine Subgroup.mem_map.mpr ⟨X * a * X⁻¹, hcon a ha, ?_⟩
    rw [hΨinv]
    simp
  have hinj : Function.Injective (Ψ K).toMonoidHom := (Ψ K).injective
  rcases tau_invariant_normal_eq h4 N hNJ hnorm htau with h0 | hall
  · apply hA0
    exact (Subgroup.map_eq_bot_iff_of_injective A hinj).mp h0
  · apply hAΩ'
    apply Subgroup.map_injective hinj
    rw [hrange]
    exact hall

end CFSG.RankThree.GF2n.Stroth80
