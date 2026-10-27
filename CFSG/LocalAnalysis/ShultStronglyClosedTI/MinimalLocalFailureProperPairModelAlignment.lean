module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneBorelAlignment

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.BorelAlignment CFSG.ShultStronglyClosedTI.CyclicPair MulAction

universe u

theorem isBorelSubgroup_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {X : Subgroup A} (hX : IsBorelSubgroup X) :
    IsBorelSubgroup (X.map e.toMonoidHom) := by
  obtain ⟨hsolv, S, rfl⟩ := hX
  let : Group.IsSolvable (Subgroup.normalizer ((S : Subgroup A) : Set A)) := hsolv
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S, ?_⟩
  · let f := (Subgroup.normalizer ((S : Subgroup A) : Set A)).equivMapOfInjective e.toMonoidHom
      e.injective
    exact Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
  · have hcoe : ((Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S : Sylow 2 B) :
        Subgroup B) = (S : Subgroup A).map e.toMonoidHom :=
      Sylow.coe_mapSurjective _ _
    rw [hcoe, Subgroup.map_equiv_normalizer_eq]

variable {G : Type u} [Group G]

theorem rightConjugate_subgroupOf_eq_map (H K : Subgroup G) {t : G} (htK : t ∈ K) :
    (rightConjugate H t).subgroupOf K =
      (H.subgroupOf K).map (MulAut.conj (⟨t, htK⟩ : K)⁻¹).toMonoidHom := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ H.map (MulAut.conj t⁻¹).toMonoidHom at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyK : y ∈ K := by
      have hyeq : y = t * (x : G) * t⁻¹ := by
        rw [← hyx]
        simp [mul_assoc]
      rw [hyeq]
      exact K.mul_mem (K.mul_mem htK x.property) (K.inv_mem htK)
    refine Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, hy, ?_⟩
    apply Subtype.ext
    simpa using hyx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    change (x : G) ∈ H.map (MulAut.conj t⁻¹).toMonoidHom
    refine Subgroup.mem_map.mpr ⟨(y : G), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa using this

variable [Finite G]

theorem proper_pair_borel_images
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let π := QuotientGroup.mk' (CFSG.oddCore K)
    IsBorelSubgroup ((H.subgroupOf K).map π) ∧
      IsBorelSubgroup (((rightConjugate H t).subgroupOf K).map π) ∧
      (H.subgroupOf K).map π ≠ ((rightConjugate H t).subgroupOf K).map π := by
  intro K π
  obtain ⟨-, -, hcore, hB⟩ := proper_pair_native_model_and_borel h hcomm hsmallerR1 hbeta ht hproper
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  let tK : K := ⟨t, htK⟩
  have hconjM := rightConjugate_subgroupOf_eq_map H K htK
  have himage : ((rightConjugate H t).subgroupOf K).map π =
      ((H.subgroupOf K).map π).map (MulAut.conj (π tK)⁻¹).toMonoidHom := by
    rw [hconjM, Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine ⟨hB, ?_, ?_⟩
  · rw [himage]
    exact isBorelSubgroup_map_mulEquiv (MulAut.conj (π tK)⁻¹) hB
  · intro heq
    have hzK : z ∈ K := minimalLocalFailureProperPair_distinguished_mem H z beta t
    let zK : K := ⟨z, hzK⟩
    have hzM : zK ∈ H.subgroupOf K := h.local_datum.distinguished_mem
    have hπz : π zK ∈ ((rightConjugate H t).subgroupOf K).map π := by
      rw [← heq]
      exact Subgroup.mem_map_of_mem π hzM
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hπz
    have hcoreMt : CFSG.oddCore K ≤ (rightConjugate H t).subgroupOf K := by
      rw [hconjM]
      intro c hc
      refine Subgroup.mem_map.mpr ⟨(MulAut.conj tK) c, ?_, ?_⟩
      · exact hcore ((inferInstance : (CFSG.oddCore K).Normal).conj_mem c hc tK)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, tK]
        group
    have hdiff : y⁻¹ * zK ∈ CFSG.oddCore K := by
      have := (QuotientGroup.eq (s := CFSG.oddCore K)).mp hyz
      exact this
    have hzMt : zK ∈ (rightConjugate H t).subgroupOf K := by
      have := Subgroup.mul_mem _ hy (hcoreMt hdiff)
      simpa using this
    have hzHt : z ∈ rightConjugate H t := hzMt
    exact pair_flip_not_mem_point hbeta ht ((h.local_datum.unique_containment t).mp hzHt)

theorem proper_pair_model_alignment
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]
    (e : minimalLocalFailureProperPairHull H z beta t ⧸
      CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) ≃* P)
    (S₀ : Sylow 2 P) (p₀ : Ω)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = stabilizer P p₀)
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    (a₀ a₁ : Ω) (ha : a₀ ≠ a₁) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let π := QuotientGroup.mk' (CFSG.oddCore K)
    ∃ ψ : K ⧸ CFSG.oddCore K ≃* P,
      ((H.subgroupOf K).map π).map ψ.toMonoidHom = stabilizer P a₀ ∧
        (((rightConjugate H t).subgroupOf K).map π).map ψ.toMonoidHom = stabilizer P a₁ := by
  intro K π
  obtain ⟨hB₁, hB₂, hne⟩ := proper_pair_borel_images h hcomm hsmallerR1 hbeta ht hproper
  have hne' : ((H.subgroupOf K).map π).map e.toMonoidHom ≠
      (((rightConjugate H t).subgroupOf K).map π).map e.toMonoidHom := fun heq =>
    hne (Subgroup.map_injective e.injective heq)
  obtain ⟨g, hg₁, hg₂⟩ := borel_pair_alignment S₀ p₀ hS₀ htwo
    (isBorelSubgroup_map_mulEquiv e hB₁) (isBorelSubgroup_map_mulEquiv e hB₂) hne' a₀ a₁ ha
  refine ⟨e.trans (MulAut.conj g), ?_, ?_⟩
  · rw [← hg₁, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rfl
  · rw [← hg₂, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    rfl

end CFSG.ShultStronglyClosedTI.ProperPairModel
