module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldDefs
public import Certificates.Certificate113
public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.StandardType.MarkingSmall
import CFSG.RankThree.PartTwo.KFacts.AutSz
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.StronglyEmbedded.ParityCriterion

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint

namespace RecipeFieldSpU

theorem commutator_mem_inn_of_mulEquiv {R S : Type*} [Group R] [Group S] (e : R ≃* S)
    (h : ∀ α β : MulAut S, α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : S →* MulAut S).range)
    (α β : MulAut R) : α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨s, hs⟩ := h (MulAut.congr e α) (MulAut.congr e β)
  refine ⟨e.symm s, (MulAut.congr e).injective ?_⟩
  rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hs, map_mul, map_mul, map_mul, map_inv,
    map_inv]

variable {a : ℕ} {K : Type} [Field K]

theorem commutator_mem_inn_suzuki [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (α β : MulAut (suzukiGroup a K)) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : suzukiGroup a K →* MulAut _).range := by
  refine commutator_mem_of_eq_mul _
    (Set.range (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K)) ?_ ?_ ?_ α β
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite]
  · rintro x - d hd
    exact (ggInnNormal _).conj_mem d hd x
  · intro γ
    obtain ⟨g, σ, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK γ
    exact ⟨MulAut.conj g, ⟨g, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩

theorem ggRawFieldCentral_suzuki [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGRawFieldCentral (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  intro _ hR α u _ f _
  obtain ⟨e₁⟩ := nonempty_centerQuot_congr (largeEvenSzGroup_eq a K)
  have : IsSimpleGroup (suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple ha hK).2.2
  obtain ⟨e₂⟩ := nonempty_centerQuot_equiv_of_isSimpleGroup (H := suzukiGroup a K)
    (nonabelian_of_mulEquiv e₁ hR)
  exact commutator_mem_inn_of_mulEquiv (e₁.trans e₂) (commutator_mem_inn_suzuki ha hK) α (u * f)

end RecipeFieldSpU

open RecipeFieldSpU

theorem ggRawFieldCentralOn_twB2 :
    GGRawFieldCentralOn fun lab => lab.tag = .twB2 := by
  intro lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawFieldCentral_suzuki (by omega) hK⟩

end CFSG.StandardType
