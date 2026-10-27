module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairNotUnitary
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearPerfect
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearModelPointStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.CyclicPair

variable {G : Type} [Group G] [Finite G]

theorem ker_comp_mk'_oddCore {K D : Type*} [Group K] [Group D]
    (e : K ⧸ CFSG.oddCore K ≃* D) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.oddCore K))).ker = CFSG.oddCore K := by
  ext x
  simp

theorem proper_pair_hull_linear_or_suzuki_iso
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let K := minimalLocalFailureProperPairHull H z beta t
    Group.IsPerfect K ∧ CFSG.oddCore K = ⊥ ∧
      ∃ a : ℕ, 2 ≤ a ∧
        (Nonempty (K ≃* PSL2BinaryMatrixGroup a) ∨
          ∃ m : ℕ, a = 2 * m + 1 ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) := by
  intro K
  have hperfect : Group.IsPerfect K := original_proper_pair_perfect h hcomm hbeta ht hproper
  obtain ⟨-, -, -, -, hcenter, hodd, -⟩ := proper_pair_recognition h hcomm hsmallerR1 hbeta ht hproper
  have hcentral : CFSG.oddCore K ≤ Subgroup.center K := hcenter.symm.le
  have hoddcore : Odd (Nat.card (CFSG.oddCore K)) := hcenter ▸ hodd
  obtain ⟨a, ha, hmodel, -⟩ := proper_pair_full_inversion_torus h hcomm hsmallerR1 hbeta ht hproper
  let π := QuotientGroup.mk' (CFSG.oddCore K)
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨E, hE, hEfin, J, hJ, hcard, hfixed, ⟨e⟩⟩
  · let η := e.toMonoidHom.comp π
    have hker : η.ker = CFSG.oddCore K := ker_comp_mk'_oddCore e
    obtain ⟨hbot, iso, -⟩ := perfect_linear_odd_cover a ha η (e.surjective.comp hπsurj)
      (hker ▸ hcentral) (hker ▸ hoddcore)
    exact ⟨hperfect, hker ▸ hbot, a, ha, Or.inl ⟨iso⟩⟩
  · let η := e.toMonoidHom.comp π
    have hker : η.ker = CFSG.oddCore K := ker_comp_mk'_oddCore e
    obtain ⟨hbot, iso, -⟩ := perfect_suzuki_odd_cover m η (e.surjective.comp hπsurj)
      (hker ▸ hcentral) (hker ▸ hoddcore)
    exact ⟨hperfect, hker ▸ hbot, a, ha, Or.inr ⟨m, hm, ⟨iso⟩⟩⟩
  · exact ((proper_pair_hull_quotient_not_unitary h hcomm hsmallerR1 hbeta ht hproper J a ha
      hcard hfixed hJ).false e).elim

theorem exists_mulEquiv_quotient_oddCore_of_eq_bot {K : Type*} [Group K]
    (hO : CFSG.oddCore K = ⊥) :
    ∃ π' : K ≃* K ⧸ CFSG.oddCore K, ∀ x, π' x = QuotientGroup.mk' (CFSG.oddCore K) x :=
  ⟨QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm),
    fun _ => rfl⟩

theorem proper_pair_hull_aligned_iso
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hO : CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) = ⊥)
    {P Ω : Type*} [Group P] [Finite P] [MulAction P Ω]
    (e : minimalLocalFailureProperPairHull H z beta t ≃* P)
    (S₀ : Sylow 2 P) (p₀ : Ω)
    (hS₀ : Subgroup.normalizer ((S₀ : Subgroup P) : Set P) = MulAction.stabilizer P p₀)
    (htwo : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : P, g • a = c ∧ g • b = d)
    (a₀ a₁ : Ω) (ha : a₀ ≠ a₁) :
    let K := minimalLocalFailureProperPairHull H z beta t
    ∃ ψ : K ≃* P, (H.subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₀ ∧
      ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom = MulAction.stabilizer P a₁ := by
  intro K
  obtain ⟨π', hπ'⟩ := exists_mulEquiv_quotient_oddCore_of_eq_bot hO
  obtain ⟨ψ', hψ₀, hψ₁⟩ := proper_pair_model_alignment h hcomm hsmallerR1 hbeta ht hproper
    (π'.symm.trans e) S₀ p₀ hS₀ htwo a₀ a₁ ha
  have hπcomp : π'.toMonoidHom = QuotientGroup.mk' (CFSG.oddCore K) := MonoidHom.ext hπ'
  refine ⟨π'.trans ψ', ?_, ?_⟩
  · rw [← hψ₀, Subgroup.map_map, ← hπcomp]
    rfl
  · rw [← hψ₁, Subgroup.map_map, ← hπcomp]
    rfl

theorem proper_pair_hull_linear_aligned
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hO : CFSG.oddCore (minimalLocalFailureProperPairHull H z beta t) = ⊥)
    {a : ℕ} (ha : 2 ≤ a)
    (e : minimalLocalFailureProperPairHull H z beta t ≃* PSL2BinaryMatrixGroup a) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let k := BinaryGaloisField a
    ∃ ψ : K ≃* PSL2MatrixGroup k,
      (H.subgroupOf K).map ψ.toMonoidHom = CFSG.GorensteinWalter.psl2Borel k ∧
      ((rightConjugate H t).subgroupOf K).map ψ.toMonoidHom =
        MulAction.stabilizer (PSL2MatrixGroup k) (CFSG.GorensteinWalter.psl2ProjectiveZero k) := by
  intro K k
  have hcard : Nat.card k = 2 ^ a := by
    simpa [k, BinaryGaloisField] using GaloisField.card 2 a (by omega)
  obtain ⟨S₀, hS₀U⟩ := LinearModel.exists_sylow_eq_rootGroup (K := k) hcard
  have hS₀ : Subgroup.normalizer ((S₀ : Subgroup (PSL2MatrixGroup k)) : Set (PSL2MatrixGroup k)) =
      MulAction.stabilizer (PSL2MatrixGroup k) (CFSG.GorensteinWalter.psl2ProjectiveInfinity k) := by
    rw [hS₀U]
    exact CFSG.GorensteinWalter.psl2UpperUnipotent_normalizer_eq_borel k
  have htwo := (LinearModel.linear_rank_one_point_structure (K := k) a ha hcard).2.1
  have htwo' : ∀ a b c d : Projectivization k (Fin 2 → k), a ≠ b → c ≠ d →
      ∃ g : PSL2MatrixGroup k, g • a = c ∧ g • b = d :=
    fun _ _ _ _ hab hcd => MulAction.is_two_pretransitive_iff.mp htwo hab hcd
  exact proper_pair_hull_aligned_iso h hcomm hsmallerR1 hbeta ht hproper hO e S₀
    (CFSG.GorensteinWalter.psl2ProjectiveInfinity k) hS₀ htwo'
    (CFSG.GorensteinWalter.psl2ProjectiveInfinity k) (CFSG.GorensteinWalter.psl2ProjectiveZero k)
    LinearModel.infinity_ne_zero

end CFSG.ShultStronglyClosedTI.ProperPairModel
