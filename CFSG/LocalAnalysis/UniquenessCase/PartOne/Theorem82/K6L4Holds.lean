module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Out
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Types
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4DiagPSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4DiagPSU
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4CentPSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4CentPSU
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4SubPSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4SubPSU
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate3007
public import Certificates.Certificate10005
public import Certificates.Certificate2326
import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharXfer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open K6L4

private theorem isPGroup_two_statedScalars_subgroupOf {K : Type} [Field K]
    (H : Subgroup (GL (Fin 4) K))
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 4) (Fin 4) K).det = 1) :
    IsPGroup 2 ((StatedScalars (Fin 4) K).subgroupOf H) := by
  intro x
  have hxS : (x.1 : GL (Fin 4) K) ∈ StatedScalars (Fin 4) K := x.2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hxS
  have hc4 : c ^ 4 = 1 := by
    apply Units.ext
    have h1 : ((Matrix.GeneralLinearGroup.scalar (Fin 4) c : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).det = 1 := by
      simpa only [hc] using hdet _ x.1.2
    have h2 : (c : K) ^ 4 = 1 := by
      rwa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal, Matrix.det_smul, Matrix.det_one, Fintype.card_fin,
        mul_one] at h1
    simpa using h2
  refine ⟨2, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show ((x.1 : H) : GL (Fin 4) K) ^ 4 = 1
  rw [← hc, ← map_pow, hc4, map_one]

theorem model_sl {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hZ : Subgroup.center Y = ⊥)
    (hm : LieModel (Y ⧸ Subgroup.center Y) .PSL 4 r 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : StatedSL 4 K →* Y),
      Nat.card K = r ∧ TwoQuot π ∧
        π.ker = (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSL) (by decide)
  rw [pow_one] at hcard
  letI := hK
  letI := hfin
  let N : Subgroup (StatedSL 4 K) := (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)
  let eqY : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let π : StatedSL 4 K →* Y :=
    eqY.toMonoidHom.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' N))
  have hker : π.ker = N := by
    dsimp only [π, N]
    rw [MonoidHom.ker_comp_of_injective _ _ eqY.injective,
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      QuotientGroup.ker_mk']
  have hsurj : Function.Surjective π := by
    dsimp only [π]
    exact eqY.surjective.comp (e.symm.surjective.comp (QuotientGroup.mk'_surjective N))
  refine ⟨K, hK, hfin, π, hcard, ⟨hsurj, ?_, ?_⟩, hker⟩
  · rw [hker]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  · rw [hker]
    exact isPGroup_two_statedScalars_subgroupOf _ fun A hA =>
      CFSG.Open.StatedAPI.det_of_mem_statedSL hA

theorem model_su {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hZ : Subgroup.center Y = ⊥)
    (hm : LieModel (Y ⧸ Subgroup.center Y) .PSU 4 r 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : StatedSU 4 r K →* Y),
      Nat.card K = r ^ 2 ∧ TwoQuot π ∧
        π.ker = (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K) := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := hm.statedClassicalModel (t := .PSU) (by decide)
  letI := hK
  letI := hfin
  have hcard' : Nat.card K = r ^ 2 := by simpa only [pow_one] using hcard
  have hSU : StatedSU 4 (r ^ 1) K = StatedSU 4 r K := by rw [pow_one]
  have he : Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSU 4 r K)) := by
    rw [← hSU]
    exact ⟨e⟩
  obtain ⟨e⟩ := he
  let N : Subgroup (StatedSU 4 r K) := (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 r K)
  let eqY : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let π : StatedSU 4 r K →* Y :=
    eqY.toMonoidHom.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' N))
  have hker : π.ker = N := by
    dsimp only [π, N]
    rw [MonoidHom.ker_comp_of_injective _ _ eqY.injective,
      MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      QuotientGroup.ker_mk']
  have hsurj : Function.Surjective π := by
    dsimp only [π]
    exact eqY.surjective.comp (e.symm.surjective.comp (QuotientGroup.mk'_surjective N))
  refine ⟨K, hK, hfin, π, hcard', ⟨hsurj, ?_, ?_⟩, hker⟩
  · rw [hker]
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  · rw [hker]
    exact isPGroup_two_statedScalars_subgroupOf _ fun A hA =>
      CFSG.Open.StatedAPI.det_of_mem_statedSU hA

set_option linter.unusedSectionVars false


theorem center_eq_bot {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hY : IsLie811 Y .l4 r 1)
    (h5 : 5 ≤ r) : Subgroup.center Y = ⊥ := by
  obtain ⟨hq, hodd, hr', -, hm⟩ := hY
  have h2 : IsPGroup 2 (Subgroup.center Y) := by
    refine CFSG.ComponentClassification.CatFactsL4U4.Cover82.multiplierL4U4 Y hq r 1 hr'
      (by omega) le_rfl ?_
    rcases hm with ⟨-, hm⟩ | ⟨-, hm⟩
    · exact Or.inl hm
    · exact Or.inr ⟨hm, by rw [pow_one]; omega⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hk0 : k = 0 := by
    by_contra hne
    rw [hk] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (by
      rw [Nat.even_pow]
      exact ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem exists_modelFacts {Y : Type} [Group Y] [Finite Y] {r : ℕ} (hY : IsLie811 Y .l4 r 1)
    (h5 : 5 ≤ r) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (H : Subgroup (GL (Fin 4) K)) (ζ : CubeRoot K)
      (π : H →* Y), ModelFacts H ζ r π := by
  have hZ := center_eq_bot hY h5
  obtain ⟨-, -, hr, -, hm⟩ := hY
  rcases hm with ⟨h3, hm⟩ | ⟨h3, hm⟩
  · obtain ⟨K, _, _, π, hK, hπ, hker⟩ := model_sl hZ hm
    rw [pow_one] at h3
    obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd (K := K) (by omega)
    exact ⟨K, inferInstance, inferInstance, StatedSL 4 K, ζ, π, hπ, hker, hr, h5,
      conjFact_sl ζ, centFact_sl hr h5 hK h3 ζ, sub8Fact_sl hr h5 hK ζ, sub9Fact_sl hr h5 hK ζ⟩
  · obtain ⟨K, _, _, π, hK, hπ, hker⟩ := model_su hZ hm
    rw [pow_one] at h3
    obtain ⟨ζ⟩ := CubeRoot.exists_of_dvd (K := K) (by
      have := Nat.pow_mod r 2 3
      rw [h3] at this
      omega)
    exact ⟨K, inferInstance, inferInstance, StatedSU 4 r K, ζ, π, hπ, hker, hr, h5,
      conjFact_su hr hK h3 ζ, centFact_su hr h5 hK h3 ζ, sub8Fact_su hr h5 hK ζ,
      sub9Fact_su hr h5 hK ζ⟩

theorem k6dL4_holds : K6dL4 := by
  intro Y _ _ r hY h5 A hA h27
  obtain ⟨K, _, _, H, ζ, π, hf⟩ := exists_modelFacts hY h5
  exact k6d_of_facts hf hA h27

theorem k6L4_holds : K6L4 := by
  intro Y _ _ r hY h5
  refine ⟨k6L4_out_two hY, ?_⟩
  obtain ⟨K, _, _, H, ζ, π, hf⟩ := exists_modelFacts hY h5
  intro A hA h27 c hc
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := l4Local_of_facts hf A hA h27 c hc
  refine ⟨h₁, h₂, h₃, h₄, ?_, ?_, h₇, h₈, h₉⟩
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h₅
  · rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact h₆

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
