module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1CitedDefs
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRest
import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank
import CFSG.GH74.GLS.Stage2.Local.GHSchLie
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.SectionRank.SectionAssembly
import CFSG.Quasithin.Background.A1cModuleCoprime
import CFSG.Quasithin.Background.A3Structure312Facts
import CFSG.Quasithin.Background.OrderingMax
import CFSG.Quasithin.Vol2.Ch1Local
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem ggU_perfect_lieModel_PSL_two
    {f : ℕ} (hadm : StatedLieAdmissible .PSL 2 2 f) :
    commutator (ggU .PSL 2 f).K = ⊤ ∧
      LieModel ((ggU .PSL 2 f).K ⧸ Subgroup.center (ggU .PSL 2 f).K) .PSL 2 2 f := by
  have hf : 2 ≤ f := by
    have h1 := hadm.2.1
    have h22 := hadm.2.2.2.1
    by_contra h
    obtain rfl : f = 1 := by omega
    exact h22 (by decide)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [hcard]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  exact ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top,
    Or.inl ⟨by simp [classicalTags],
      SpecialLinear.statedClassicalModel_center_quotient 1 (GaloisField 2 f) hadm hcard⟩⟩

private theorem lieModel_range_centerQuot_of
    {G : Type} [Group G] {t : StatedLieTag} {n f : ℕ}
    (hU : commutator (ggU t n f).K = ⊤ ∧
      LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f)
    (ψ : (ggU t n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) :
    LieModel (↥ψ.range ⧸ Subgroup.center ↥ψ.range) t n 2 f := by
  obtain ⟨hperf, hmodel⟩ := hU
  have hZ : Subgroup.center ↥ψ.range = (Subgroup.center (ggU t n f).K).map ψ.rangeRestrict := by
    ext l
    obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
    constructor
    · intro hu
      exact ⟨u, InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker hu, rfl⟩
    · rintro ⟨v, hv, hvu⟩
      rw [← hvu, Subgroup.mem_center_iff]
      intro l'
      obtain ⟨w, rfl⟩ := ψ.rangeRestrict_surjective l'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hv w]
  exact lieModel_of_mulEquiv' (CFSG.LieType.CurtisTits.centerQuotientEquivOfSurjective
    ψ.rangeRestrict ψ.rangeRestrict_surjective (by rw [MonoidHom.ker_rangeRestrict]; exact hker)
    hZ) hmodel

theorem ggSplitLieOutInput_holds :
    GGSplitLieOutInput := by
  rintro G _ _ p X ⟨t, n, f, ψ, hadm, hker, hrange, htag, -⟩
  subst hrange
  have hU : commutator (ggU t n f).K = ⊤ ∧
      LieModel ((ggU t n f).K ⧸ Subgroup.center (ggU t n f).K) t n 2 f := by
    rcases htag with rfl | rfl | rfl | rfl | rfl
    · by_cases hn : n = 2
      · subst hn
        exact ggU_perfect_lieModel_PSL_two hadm
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
        exact ggU_perfect_lieModel hadm (show 2 ≤ m by have := hadm.2.2.1; omega)
    · exact ggU_perfect_lieModel hadm (two_le_lieUniversal_rank _ n 2 f Nat.prime_two hadm
        (by simp only [bnRank]; have := hadm.2.2; omega))
    all_goals
      exact ggU_perfect_lieModel hadm
        (two_le_lieUniversal_rank _ n 2 f Nat.prime_two hadm (by simp [bnRank]))
  have : Group.IsPerfect ↥ψ.range := ⟨by
    have h1 : (commutator (ggU t n f).K).map ψ.rangeRestrict = commutator ↥ψ.range := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top_of_surjective _ ψ.rangeRestrict_surjective, commutator_def]
    rw [← h1, hU.1, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ ψ.rangeRestrict_surjective]⟩
  have htag' : t ≠ .twistedF4 ∧ t ≠ .Tits := by
    rcases htag with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  have : Group.IsSolvable (Outer (↥ψ.range ⧸ Subgroup.center ↥ψ.range)) :=
    CFSG.GH74.GLS.Stage2.Local.GHSch.lieModel_outer_solvable htag'
      (lieModel_range_centerQuot_of hU ψ hker)
  exact CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
    (CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_centerQuotient ↥ψ.range)

end CFSG.StandardType

end
