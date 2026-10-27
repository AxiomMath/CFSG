module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

theorem kFactL28_L2_even {Q : Type} [Group Q] [Finite Q] {f : ℕ}
    (hQ : LieModel Q .PSL 2 2 f) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 ↥P → IsCyclic ↥P)
    {X W T : Subgroup Q} (c : KCfgL28 X W T) : W = ⊤ := by
  have hcard504 : Nat.card (Bar2 X) = 504 := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hsimple : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) c.isL2
  have hnc : ¬ IsMulCommutative (Bar2 X) := fun _ => by
    have hpr := (Group.is_simple_iff_prime_card (α := Bar2 X)).mp hsimple
    rw [hcard504] at hpr
    norm_num at hpr
  have hdvd : Nat.card (Bar2 X) ∣ Nat.card ↥X :=
    Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥X)
  have h3X : 3 ∣ Nat.card ↥X :=
    dvd_trans (by rw [hcard504]; norm_num) hdvd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3X
  let A : Subgroup Q := (Subgroup.zpowers x).map X.subtype
  have hAX : A ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA3 : Nat.card A = 3 := by
    rw [Subgroup.card_map_of_injective X.subtype_injective, Nat.card_zpowers, hx]
  have hW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := fun hW3 =>
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.false_of_isPSolvable_surj
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (p := 3) (X := Q) (N := W) (Y := X) hW3 c.X_le)
      ⊤ ((QuotientGroup.mk' (CFSG.pCore 2 ↥X)).comp
        (Subgroup.topEquiv (G := ↥X)).toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp (Subgroup.topEquiv (G := ↥X)).surjective)
      hsimple hnc (by rw [hcard504]; norm_num)
  obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hQ.statedClassicalModel (by decide)
  have hL2 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.OvergroupEqTop
      (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 (p := 2) hF
      (by norm_num : (2 : ℕ) ≠ 3)
  have e : Q ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv
    e hL2 hcyc A W hA3 (c.N3 A hAX hA3) hW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
