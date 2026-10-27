module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95A3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E1
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_gB_L2 {Q : Type} [Group Q] [Finite Q] {p f : ℕ}
    (hQ : LieModel Q .PSL 2 p f) (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P)
    {E : Subgroup Q} (hE : HasL32Quot E) {W : Subgroup Q} (hEW : E ≤ W)
    (hNW : ∀ D : Subgroup Q, D ≤ E → Nat.card D = 3 → normalizer (D : Set Q) ≤ W) :
    W = ⊤ := by
  obtain ⟨A, hAE, hA⟩ := r95_exists_order_three_of_hasL32Quot hE
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  haveI : Finite Qm := Finite.of_surjective π hπ
  have hp7 : p = 7 := r95_char_seven_of_section hQ π hπ hm
  obtain ⟨⟨hp, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hQ.statedClassicalModel (by decide)
  haveI : Fact p.Prime := ⟨hp⟩
  let e : Q ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F :=
    eF.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  obtain ⟨hsimple, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  have hnc : ¬ IsMulCommutative Qm := fun _ => by
    have hpr := (Group.is_simple_iff_prime_card (α := Qm)).mp hsimple
    rw [hcard] at hpr
    norm_num at hpr
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW : ¬ CFSG.HallHigman.IsPSolvable 3 ↥W := fun hW3 =>
    CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.false_of_isPSolvable_surj
      (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (p := 3) (X := Q) (N := W) (Y := E) hW3 hEW)
      ⊤ (π.comp (Subgroup.topEquiv (G := ↥E)).toMonoidHom)
      (hπ.comp (Subgroup.topEquiv (G := ↥E)).surjective) hsimple hnc (by rw [hcard]; norm_num)
  have hL2 : CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.OvergroupEqTop
      (CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.overgroupEqTop_psl2 hF
      (by rw [hp7]; norm_num : p ≠ 3)
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv
    e hL2 hcyc A W hA (hNW A hAE hA) hW

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
