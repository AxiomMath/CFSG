module

public import CFSG.RankThree.PartTwo.Sec15.F153L3KOutRed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
public import CFSG.Adapters.RankThreeOutcomesReverse

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

theorem noOuterIrr_U3
    {f : ℕ} (h2f : 2 < 2 ^ f) {Y : Type} [Group Y]
    (hY : Nonempty (Y ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 f)) :
    NoOuterIrrFFOffender Y := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hN hne hel hquad hEL h4
  have hf : 2 ≤ f := by
    by_contra h
    have : f = 0 ∨ f = 1 := by omega
    rcases this with rfl | rfl <;> norm_num at h2f
  have hne3 : (3, 2 ^ f) ≠ (3, 2) := fun he => by
    rw [(Prod.mk.inj he).2] at h2f
    exact lt_irrefl _ h2f
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2 f :=
    CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSU (n := 3) (p := 2) (f := f)
      ⟨Nat.prime_two, by omega, by norm_num, hne3⟩ (e.trans hY.some)
  exact X5.evenUnitaryThreeNoOffender f hf W hW hirr.1 L E hq.1 hirr.2 hmodel hne hel hN

theorem outTwoRank_of_isLThreeEpsAt {f : ℕ} (hf : 1 ≤ f) {T : Type} [Group T]
    (h : Nonempty (T ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 f)) ∨
      (2 < 2 ^ f ∧ Nonempty (T ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 f))) :
    CFSG.HardMathSupport.Cooperstein.StructureLie.OutTwoRank T := by
  rcases h with ⟨⟨e⟩⟩ | ⟨h2, ⟨e⟩⟩
  · exact CFSG.HardMathSupport.Cooperstein.StructureLie.outTwoRank_PSL_ge_three (le_refl 3)
      (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL (n := 3) (p := 2) (f := f)
        ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩ e)
  · have hne3 : (3, 2 ^ f) ≠ (3, 2) := fun he => by
      rw [(Prod.mk.inj he).2] at h2
      exact lt_irrefl _ h2
    exact CFSG.HardMathSupport.Cooperstein.StructureLie.outTwoRank_PSU
      (CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSU (n := 3) (p := 2) (f := f)
        ⟨Nat.prime_two, hf, by norm_num, hne3⟩ e)

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out
