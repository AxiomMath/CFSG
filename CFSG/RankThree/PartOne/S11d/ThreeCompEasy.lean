module

public import CFSG.RankThree.PartOne.TCX.RankInterface
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11c.Sec66TModelsTw
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.RankThree.PartOne.TCX.Interface

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG
open CFSG.Blueprint (LieModel SuzukiModel)
open CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix

theorem not_lieModel_POmegaOdd {T : Type} [Group T] {n f : ℕ} :
    ¬ LieModel T .POmegaOdd n 2 f := fun hM =>
  absurd rfl ((lieModel_classical_iff (by decide)).mp hM).1.2.2.2

theorem not_lieModel_twistedG2 {T : Type} [Group T] {n f : ℕ} :
    ¬ LieModel T .twistedG2 n 2 f := fun hM =>
  absurd (statedLieAdmissible_of_lieModel hM).2.2.2.1 (by norm_num)

theorem not_lieModel_Tits {T : Type} [Group T] {n p f₀ : ℕ} (hp : 2 ≤ p) (hf₀ : 1 ≤ f₀) :
    ¬ LieModel T .Tits n 2 (p * f₀) := fun hM => by
  have h := (statedLieAdmissible_of_lieModel hM).2.2.2.2
  have : p ≤ p * f₀ := Nat.le_mul_of_pos_right p hf₀
  omega

theorem pRank_le_one_of_lieModel_twistedB2 {T : Type} [Group T] [Finite T] {n f p : ℕ}
    (hM : LieModel T .twistedB2 n 2 f) (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.pRank p T ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.QuasithinUnique.Id2519.pRank_le_one_suzuki (lieModel_twistedB2_iff.mp hM).2 hp hp2

theorem threeCompT_POmegaOdd : ThreeCompT .POmegaOdd := by
  intro T _ _ p _ _ _ _ n f₀ _ hM
  exact (not_lieModel_POmegaOdd hM).elim

theorem fixedRankT_POmegaOdd : FixedRankT .POmegaOdd := by
  intro T _ _ p _ _ _ _ n f₀ _ hM
  exact (not_lieModel_POmegaOdd hM).elim

theorem threeCompT_twistedG2 : ThreeCompT .twistedG2 := by
  intro T _ _ p _ _ _ _ n f₀ _ hM
  exact (not_lieModel_twistedG2 hM).elim

theorem fixedRankT_twistedG2 : FixedRankT .twistedG2 := by
  intro T _ _ p _ _ _ _ n f₀ _ hM
  exact (not_lieModel_twistedG2 hM).elim

theorem threeCompT_Tits : ThreeCompT .Tits := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hM
  exact (not_lieModel_Tits (by omega) hf₀ hM).elim

theorem fixedRankT_Tits : FixedRankT .Tits := by
  intro T _ _ p hp hp5 _ _ n f₀ hf₀ hM
  exact (not_lieModel_Tits (by omega) hf₀ hM).elim

theorem threeCompT_Sz : ThreeCompT .twistedB2 := by
  intro T _ _ p hp hp5 _ h2 n f₀ _ hM
  have := pRank_le_one_of_lieModel_twistedB2 hM hp (by omega)
  omega

theorem fixedRankT_Sz : FixedRankT .twistedB2 := by
  intro T _ _ p hp hp5 _ h2 n f₀ _ hM
  have := pRank_le_one_of_lieModel_twistedB2 hM hp (by omega)
  omega

end CFSG.RankThree.PartOne.TCX
