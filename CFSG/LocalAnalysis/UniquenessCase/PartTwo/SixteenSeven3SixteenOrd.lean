module

public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatAlt
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

theorem s16c167_two_mul_card_isAlt {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (h : UC22.IsAlt X n) : 2 * Nat.card X = Nat.factorial n := by
  obtain ⟨e⟩ := h
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_congr e.toEquiv]
  have h2 : 2 * Nat.card (alternatingGroup (Fin n)) = Nat.card (Equiv.Perm (Fin n)) :=
    two_mul_nat_card_alternatingGroup
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
    Fintype.card_fin] at h2
  exact h2

theorem s16c167_card_isAlt_six {X : Type} [Group X] (h : UC22.IsAlt X 6) :
    Nat.card X = 360 := by
  have h2 := s16c167_two_mul_card_isAlt (n := 6) (by norm_num) h
  rw [show Nat.factorial 6 = 720 by decide] at h2
  omega

theorem s16c167_card_isAlt_seven {X : Type} [Group X] (h : UC22.IsAlt X 7) :
    Nat.card X = 2520 := by
  have h2 := s16c167_two_mul_card_isAlt (n := 7) (by norm_num) h
  rw [show Nat.factorial 7 = 5040 by decide] at h2
  omega

theorem s16c167_card_isLn_four {X : Type} [Group X] (h : IsLn X 4 1) :
    Nat.card X = 20160 := by
  have hc := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two h
  rw [hc]
  decide

theorem s16c167_card_isOmegaMinus_six {X : Type} [Group X] (h : IsOmegaMinus X 6 1) :
    Nat.card X = 25920 := by
  obtain ⟨-, K, _, _, b, c, hK, hirr, ⟨e⟩⟩ := h
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hv : ∃ v, (quadMinus (6 / 2) K b c) v ≠ 0 := by
    refine ⟨fun i => if i = Sum.inr (Sum.inr 0) then 1 else 0, ?_⟩
    rw [coe_quadMinus]
    simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega (coe_quadMinus (6 / 2) K b c) hv,
    show (6 / 2 : ℕ) = 3 from rfl,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_three hirr, hK]
  decide

theorem s16c167_card_isElemAbelianOfRank {X : Type} [Group X] {p r : ℕ} [NeZero p]
    (h : IsElemAbelianOfRank p r X) : Nat.card X = p ^ r := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem s16c167_card_le_of_selfCentralizing {H : Type} [Group H] [Finite H] {F : Subgroup H}
    [F.Normal] (hF : centralizer (F : Set H) ≤ F) :
    Nat.card H ≤ Nat.card F * Nat.card (MulAut F) := by
  classical
  let φ : H →* MulAut F := MulAut.conjNormal
  have hker : φ.ker ≤ F := by
    intro x hx
    apply hF
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have h2 : x * f * x⁻¹ = f := by
      have h := congrArg (fun e : MulAut ↥F => ((e ⟨f, hf⟩ : ↥F) : H)) hx
      simpa only [φ, MulAut.one_apply, MulAut.conjNormal_apply, Subtype.coe_mk] using h
    calc f * x = x * f * x⁻¹ * x := by rw [h2]
      _ = x * f := by group
  haveI : Finite (MulAut F) := MulEquiv.finite_left
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card H := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  have h2 : Nat.card φ.ker ≤ Nat.card F := Subgroup.card_le_of_le hker
  have h3 : Nat.card φ.range ≤ Nat.card (MulAut F) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

theorem s16c167_card_mulAut_E9 {X : Type} [Group X] (h : IsElemAbelianOfRank 3 2 X) :
    Nat.card (MulAut X) = 48 := by
  obtain ⟨e⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    Nat.card_congr (CFSG.Sporadic.RuSchreier.ruMulAutEquivGL (p := 3) 2).toEquiv]
  exact CFSG.RankThree.Asc83Table.card_GL23

theorem s16c167_card_le_of_isElemAbelianOfRank_three_two {H : Type} [Group H] [Finite H]
    {F : Subgroup H} [F.Normal] (hF : centralizer (F : Set H) ≤ F)
    (hE : IsElemAbelianOfRank 3 2 ↥F) : Nat.card H ≤ 432 := by
  have h1 := s16c167_card_le_of_selfCentralizing hF
  rw [s16c167_card_mulAut_E9 hE, s16c167_card_isElemAbelianOfRank hE] at h1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
