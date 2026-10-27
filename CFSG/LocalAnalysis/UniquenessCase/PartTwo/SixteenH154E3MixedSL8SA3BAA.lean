module

public import CFSG.Adapters.StatedSLPerfect
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Models.PGLSimple
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_sl8_isPerfect_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Group.IsPerfect X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_sl8_isSimpleGroup_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : IsSimpleGroup X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hK2 : Nat.card K ≠ 2 := by omega
  have hK3 : Nat.card K ≠ 3 := by omega
  have hKeven : Fintype.card K % 2 = 0 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  have hchar : ringChar K = 2 :=
    (FiniteField.even_card_iff_char_two (F := K)).mpr hKeven
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hbot : (StatedScalars (Fin 2) K).subgroupOf (StatedSL 2 K) = ⊥ :=
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot
  let q : StatedProj (StatedSL 2 K) ≃* ↥(StatedSL 2 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedProj (StatedSL 2 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (d := 2) (by norm_num)
      (Or.inr hK2) (Or.inr hK3)
  haveI : IsSimpleGroup ↥(StatedSL 2 K) := q.symm.isSimpleGroup
  exact e.isSimpleGroup

theorem s16h_sl8_center_eq_bot_of_isSLn_two {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (h : IsSLn X 2 m) : Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := s16h_sl8_isSimpleGroup_of_isSLn_two hm h
  haveI : Group.IsPerfect X := s16h_sl8_isPerfect_of_isSLn_two hm h
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center X) with hbot | htop
  · exact hbot
  · exfalso
    have hcomm : ∀ a b : X, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center X := htop ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm
    haveI : IsMulCommutative X := ⟨⟨hcomm⟩⟩
    exact (Group.IsPerfect.not_isMulCommutative X) inferInstance

theorem s16h_sl8_closure_elemAbelian {A : Type*} [Group A] {k : Set A} {p : ℕ}
    (hpair : k.Pairwise Commute) (hexp : ∀ x ∈ k, x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure k) := by
  haveI : IsMulCommutative ↥(Subgroup.closure k) := Subgroup.isMulCommutative_closure hpair
  refine ⟨inferInstance, ?_⟩
  have hcomm : ∀ x ∈ Subgroup.closure k, ∀ y ∈ Subgroup.closure k, x * y = y * x :=
    fun x hx y hy =>
      congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x, hx⟩ : ↥(Subgroup.closure k)) ⟨y, hy⟩)
  intro x hx
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · exact fun y hy => hexp y hy
  · simp
  · intro y z hy hz ihy ihz
    rw [Commute.mul_pow (hcomm y hy z hz), ihy, ihz, one_mul]
  · intro y hy ihy
    rw [inv_pow, ihy, inv_one]

theorem s16h_sl8_inf_eq_bot_of_commute {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hB : Subgroup.center ↥B = ⊥) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hz : (⟨x, hx.2⟩ : ↥B) ∈ Subgroup.center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hcomm x hx.1 y y.2).symm
  rw [hB, Subgroup.mem_bot] at hz
  rw [Subgroup.mem_bot]
  simpa using congrArg Subtype.val hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
