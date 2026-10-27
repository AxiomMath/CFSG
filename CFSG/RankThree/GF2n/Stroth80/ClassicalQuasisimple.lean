module

public import CFSG.RankThree.GF2n.Stroth80.Sec44
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidMinusFacts
public import CFSG.Quasithin.Background.P3OrthoOm4

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Assembly.LowTwoRank

private theorem nonabelian_of_commutator_eq_top {G : Type} [Group G] [Nontrivial G]
    (h : commutator G = ⊤) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : Group.IsPerfect G := Group.isPerfect_def.mpr h
  haveI : IsMulCommutative G := ⟨⟨fun a b => hcon a b⟩⟩
  exact (Group.IsPerfect.not_isMulCommutative G) inferInstance

theorem statedSL_quasisimple_of_card (m : ℕ) (K : Type) [Field K] [Finite K] (hm : 2 ≤ m)
    (h4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple ↥(StatedSL m K) :=
  CFSG.IsQuasisimple.of_mulEquiv (specialLinearGroupEquivStatedSL m K).symm
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple m K hm
      (Or.inr (by omega)) (Or.inr (by omega)))

theorem statedSp_quasisimple_of_card (m : ℕ) (K : Type) [Field K] (hm : 1 ≤ m)
    (h4 : 4 ≤ Nat.card K) : CFSG.IsQuasisimple ↥(StatedSp m K) :=
  CFSG.LieType.Universal.Symplectic.isQuasisimple m K hm (Or.inl (Or.inr h4))

theorem statedOmega_plus_quasisimple_of_three_le (K : Type) [Field K] (m : ℕ) (hm : 3 ≤ m) :
    CFSG.IsQuasisimple ↥(StatedOmega (StatedQuadPlus m K)) :=
  CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadPlus hm

open CFSG.ComponentClassification.RankTwoClassical.ORigid in
theorem statedOmega_minus_quasisimple_of_two_le (K : Type) [Field K] [Finite K] [CharP K 2]
    {m : ℕ} {b c : K} (hm : 2 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.IsQuasisimple ↥(StatedOmega (StatedQuadMinus m K b c)) := by
  haveI : IsSimpleGroup ↥(StatedOmega (StatedQuadMinus m K b c)) :=
    isSimpleGroup_statedOmega_quadMinus_of_two_le hm hirr
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_of_commutator_eq_top (commutator_statedOmega_quadMinus_eq_top hm hirr))).1

theorem statedOmega_plus_four_nonempty_equiv (K : Type) [Field K] [Finite K] [CharP K 2]
    (h4 : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 2 K)) ≃* ↥(StatedSL 2 K) × ↥(StatedSL 2 K)) := by
  obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card K h4
  exact ⟨e.trans (MulEquiv.prodCongr (specialLinearGroupEquivStatedSL 2 K)
    (specialLinearGroupEquivStatedSL 2 K))⟩

theorem classicalQuasisimpleStatement_holds : ClassicalQuasisimpleStatement := by
  intro K _ _ _ h4
  exact ⟨fun m hm => statedSL_quasisimple_of_card m K hm h4,
    fun m hm => statedSp_quasisimple_of_card m K hm h4,
    fun m hm => statedOmega_plus_quasisimple_of_three_le K m hm,
    fun m b c hm hirr => statedOmega_minus_quasisimple_of_two_le K hm hirr,
    statedOmega_plus_four_nonempty_equiv K h4⟩

end CFSG.RankThree.GF2n.Stroth80
