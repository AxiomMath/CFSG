module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s15Simple_qs_of_simple_perfect {X : Type} [Group X] [IsSimpleGroup X]
    (hP : Group.IsPerfect X) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      haveI := hP
      exact Group.IsPerfect.not_isMulCommutative X
        (IsMulCommutative.of_comm fun x y => by
          have hy : y ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top y
          exact Subgroup.mem_center_iff.mp hy x)
  refine ⟨⟨hP.commutator_eq_top, ?_⟩, hZ⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

private theorem s15Simple_ln {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n)
    (h : IsLn X n 1) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := s16c167_cfg2_simple_ln h
  obtain ⟨-, K, instK, instFin, -, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI : Field K := instK
  letI : Finite K := instFin
  haveI : Group.IsPerfect (StatedSL n K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hn K
  haveI : Group.IsPerfect (StatedProj (StatedSL n K)) := inferInstance
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem s15Simple_sp {X : Type} [Group X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsSpn X n 1) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨-, K, instK, instFin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hm : 3 ≤ n / 2 := by omega
  haveI : IsSimpleGroup (StatedProj (StatedSp (n / 2) K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K (n / 2) (by omega)
      (Or.inr (Or.inr ⟨hK2, hm⟩))
  have hscal : (StatedScalars (Fin (n / 2) ⊕ Fin (n / 2)) K).subgroupOf
      (StatedSp (n / 2) K) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  let eP : StatedProj (StatedSp (n / 2) K) ≃* StatedSp (n / 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedSp (n / 2) K) := eP.symm.isSimpleGroup
  haveI : Group.IsPerfect (StatedSp (n / 2) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (n / 2) K
      (Or.inr (Or.inr ⟨hK2, hm⟩))
  haveI : IsSimpleGroup X := e.isSimpleGroup
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem s15Simple_omegaPlus {X : Type} [Group X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsOmegaPlus X n 1) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨-, K, instK, instFin, -, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  have hm : 3 ≤ n / 2 := by omega
  haveI : Group.IsPerfect (StatedOmega (StatedQuadPlus (n / 2) K)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) hm
  haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) := inferInstance
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := K) hm
  haveI : IsSimpleGroup X := e.isSimpleGroup
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem s15Simple_omegaMinus_six {X : Type} [Group X] (h : IsOmegaMinus X 6 1) :
    CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  haveI : IsSimpleGroup X := s16c1_isSimpleGroup_of_isOmegaMinus_six h
  obtain ⟨-, K, instK, instFin, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hK2])
  haveI : Group.IsPerfect (StatedOmega (StatedQuadMinus 3 K b c)) :=
    Group.isPerfect_def.mpr
      (CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
        (K := K) (n := 3) (Or.inr rfl) hirr).2.1
  haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus 3 K b c))) := inferInstance
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem s15Simple_omegaMinus_ge_eight {X : Type} [Group X] {n : ℕ} (hn : 8 ≤ n)
    (h : IsOmegaMinus X n 1) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨-, K, instK, instFin, b, c, -, hirr, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  have hm : 4 ≤ n / 2 := by omega
  haveI : Group.IsPerfect (StatedOmega (StatedQuadMinus (n / 2) K b c)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus (K := K) hm hirr
  haveI : Group.IsPerfect (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
    inferInstance
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (K := K) hm hirr
  haveI : IsSimpleGroup X := e.isSimpleGroup
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

private theorem s15Simple_omegaMinus {X : Type} [Group X] {n : ℕ} (hn : 6 ≤ n)
    (h : IsOmegaMinus X n 1) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨k, hk⟩ := h.1
  rcases Nat.lt_or_ge n 8 with hn8 | hn8
  · have hn6 : n = 6 := by omega
    subst hn6
    exact s15Simple_omegaMinus_six h
  · exact s15Simple_omegaMinus_ge_eight hn8 h

private theorem s15Simple_alt {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (h : UC22.IsAlt X n) : CFSG.Open.IsQuasisimple X ∧ Subgroup.center X = ⊥ := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)
  haveI : Group.IsPerfect (alternatingGroup (Fin n)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simpa using hn))
  haveI : IsSimpleGroup X := e.isSimpleGroup
  exact s15Simple_qs_of_simple_perfect
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)

theorem rSimple153_holds : RSimple153 := by
  intro V _ X _ _ K Z h
  rcases h with ⟨n, hn, hL, -⟩ | ⟨n, hn, hS, -⟩ | ⟨n, hn, hO, -⟩ | ⟨n, hn, hO, -⟩ |
    ⟨n, hn, hA, -⟩
  · exact s15Simple_ln hn hL
  · exact s15Simple_sp hn hS
  · exact s15Simple_omegaPlus hn hO
  · exact s15Simple_omegaMinus hn hO
  · exact s15Simple_alt hn hA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
