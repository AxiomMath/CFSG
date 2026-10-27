module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Crit
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowHNTh
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section HN

open CFSG.Sporadic.HNSchreier


theorem good427_hn_s1 : Good427 (CJ (sJ 0)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcomm⟩ :=
    ctuc_hn_three_centralizers_exact
  haveI : IsSimpleGroup ↥L1J := isSimpleGroup_L1J
  have hLC : L1J ≤ CJ (sJ 0) := by
    rw [← hcomm]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [commutatorElement_def]
    exact (CJ (sJ 0)).mul_mem ((CJ (sJ 0)).mul_mem ((CJ (sJ 0)).mul_mem hx hy)
      ((CJ (sJ 0)).inv_mem hx)) ((CJ (sJ 0)).inv_mem hy)
  haveI : Group.IsPerfect ↥L1J := by
    haveI : Group.IsPerfect alt3 := ⟨commutator_alt3⟩
    exact Group.IsPerfect.map _
  haveI : Nontrivial ↥L1J := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_L1J_eq]
    norm_num
  exact good427_of_derived_le_simple hLC (exists_noncomm_of_perfect (K := L1J))
    (by rw [card_L1J_eq]; norm_num) hcomm.le

theorem good427_hn_s3 : Good427 (CJ (sJ 2)) :=
  good427_of_pConstrained
    (CFSG.HardMathSupport.Dickson.I271.pConstrainedShape_of_hn3bRChecks
      CFSG.HardMathSupport.Dickson.I271.hn3bR_checks)

theorem good427_hnJ (x : JH) (hx : orderOf x = 3) :
    Good427 (Subgroup.centralizer ({x} : Set JH)) := by
  rcases (hn_three_class x).1 hx with h | h
  · exact Good427.of_isConj h good427_hn_s1
  · exact Good427.of_isConj h good427_hn_s3

theorem noCfgS427_hn :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .HN) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .HN)) := by
    rw [RankThree.PartOne.SPOR.card_outer_HN]; norm_num
  have hnat : ∀ x : Blueprint.NativeSporadic.HN, orderOf x = 3 →
      Good427 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.HN)) :=
    @forall_good427_of_mulEquiv Blueprint.NativeSporadic.HN ↥JH Units.instGroup _ hnEquivJ
      good427_hnJ
  refine ⟨noCfgS427_of_model (G' := Blueprint.NativeSporadic.HN) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) hnat,
    noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.HN
  rw [CFSG.Sporadic.HN.card_HN]
  norm_num

end HN

section Th

open CFSG.Sporadic.Th (J thEquivJ)
open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census thEps th_letters_spec
  leaf_closure_of_six)
open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)


theorem good427_thS : Good427 (Subgroup.centralizer ({thS} : Set ↥J)) := by
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr =>
    (Census.CoverCenterThreeRest.lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨-, hsimp, hna, hcard⟩ := leaf_closure_of_six thEps hε hne
  haveI := hsimp
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2
  have hCm : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤
      14 * Nat.card ↥(Subgroup.closure (Set.range thEps)) := by
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEC
    rw [hcard] at hk ⊢
    rw [hk] at hC
    rw [hk]
    omega
  have hdvd : ¬ Nat.card ↥(Subgroup.closure (Set.range thEps)) ∣ Nat.factorial 14 := by
    rw [hcard]
    decide
  exact good427_of_le_simple hEC hna (by rw [hcard]; norm_num) fun K hKC _ =>
    perfect_le_of_simple_small_index hEC (m := 14) (by norm_num) hCm hdvd hKC

theorem good427_thZ : Good427 (Subgroup.centralizer ({thZ} : Set ↥J)) :=
  good427_of_card_dvd (M := 472392) CFSG.HardMathSupport.Dickson.I271.card_centralizer_zJ_dvd
    (by norm_num)

theorem good427_thU : Good427 (Subgroup.centralizer ({thU} : Set ↥J)) :=
  good427_of_pConstrained pConstrained_thU

theorem good427_thJ (x : ↥J) (hx : orderOf x = 3) :
    Good427 (Subgroup.centralizer ({x} : Set ↥J)) := by
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census x hx
  obtain ⟨hs3, hz3, hu3⟩ := RonanK429H.th_reps_pow_three
  have hg : Good427 (Subgroup.centralizer ({c} : Set ↥J)) ∧ c ^ 3 = 1 := by
    rcases hc with rfl | rfl | rfl
    · exact ⟨good427_thS, hs3⟩
    · exact ⟨good427_thZ, hz3⟩
    · exact ⟨good427_thU, hu3⟩
  have ha : Good427 (Subgroup.centralizer ({c ^ e} : Set ↥J)) := by
    rw [RonanK429H.centralizer_pow_of_pow_three hg.2 he]
    exact hg.1
  exact Good427.of_isConj (isConj_iff.mpr ⟨k, rfl⟩) ha

theorem noCfgS427_th :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Th) → NoCfgS427 S ∧ NoONS427 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
      RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  have hnat : ∀ x : Blueprint.NativeSporadic.Th, orderOf x = 3 →
      Good427 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.Th)) :=
    @forall_good427_of_mulEquiv Blueprint.NativeSporadic.Th ↥J Units.instGroup _ thEquivJ
      good427_thJ
  refine ⟨noCfgS427_of_model (G' := Blueprint.NativeSporadic.Th) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) hnat,
    noONS427_of_card ?_⟩
  rw [Nat.card_congr e.toEquiv]
  show ¬ (19 * 31 * 343) ∣ Nat.card Blueprint.NativeSporadic.Th
  rw [CFSG.RankThree.PartOne.CTP.card_Th]
  norm_num

end Th

section Rows



section HNRow


theorem rowOf427_hn
    : RowOf427 (Spor .HN) :=
  rowOf427_spor (s := .HN) CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv noCfgS427_hn

end HNRow

section ThRow


theorem rowOf427_th
    : RowOf427 (Spor .Th) :=
  rowOf427_spor (s := .Th) CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv noCfgS427_th

end ThRow

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
