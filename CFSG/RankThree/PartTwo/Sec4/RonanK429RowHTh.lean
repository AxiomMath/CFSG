module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabThShapeZ
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSporThCent

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

open CFSG.Sporadic.Th (J thEquivJ)

open CFSG.HardMathSupport.Dickson.I271 (thS thZ thU th_census thEps th_letters_spec
  leaf_closure_of_six)

open CFSG.GH74.QTGen4.Recog.G23 (SatisfiesG23Words)


section Certs


theorem good429_th_S : Good429 (Subgroup.centralizer ({thS} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨hrel, hcomm, hne⟩ := th_letters_spec
  have hε : SatisfiesG23Words thEps := fun r hr =>
    (Census.CoverCenterThreeRest.lift_mk_eq_evalW _ r).trans (hrel r hr)
  obtain ⟨-, hsimp, -, hcard⟩ := leaf_closure_of_six thEps hε hne
  haveI := hsimp
  have hEC : Subgroup.closure (Set.range thEps) ≤ Subgroup.centralizer ({thS} : Set ↥J) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm i).symm
  have hC : Nat.card ↥(Subgroup.centralizer ({thS} : Set ↥J)) ≤ 63685439 :=
    CFSG.HardMathSupport.Dickson.Sec6.th3_facts.2.2.2.2.2
  refine good429_of_simple_small_index (m := 14) (B := 162) hEC (by norm_num) ?_
    (by rw [hcard]; decide) (by rw [hcard]; norm_num) (by rw [hcard]; decide)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hEC
  rw [hcard] at hk ⊢
  rw [hk] at hC
  have hk15 : k < 15 := by omega
  rw [hk]
  nlinarith

theorem good429_th_ZU :
    Good429 (Subgroup.centralizer ({thZ} : Set ↥J)) ∧
      Good429 (Subgroup.centralizer ({thU} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  refine ⟨good429_of_card_dvd (M := 472392) (B := 78) ?_ (by norm_num) (by norm_num) (by decide),
    good429_of_card (B := 57) RonanK432.th_card_centralizer_U (by norm_num) (by decide)⟩
  exact CFSG.HardMathSupport.Dickson.I271.card_centralizer_zJ_dvd

theorem th_reps_pow_three : thS ^ 3 = 1 ∧ thZ ^ 3 = 1 ∧ thU ^ 3 = 1 := by
  obtain ⟨hs, hz, hu⟩ := CFSG.HardMathSupport.Dickson.I271.th_orderOf
  exact ⟨by rw [← hs]; exact pow_orderOf_eq_one _, by rw [← hz]; exact pow_orderOf_eq_one _,
    by rw [← hu]; exact pow_orderOf_eq_one _⟩

theorem good429_th (x : ↥J) (hx : orderOf x = 3) :
    Good429 (Subgroup.centralizer ({x} : Set ↥J)) := by
  haveI : Finite ↥J := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.finite_J
  obtain ⟨k, c, hc, e, he, rfl⟩ := th_census x hx
  obtain ⟨hs3, hz3, hu3⟩ := th_reps_pow_three
  have key : ∀ y : ↥J, y ^ 3 = 1 → Good429 (Subgroup.centralizer ({y} : Set ↥J)) →
      Good429 (Subgroup.centralizer ({k * y ^ e * k⁻¹} : Set ↥J)) := fun y hy h => by
    refine Good429.of_isConj (isConj_iff.mpr ⟨k, rfl⟩) ?_
    rwa [centralizer_pow_of_pow_three hy he]
  rcases hc with rfl | rfl | rfl
  · exact key _ hs3 good429_th_S
  · exact key _ hz3 good429_th_ZU.1
  · exact key _ hu3 good429_th_ZU.2


theorem noCfgS429_th :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .Th) → NoCfgS429 S := by
  intro S _ _ _ hna ⟨e⟩
  have hout : ¬ 3 ∣ Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) := by
    rw [show Nat.card (Outer (Blueprint.NativeSporadic.Carrier .Th)) = 1 from
      RankThree.PartOne.SPOR.card_outer_Th_native]
    norm_num
  have hnat : ∀ x : Blueprint.NativeSporadic.Th, orderOf x = 3 →
      Good429 (Subgroup.centralizer ({x} : Set Blueprint.NativeSporadic.Th)) :=
    @forall_good429_of_mulEquiv Blueprint.NativeSporadic.Th ↥J Units.instGroup _ thEquivJ
      good429_th
  exact noCfgS429_of_model (G' := Blueprint.NativeSporadic.Th) e
    (center_eq_bot_of_simple_nonab hna) (not_three_dvd_outer_of_mulEquiv e hout) hnat

theorem rowSOf429_th :
    RowSOf429 (Spor .Th) :=
  rowSOf429_spor CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv noCfgS429_th

end Certs

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
