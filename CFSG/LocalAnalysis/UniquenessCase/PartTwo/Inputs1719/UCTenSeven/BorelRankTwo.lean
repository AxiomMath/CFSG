module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.Defs
public import CFSG.LieType.SteinbergBROddSylowNormalizers
public import CFSG.Adapters.LieModelSimple
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem not_eleven_dvd_two_pow_sub_one_of_odd {s : ℕ} (hs : Odd s) : ¬ 11 ∣ 2 ^ s - 1 := by
  intro hd
  have h2pow : (2 : ZMod 11) ^ s = 1 :=
    (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff s).mp hd
  have hord11 : orderOf (2 : ZMod 11) = 10 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 10)]
    refine ⟨by decide, ?_⟩
    intro k hk _
    interval_cases k <;> decide
  have h10 : 10 ∣ s := by
    rw [← hord11]
    exact orderOf_dvd_iff_pow_eq_one.mpr h2pow
  obtain ⟨k, rfl⟩ := hs
  omega

theorem kLieBorelAutPrimeRank2_holds : KLieBorelAutPrimeRank2 := by
  intro X _instGroup _instFinite t m hadm hLie hrank htD htT U hU s r hs hr hr7 hrdvd α hαr hαU
  have halpha : α = 1 ∨ (orderOf α = r ∧ Odd (orderOf α)) := by
    have hdvd : orderOf α ∣ r := orderOf_dvd_of_pow_eq_one hαr
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr1
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · refine Or.inr ⟨hr1, ?_⟩
      rw [hr1]
      exact hr.odd_of_ne_two (by omega)
  have hcases : (t = .PSL ∧ m = 3) ∨ (t = .PSU ∧ (m = 4 ∨ m = 5)) := by
    cases t <;>
      simp [CFSG.Open.StatedLieAdmissible, PartTwo.S17.CS17LieRank] at hadm hrank htD htT ⊢ <;>
      omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, hm45⟩
  ·
    rcases halpha with h1 | ⟨hord, hodd⟩
    · exact h1
    · have hSCM : CFSG.Open.StatedClassicalModel X .PSL 3 2 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
      have hsimple : IsSimpleGroup X :=
        CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSCM
      have hcard : Nat.card X = 168 :=
        CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two hSCM
      have hnab : ∃ a b : X, a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        have : IsMulCommutative X := ⟨⟨hcon⟩⟩
        have hp : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).1 hsimple
        rw [hcard] at hp
        norm_num at hp
      obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
          hLie
      letI : Field K := hKf
      have : Finite K := hKfin
      have hcase : (∃ n : ℕ, (n = 6 ∨ n = 7 ∨ n = 8) ∧
            Nonempty (X ≃* alternatingGroup (Fin n))) ∨
          ∃ (n : ℕ) (k : Type) (_ : Field k) (_ : Finite k), 3 ≤ n ∧ Nat.card k = 2 ∧
            Nonempty (X ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n k) :=
        Or.inr ⟨3, K, hKf, hKfin, by norm_num, by simpa using hKcard, ⟨e⟩⟩
      have hidx : ¬ 2 ∣ U.index := by
        rw [← Subgroup.relIndex_top_right]
        exact hU.2.2
      have hαU' : (((hU.2.1.toSylow hidx : Sylow 2 X) : Subgroup X)).map α.toMonoidHom =
          ((hU.2.1.toSylow hidx : Sylow 2 X) : Subgroup X) := by
        rw [IsPGroup.toSylow_coe hU.2.1 hidx]
        exact hαU
      exact (CFSG.LieType.small_alternating_and_binary_linear_odd_Sylow_normalizers_are_trivial
        X hsimple hnab (hU.2.1.toSylow hidx) α hodd hαU' hcase).2.2
  ·
    rcases halpha with h1 | ⟨hord, hodd⟩
    · exact h1
    · have hSCM : CFSG.Open.StatedClassicalModel X .PSU m 2 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel hLie (by decide)
      have hSCM' : CFSG.Open.StatedClassicalModel X .PSU m 2 1 := hSCM
      obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSCM'
      letI : Field K := hKf
      have : Finite K := hKfin
      have hm1 : 1 ≤ m := by rcases hm45 with rfl | rfl <;> norm_num
      have hn3 : 3 ≤ m := by rcases hm45 with rfl | rfl <;> norm_num
      have hcardX : Nat.card X = 25920 ∨ Nat.card X = 13685760 := by
        rcases hm45 with rfl | rfl
        · exact Or.inl (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hSCM)
        · exact Or.inr (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two hSCM)
      have hsimple : IsSimpleGroup X :=
        CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hSCM
      have hnab : ∃ a b : X, a * b ≠ b * a := by
        by_contra hcon
        push Not at hcon
        have : IsMulCommutative X := ⟨⟨hcon⟩⟩
        have hp : (Nat.card X).Prime := (Group.is_simple_iff_prime_card).1 hsimple
        rcases hcardX with hc | hc <;> rw [hc] at hp <;> norm_num at hp
      have : IsSimpleGroup X := hsimple
      have hcenter : Subgroup.center X = ⊥ :=
        CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab
      have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) = 2 := by
        have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
          ⟨Nat.prime_two, le_rfl, by rw [hKcard]; norm_num⟩
        have hq : ¬(m = 3 ∧ 2 ^ 1 = 2) := by rcases hm45 with rfl | rfl <;> norm_num
        obtain ⟨-, -, -, -, houtU, -⟩ :=
          CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_full_diagonal_outer_order
            hU hn3 hq
        rw [CFSG.LieType.SteinbergBR.OddSylow.card_outer_congr
          (e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU hm1).symm), houtU]
        rcases hm45 with rfl | rfl <;> norm_num
      have hcardAut : Nat.card (MulAut X) = 51840 ∨ Nat.card (MulAut X) = 27371520 := by
        rcases hcardX with hc | hc
        · refine Or.inl ?_
          calc Nat.card (MulAut X) = Nat.card X * Nat.card (Outer X) :=
                CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hcenter
            _ = 25920 * 2 := by rw [hc, hout]
            _ = 51840 := by norm_num
        · refine Or.inr ?_
          calc Nat.card (MulAut X) = Nat.card X * Nat.card (Outer X) :=
                CFSG.RankThree.PartOne.card_mulAut_eq_mul_card_outer hcenter
            _ = 13685760 * 2 := by rw [hc, hout]
            _ = 27371520 := by norm_num
      have hrdvdAut : r ∣ Nat.card (MulAut X) := by
        have h := orderOf_dvd_natCard α
        rwa [hord] at h
      have h11 : ¬ 11 ∣ 2 ^ s - 1 := not_eleven_dvd_two_pow_sub_one_of_odd hs
      rcases hcardAut with hca | hca
      · rw [hca, show (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 by norm_num] at hrdvdAut
        rcases hr.dvd_mul.mp hrdvdAut with h | h
        · rcases hr.dvd_mul.mp h with h | h
          · have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h
            rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
            · exact absurd h1 hr.ne_one
            · rw [h1] at hr7
              omega
          · have h3 : r ∣ 3 := hr.dvd_of_dvd_pow h
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h1
            · exact absurd h1 hr.ne_one
            · rw [h1] at hr7
              omega
        · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | h1
          · exact absurd h1 hr.ne_one
          · rw [h1] at hr7
            omega
      · rw [hca, show (27371520 : ℕ) = 2 ^ 11 * 3 ^ 5 * 5 * 11 by norm_num] at hrdvdAut
        rcases hr.dvd_mul.mp hrdvdAut with h | h
        · rcases hr.dvd_mul.mp h with h | h
          · rcases hr.dvd_mul.mp h with h | h
            · have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h
              rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
              · exact absurd h1 hr.ne_one
              · rw [h1] at hr7
                omega
            · have h3 : r ∣ 3 := hr.dvd_of_dvd_pow h
              rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h1
              · exact absurd h1 hr.ne_one
              · rw [h1] at hr7
                omega
          · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | h1
            · exact absurd h1 hr.ne_one
            · rw [h1] at hr7
              omega
        · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 11)).mp h with h1 | h1
          · exact absurd h1 hr.ne_one
          · rw [h1] at hrdvd
            exact absurd hrdvd h11

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
