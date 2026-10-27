module

public import CFSG.RankThree.PartTwo.Sec8.HeringU3nCover
public import CFSG.RankThree.PartTwo.Sec8.HeringU3nGlue3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
import CFSG.Open.StatedCenterThree

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG.RankThree.PartTwo.Sec8.HeringU3n CFSG.GH74.Uniqueness.Bender
open CFSG.RankThree.PartTwo.Sec8
open CFSG.Quasithin.Background.Harris.OrdinaryProofs
  (statedClassicalModel_quotient_of_statedSU)

theorem unitary_cover_data {X : Type} [Group X] [Finite X] {m : ℕ} (hm : Odd m) (hm2 : 2 ≤ m)
    (hX : IsUnitaryTwo X m) :
    Group.IsPerfect X ∧ Odd (Nat.card (Subgroup.center X)) ∧
      ∃ e, BenderType (X ⧸ Subgroup.center X) m 3 e := by
  rcases hX with ⟨⟨φ⟩⟩ | ⟨K, hK, hKfin, hKcard, ⟨φ⟩⟩
  ·
    have hst := CFSG.RankThree.PartTwo.Sec20.statedClassicalModel_of_mulEquiv_projSU3 hm2 φ
    obtain ⟨φ2⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hm2 hst
    have hB : BenderType X m 3 ((2 ^ m + 1) / Nat.gcd 3 (2 ^ m + 1)) :=
      .unitary m hm2 (φ2.trans (MulEquiv.subgroupCongr
        (CFSG.Models.benderPSU3Model_eq_psu3 m).symm))
    have hcen : Subgroup.center X = ⊥ := hB.center_eq_bot
    have hsimple : IsSimpleGroup X := hB.isSimple
    have hnc : ¬ IsMulCommutative X := fun hc => by
      have := Subgroup.center_eq_top_iff.mpr hc
      rw [hcen] at this
      exact bot_ne_top this
    refine ⟨TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc, ?_, ?_⟩
    · rw [hcen, Subgroup.card_bot]
      exact odd_one
    · refine ⟨_, hB.of_mulEquiv ?_⟩
      exact (QuotientGroup.quotientBot (G := X)).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcen.symm)
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2) (by
      simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hKcard)
    have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := by
      intro h
      have h2 : 2 ^ m = 2 := congrArg Prod.snd h
      have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      norm_num at h4
      omega
    have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (p := 2) (f := m)
      (n := 3) hKcard (by norm_num) hnq
    haveI : Group.IsPerfect (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K) := hq.1.1
    haveI : Group.IsPerfect X :=
      Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
    have hmod : 2 ^ m % 3 = 2 := by
      obtain ⟨k, rfl⟩ := hm
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hc3 : Nat.card (Subgroup.center (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) = 3 :=
      CFSG.Open.StatedCenterThree.card_center_statedSU_three hKcard (by omega)
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.centerCongr φ).toEquiv, hc3]
      exact (by decide : Odd 3)
    · have hst := statedClassicalModel_quotient_of_statedSU hm2 hKcard ⟨φ⟩
      obtain ⟨φ2⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hm2 hst
      exact ⟨_, .unitary m hm2 (φ2.trans (MulEquiv.subgroupCongr
        (CFSG.Models.benderPSU3Model_eq_psu3 m).symm))⟩

theorem u3nPure_holds : U3nPure := by
  intro n hn X _ _ hX s hs1 hs2
  have hm : Odd (3 * n) := Odd.mul (by decide) hn
  have hm2 : 2 ≤ 3 * n := by
    have := hn.pos
    omega
  obtain ⟨hperf, hodd, e, hB⟩ := unitary_cover_data hm hm2 hX
  haveI := hperf
  exact ⟨hodd, fun E hE hEc hsE => cover_root (le_refl _) hodd hB hs1 hs2 hE hEc hsE,
    fun F hF hFs hFn => cover_aut hodd hm hB hs1 hs2 hF hFs hFn⟩

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
