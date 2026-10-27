module

public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompAdapter
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExclusionUnitary
public import CFSG.RankThree.PartOne.KF.ClsSUUpper

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.G11.Harris

theorem not_isSimpleGroup_of_index_four {Y : Type} [Group Y] (hY : Nat.card Y = 72)
    (hS : IsSimpleGroup Y) (H : Subgroup Y) (hH : H.index = 4) : False := by
  have hcore := hS.eq_bot_or_eq_top_of_normal H.normalCore
  have hle : H.normalCore.index ≤ H.index.factorial := Subgroup.index_normalCore_le_factorial_index H
  rw [hH] at hle
  rcases hcore with h | h
  · rw [h, Subgroup.index_bot, hY] at hle
    norm_num [Nat.factorial] at hle
  · have htop : H = ⊤ := top_le_iff.mp (by rw [← h]; exact H.normalCore_le)
    rw [htop, Subgroup.index_top] at hH
    norm_num at hH

theorem not_isSimpleGroup_of_card_72 {Y : Type} [Group Y] (hY : Nat.card Y = 72) :
    ¬ IsSimpleGroup Y := by
  intro hS
  have : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 Y))
  have hn : Nat.card (Sylow 3 Y) = (Subgroup.normalizer (P : Set Y)).index :=
    Sylow.card_eq_index_normalizer P
  have hmod : Nat.card (Sylow 3 Y) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 Y
  have hdvd : (Subgroup.normalizer (P : Set Y)).index ∣ 72 := by
    rw [← hY]; exact Subgroup.index_dvd_card _
  have hcases : (Subgroup.normalizer (P : Set Y)).index = 1 ∨
      (Subgroup.normalizer (P : Set Y)).index = 4 := by
    have hmem : (Subgroup.normalizer (P : Set Y)).index ∈ Nat.divisors 72 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 72 = {1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72} from by decide] at hmem
    rw [hn] at hmod
    unfold Nat.ModEq at hmod
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  rcases hcases with h1 | h4
  ·
    have hnorm : Subgroup.normalizer (P : Set Y) = ⊤ := Subgroup.index_eq_one.mp h1
    have : (P : Subgroup Y).Normal := Subgroup.normalizer_eq_top_iff.mp hnorm
    have hfac : (72 : ℕ).factorization 3 = 2 := by
      rw [Nat.factorization_def _ Nat.prime_three]
      have h72 : (72 : ℕ) = 3 ^ 2 * 8 := by norm_num
      rw [h72, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    have hP9 : Nat.card (P : Subgroup Y) = 9 := by
      rw [Sylow.card_eq_multiplicity, hY, hfac]; norm_num
    rcases hS.eq_bot_or_eq_top_of_normal (P : Subgroup Y) with hb | ht
    · rw [hb, Subgroup.card_bot] at hP9
      norm_num at hP9
    · rw [ht, Subgroup.card_top, hY] at hP9
      norm_num at hP9
  · exact not_isSimpleGroup_of_index_four hY hS _ h4

theorem statedClassicalModel_quotient_of_statedSU {X : Type} [Group X] {e : ℕ} (he : 2 ≤ e)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ e) ^ 2)
    (hX : Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ e) K))) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 e := by
  obtain ⟨e0⟩ := hX
  have hnq : (3, 2 ^ e) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ e = 2 := congrArg Prod.snd h
    have h4 : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
    norm_num at h4
    omega
  have hiso := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := e) (n := 3) hK (by norm_num) hnq
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSU 3 2 e := by
    show Nat.Prime 2 ∧ 1 ≤ e ∧ 3 ≤ 3 ∧ (3, 2 ^ e) ≠ (3, 2)
    exact ⟨Nat.prime_two, by omega, le_refl 3, hnq⟩
  refine ⟨hadm, K, inferInstance, inferInstance, hK, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e0
    (CFSG.LieType.Universal.Unitary.map_center_mulEquiv e0)).trans
    (QuotientGroup.quotientMulEquivOfEq hiso.2)

theorem card_statedSU_three_two_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) = 216 := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩
  have : CharP K 2 := hUF.charP
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hUF (n := 3) (by norm_num)
  have hprod : (∏ i ∈ Finset.Icc 2 3, (((2 ^ 1 : ℕ) : ℤ) ^ i - (-1) ^ i)) = 27 := by
    decide
  have h216 : (Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ 1) K) : ℤ) = 216 := by
    rw [hc, hprod]
    norm_num
  exact_mod_cast h216

@[expose] def CoverSU3Quot (Y : Type) [Group Y] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSU 3 2 f) ∨
    Nat.card Y = 72

theorem famCoverSU3Two_false :
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (Γ A L : Subgroup (GLV V)) (m : ℕ),
      G93Hyp Γ A L L m → CoverSU3Quot (↥L ⧸ Subgroup.center ↥L) → False := by
  intro V _ _ _ Γ A L m hG hP
  rcases hP with ⟨f, hf, hU⟩ | hcard
  · exact CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.false_of_unitaryEven
      hf hG hU
  · exact not_isSimpleGroup_of_card_72 hcard hG.L_comp.2.2.2

theorem oneCompFor_famCoverSU3Two :
    OneCompFor FamCoverSU3Two := by
  refine oneCompFor_of_false (P := CoverSU3Quot) famCoverSU3Two_false ?_
  intro X _ hX
  obtain ⟨hZ, e, he1, _, hiso⟩ := hX
  obtain ⟨K, _, _, hK, hX'⟩ := hiso
  rcases Nat.lt_or_ge e 2 with hlt | hge
  · obtain rfl : e = 1 := by omega
    right
    have hX216 : Nat.card X = 216 := by
      obtain ⟨e0⟩ := hX'
      rw [Nat.card_congr e0.toEquiv]
      exact card_statedSU_three_two_of_card_four hK
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
    rw [hZ, hX216] at hq
    omega
  · left
    exact ⟨e, hge, statedClassicalModel_quotient_of_statedSU hge hK hX'⟩

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
