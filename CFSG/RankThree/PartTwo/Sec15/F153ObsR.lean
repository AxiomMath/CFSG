module

public import CFSG.RankThree.PartTwo.Sec15.F153ObsG
public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProofTwin
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof
import CFSG.CGT.PushingUp.TwoLocals

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153Obs

open Subgroup

section ObsWR

@[expose] def TwinOKType {G : Type*} [Group G] (Y : Subgroup G) : Prop :=
  ¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
    CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 in
theorem theoremA881 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), TwinOKType Y →
      ∀ R : Subgroup G, R ≤ n155 A Y → A ≤ Subgroup.normalizer (R : Set G) →
        (Nat.card R).Coprime 3 → R ≤ Subgroup.normalizer (Y : Set G) := by
  intro G _ _ A c L hR Y hY hTwin R hRX hAR hR3
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.1
  have hYX : Y ≤ CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G))) :=
    le_oPrimeResidualOf_delta hY4 Subgroup.le_normalizer
  obtain ⟨hYA, hY3, hYdelta, hq⟩ := hY4
  have hXY : CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ≤ Subgroup.normalizer (Y : Set G) :=
    (CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_le_self 3 _).trans (delta_le _)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hYA.2
  have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.2.2
  have hAX : A ≤ Subgroup.normalizer (CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G))) : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_oPrimeResidualOf
      (CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta _)
  have hE := hR.toSec14Std.toSec13Data.mem_partTwoE
  have hF := hR.toSec14Std.toSec13Data.mem_partTwoF
  obtain ⟨hEab, hA27, -⟩ := hE
  have hA : ∀ a ∈ A, a ^ 3 = 1 := hEab.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (isMulCommutative_iff.mp hEab.1 ⟨a, ha⟩ ⟨b, hb⟩)
  have hmax : ∀ x : G, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set G) → x ∈ A := by
    intro x hx3 hxc
    have hx : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    have hcent : A ≤ Subgroup.centralizer ({x} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxc a ha)
    exact CFSG.RankThree.PartTwo.Sec15.mem_of_mem_partTwoF hF hx hcent
  have hgen : ∀ y ∈ Y, y ∈ ⨆ (Q : Subgroup G) (_ : Q ≤ Y ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      (Nat.card Q).Coprime 3), Q := by
    have hsup : delta A (lB A) Y ≤ ⨆ (Q : Subgroup G) (_ : Q ≤ Y ∧
        A ≤ Subgroup.normalizer (Q : Set G) ∧ (Nat.card Q).Coprime 3), Q := by
      apply sSup_le
      intro Q hQ
      have hQA : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ.1).2.1
      have hQc : (Nat.card Q).Coprime 3 := by
        have hπ := (mem_scriptQ_iff.mp hQ.1).1
        rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
        intro hdvd
        exact hπ ⟨3, Nat.prime_three⟩ hdvd rfl
      exact le_iSup_of_le Q (le_iSup_of_le ⟨hQ.2, hQA, hQc⟩ le_rfl)
    intro y hy
    exact ((le_of_eq hYdelta).trans hsup) hy
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNO : CFSG.Open.IsTwoLocal
      (Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G)) :=
    ⟨CFSG.Open.pCoreOf 2 Y, hO2, CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y, rfl⟩
  have hXN : CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ≤
        Subgroup.normalizer ((CFSG.Open.pCoreOf 2 Y : Subgroup G) : Set G) :=
    hXY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hX3 : CFSG.Open.pRank 3 (CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) ≤ 3 := by
    have h1 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hXN
    have h2 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) _ hNO
    have h4 : CFSG.Open.evenRank G = 3 :=
      hR.toSec14Std.toSec13Data.toPartTwoStanding.toTheoremFourHyp.evenRank_eq
    exact h1.trans (h2.trans h4.le)
  have h3 : ∀ E : Subgroup G, E ≤ CFSG.GH74.GLS.oPrimeResidualOf 3
      (delta A (lB A) (Subgroup.normalizer (Y : Set G))) →
      (∀ e ∈ E, e ^ 3 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) → Nat.card E ≤ 27 := by
    intro E hEX hE3 hEc
    have hab : CFSG.Open.IsElemAbelian 3 E :=
      ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (hEc a.1 a.2 b.1 b.2),
        fun x hx => hE3 x hx⟩
    have hp3 : IsPGroup 3 E := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro g
      exact ⟨1, Subtype.ext (by simpa using hE3 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp3
    have hkX : k ≤ CFSG.Open.pRank 3 (CFSG.GH74.GLS.oPrimeResidualOf 3
        (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEX hab hk
    calc Nat.card E = 3 ^ k := hk
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hkX.trans hX3)
      _ = 27 := by norm_num
  exact normalizes_of_coprime_invariant_inG _ Y A R hYX hXY hY3 hq hA hAc
    hA27 hAY hAX hmax hTwin hgen h3 hRX hR3 hAR

end ObsWR

section ObsWB

theorem not_dvd_three_card_center_of_alt5 {K : Type} [Group K]
    (e : K ≃* alternatingGroup (Fin 5)) :
    ¬ 3 ∣ Nat.card (Subgroup.center K) := by
  have hA5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hbot : Subgroup.center K = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hcen : e z ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 : e.symm g * z = z * e.symm g := Subgroup.mem_center_iff.mp hz (e.symm g)
      have h2 : e (e.symm g * z) = e (z * e.symm g) := by rw [h1]
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [hA5, Subgroup.mem_bot] at hcen
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hcen, map_one])
  rw [hbot, Subgroup.card_bot]
  norm_num

theorem coprime_card_three_of_isPi_two {G : Type} [Group G] {S : Subgroup G}
    (hS : CFSG.IsPiSubgroup (CFSG.RankThree.PartTwo.piOf 2) S) :
    (Nat.card S).Coprime 3 := by
  refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
  intro h3
  have hmem := hS (⟨3, Nat.prime_three⟩ : Nat.Primes) h3
  have h32 : (3 : ℕ) = 2 := hmem
  omega

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 in
theorem claim153ObsR_of
    (hThA : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A),
        (¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
          CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6))) →
        ∀ R : Subgroup G, R ≤ n155 A Y → A ≤ Subgroup.normalizer (R : Set G) →
          (Nat.card R).Coprime 3 → R ≤ Subgroup.normalizer (Y : Set G))
    (htypes : Claim153TwinTypes) (h149 : Sec16.Item149S14) (h152 : Item152R) : Claim153ObsR := by
  intro G _ _ A c L hR Y hY S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hYX, -, hX2⟩ := facts153 hR.toSec14Std (h149 G A c L hR.toSec14Std) hY
  by_cases hE : HasFaithfulE9 Y
  · exact claim153ObsE9_of hR.toSec14Std (h149 G A c L hR.toSec14Std) (h152 G A c L hR)
      Y hY hE S hS
  have hSX : S ≤ n155 A Y := hS.prop.1.2
  by_cases hNY : n155 A Y ≤ Subgroup.normalizer (Y : Set G)
  · exact hSX.trans hNY
  set X := CFSG.GH74.GLS.oPrimeResidualOf 3
    (delta A (lB A) (Subgroup.normalizer (Y : Set G))) with hX
  have hloc := CFSG.CGT.PushingUp.isPLocal_normalizer_of_isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X) hX2
  obtain ⟨M, hle, hM⟩ := CFSG.CGT.PushingUp.exists_isMaximalTwoLocal_ge hloc
  have hNXle : Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_oPrimeResidualOf
      (CFSG.RankThree.PartTwo.Sec14.le_normalizer_delta (Subgroup.normalizer (Y : Set G)))
  have hYA : Y ⊔ A ≤ Subgroup.normalizer (X : Set G) :=
    sup_le (hYX.trans Subgroup.le_normalizer) hAX
  have hMm : M ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) :=
    ⟨hM, fun x hx => hle (hNXle (hYA hx))⟩
  have hMY : ¬ M ≤ Subgroup.normalizer (Y : Set G) := fun hMY =>
    hNY ((hNXle.trans hle).trans hMY)
  have hdisj : ¬ 3 ∣ Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) ∨
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y)
        (alternatingGroup (Fin 6)) := by
    rcases htypes G A c L hR Y hY hE M hMm hMY with ⟨⟨e⟩⟩ | h6
    · exact Or.inl (not_dvd_three_card_center_of_alt5 e)
    · exact Or.inr h6
  have hAS : A ≤ Subgroup.normalizer (S : Set G) :=
    ((CFSG.RankThree.PartTwo.Sec14.mem_scriptQ_iff).mp hS.prop.1.1).2.1
  exact hThA G A c L hR Y hY.prop hdisj S hSX hAS (coprime_card_three_of_isPi_two hS.prop.2)

open CFSG.RankThree.PartTwo.Sec15 in
theorem step153PushTwinR_of_obs (hobs : Claim153ObsR) : Step153PushTwinR := by
  intro G _ _ A c L hR Y hY S hS _ _ hSY
  exact absurd (hobs G A c L hR Y hY S hS) hSY

end ObsWB

end CFSG.RankThree.PartTwo.Sec15.F153Obs
