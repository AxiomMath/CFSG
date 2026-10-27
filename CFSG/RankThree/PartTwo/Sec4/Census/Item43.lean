module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open43
public import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
public import CFSG.RankThree.PartOne.Census3.OpenCases
import CFSG.RankThree.PartOne.Census3.Linear
import CFSG.RankThree.PartOne.Census3.UnitarySixEight
import CFSG.RankThree.PartTwo.Census.Classical.Bridges
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
import CFSG.LocalAnalysis.SectionRank.NativeKGroup
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne.Census3
open CFSG.Assembly.LowTwoRank TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)

theorem excludedIndex_A_of_five_le (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hr : 5 ≤ r) (hq : q.p ≠ 2 ∨ 2 ≤ q.exponent) : ExcludedIndex (.lie ⟨.A r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  by_cases hq2 : q.p = 2
  · have hf2 : 2 ≤ q.exponent := hq.resolve_left (not_not.mpr hq2)
    have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq2
    have hU : Nat.card (GaloisField q.p q.exponent)ˣ = 2 ^ q.exponent - 1 := by
      rw [Nat.card_units, hK, hq2]
    obtain ⟨s, hs, hs2, -, hsd⟩ :=
      CFSG.RankThree.PartTwo.Census.exists_prime_ne_five_dvd_two_pow_sub_one hf2
    exact excludedIndex_A_of_four_le r q hv hs hs2
      (CFSG.RankThree.PartTwo.Census.le_localRank_PSL_torus (m := 4) hs (by rw [hU]; exact hsd)
        (by omega) (by omega) (Or.inl (by omega)))
  · have hf1 := q.exponent_pos
    exact excludedIndex_A_of_four_le r q hv q.prime_p hq2 (le_trans (by omega)
      (CFSG.RankThree.PartTwo.Census.four_mul_le_localRank_PSL
        (K := GaloisField q.p q.exponent) (n := r + 1) hq2 hK (by omega)))

theorem excludedIndex_twistedA_of_five_le (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hr : 5 ≤ r)
    (hq : ¬ (r = 5 ∧ q.p = 2 ∧ q.exponent = 1)) : ExcludedIndex (.lie ⟨.twistedA r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hu := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField q.p q.exponent
    q.exponent_pos
  have hf1 := q.exponent_pos
  by_cases hq2 : q.p = 2
  · have : CharP (GaloisField q.p (2 * q.exponent)) 2 := CharP.congr q.p hq2
    rcases (show r = 5 ∨ 6 ≤ r by omega) with rfl | hr6
    · rcases (show q.exponent = 1 ∨ q.exponent = 3 ∨ (2 ≤ q.exponent ∧ q.exponent ≠ 3) by
        omega) with hf | hf | ⟨hf2, hf3⟩
      · exact absurd ⟨rfl, hq2, hf⟩ hq
      · refine excludedIndex_twistedA_of_four_le 5 q hv Nat.prime_three (by norm_num) ?_
        have hK : Nat.card (GaloisField q.p (2 * q.exponent)) = 64 := by
          rw [GaloisField.card _ _ (by omega), hq2, hf]
          norm_num
        have h8 : q.p ^ q.exponent = 8 := by
          rw [hq2, hf]
          norm_num
        rw [h8]
        exact localRankThreeU68 _ hK
      · obtain ⟨s, hs, hs5, hsd⟩ :=
          CFSG.RankThree.PartTwo.Census.exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
        refine excludedIndex_twistedA_of_four_le 5 q hv hs (by omega) ?_
        refine CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 3) hu hs
          (by rw [hq2]; exact hsd) (by norm_num) (Or.inr fun h6 => ?_)
        have hs6 := Nat.le_of_dvd (by norm_num) h6
        interval_cases s
        · exact absurd h6 (by norm_num)
        · exact absurd hs (by norm_num)
    · obtain ⟨s, hs, hs2, hsd⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
      exact excludedIndex_twistedA_of_four_le r q hv hs hs2
        (CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 3) hu hs
          (by rw [hq2]; exact hsd) (by omega) (Or.inl (by omega)))
  · refine excludedIndex_twistedA_of_four_le r q hv q.prime_p hq2 ?_
    rw [← CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hu (n := r + 1) (by omega)) q.prime_p]
    exact le_trans (by norm_num; omega)
      (CFSG.RankThree.PartTwo.Census.le_localRank_unitaryPSU hu hq2 (n := r + 1) (r := 2)
        (by norm_num) (by omega))

theorem exists_index_of_sectionFourHyp {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : SectionFourHyp S) : ∃ i : CFSGIndex, Nonempty (S ≃* i.Group) := by
  let e : (⊤ : Subgroup S) ⧸ (⊥ : Subgroup (⊤ : Subgroup S)) ≃* S :=
    QuotientGroup.quotientBot.trans Subgroup.topEquiv
  have : IsSimpleGroup ((⊤ : Subgroup S) ⧸ (⊥ : Subgroup (⊤ : Subgroup S))) := e.isSimpleGroup
  obtain ⟨i, ⟨f⟩⟩ := hS.kGroup ⊤ ⊥ this
  exact ⟨i, ⟨e.symm.trans f⟩⟩

theorem isoLThreePi_of_A2 {X : Type} [Group X] {q : PrimePower} (hv : (LieTypeIndex.A 2 q).Valid)
    (h3 : 3 ∣ q.card - 1) (e : X ≃* (CFSGIndex.lie ⟨.A 2 q, hv⟩).Group) :
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    IsoLThreePi X q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq : 2 ≤ q.card := by
    rw [PrimePower.card_def]
    exact (q.prime_p.two_le).trans (Nat.le_self_pow q.exponent_pos.ne' _)
  refine Or.inl ⟨?_, ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeAGroupEquivProjSL 2 q hv)⟩⟩
  rw [← PrimePower.card_def]
  omega

theorem isoLThreePi_of_twistedA2 {X : Type} [Group X] {q : PrimePower}
    (hv : (LieTypeIndex.twistedA 2 q).Valid) (h3 : 3 ∣ q.card + 1)
    (e : X ≃* (CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group) :
    haveI : Fact q.p.Prime := ⟨q.prime_p⟩
    IsoLThreePi X q.p q.exponent := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine Or.inr ⟨?_, ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 2 q hv)⟩⟩
  rw [← PrimePower.card_def]
  omega

theorem eq_three_of_card_eq_three {q : PrimePower} (h : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 :=
  (Nat.Prime.pow_eq_iff Nat.prime_three).mp (by rw [← PrimePower.card_def]; exact h)

theorem rank3II_4_3_of_open (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hSuz : TripleCoverSuzRankFour) (hU62 : TripleCoverU62RankFour) (hspin : SpinRankFour)
    (hexc : ExceptionalRankFour) (hFi22 : ExcludedIndex (.sporadic .Fi22))
    (hFi24 : ExcludedIndex (.sporadic .Fi24Prime)) : Item4_3 := by
  intro G _ _ hG hq h3
  have hS : SectionFourHyp (G ⧸ Subgroup.center G) := sectionFourHyp_quotient_center h41 hG hq
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hnonab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := hq.2.2
  obtain ⟨i, ⟨e⟩⟩ := exists_index_of_sectionFourHyp hS
  have htc : IsThreeCenterCover G i.Group := ⟨hq, h3, ⟨e⟩⟩
  have hex : ∀ {j : CFSGIndex}, ExcludedIndex j → (G ⧸ Subgroup.center G ≃* j.Group) → False :=
    fun hj e' => SectionFourHyp.false_of_four_le_twoLocalOddRank hS (hj _ this hnonab e')
  have hexG : 4 ≤ CFSG.twoLocalOddRank G → False :=
    SectionFourHyp.false_of_four_le_twoLocalOddRank hG
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc _ _))
  | alternating n hn =>
    rcases hmult.alternating n G hn htc with rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | sporadic s =>
    rcases hmult.sporadic s G htc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans b.symm⟩)))))
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans b.symm⟩))))))
    · have : IsSimpleGroup SporadicName.McL.Group := e.symm.isSimpleGroup
      obtain ⟨b⟩ := CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans b⟩)))))))
    · exact (hexG (hSuz G htc)).elim
    · obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans b.symm⟩)))))))
    · exact (hex hFi22 e).elim
    · exact (hex hFi24 e).elim
  | lie d =>
    obtain ⟨d, hv⟩ := d
    have hd := hmult.lie ⟨d, hv⟩ G htc
    cases d with
    | A r q =>
      obtain ⟨h3r, h3q⟩ := hd
      have hr1 : 1 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
      rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
      · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos, isoLThreePi_of_A2 hv h3q e⟩
      · refine (hex (excludedIndex_A_of_five_le r q hv hr5 ?_) e).elim
        by_contra hq
        push Not at hq
        have hc : q.card = 2 := by
          rw [PrimePower.card_def, hq.1, show q.exponent = 1 by have := q.exponent_pos; omega]
          norm_num
        rw [hc] at h3q
        omega
    | twistedA r q =>
      have hr2 : 2 ≤ r :=
        LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
      rcases hd with ⟨h3r, h3q⟩ | ⟨rfl, hq3⟩
      · rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
        · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos,
            isoLThreePi_of_twistedA2 hv h3q e⟩
        · by_cases h62 : r = 5 ∧ q.p = 2 ∧ q.exponent = 1
          · exact (hexG (hU62 q (h62.1 ▸ hv) h62.2.1 h62.2.2 G (by
              obtain ⟨rfl, -, -⟩ := h62
              exact htc))).elim
          · exact (hex (excludedIndex_twistedA_of_five_le r q hv hr5 h62) e).elim
      · obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hq3
        obtain ⟨p, f, hp, hf⟩ := q
        obtain rfl : p = 3 := hp3
        obtain rfl : f = 1 := hf1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 3 _ hv)⟩))))
    | B r q =>
      obtain ⟨rfl, hq3⟩ := hd
      obtain ⟨hp3, -⟩ := eq_three_of_card_eq_three hq3
      exact (hex (excludedIndex_of_four_le (hspin.typeB 3 q hv le_rfl (fun h => by omega)
        (fun h => by omega))) e).elim
    | G2 q =>
      obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hd
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
          (chevalleyExceptionalModel_G2_three q hv hp3 hf1)))))
    | E6 q => exact (hex (excludedIndex_of_four_le (hexc.e6 q hv)) e).elim
    | twistedE6 q => exact (hex (excludedIndex_of_four_le (hexc.twistedE6 q hv)) e).elim
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | E7 q => exact hd.elim
    | E8 q => exact hd.elim
    | F4 q => exact hd.elim
    | trialityD4 q => exact hd.elim
    | suzuki m => exact hd.elim
    | reeG2 m => exact hd.elim
    | reeF4 m => exact hd.elim
    | tits => exact hd.elim

end CFSG.RankThree.PartTwo.Sec4.Census
