module

public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA10
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofList
import CFSG.RankThree.PartTwo.Sec15.Item153Push2Proof
import CFSG.RankThree.PartTwo.Sec14.Ronan148KPoint
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.ON
import CFSG.RankThree.PartTwo.Sec14.Item148StepCases
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.Assembly.RankThreeEven (projSL)

section Reading

theorem type153Fine_of_item148R
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
        IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON := by
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have hnt : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hYΔ := Proof1523Res3.eq_deltaZero_of_mem_scriptY4 h134 h48 hR hY4
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have key : ∀ {S : Type} [Group S], Proof1515.MultFree S →
      Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* S) → Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* S) :=
    fun hm hS => Proof1515.nonempty_quot_pCore_two_equiv_of_multFree hY4 hS hm
  have hL3eps : ∀ {p f : ℕ} [Fact p.Prime], 1 ≤ f → p ≠ 3 →
      IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f := by
    intro p f hp hf hp3 hε
    have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
      Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun Z _ hZc hcop ⟨φ⟩ =>
        Proof1511Steps.eq_bot_of_isLThreeEpsAt _ Z hperf hZc hcop hf
          (IsLThreeEpsAt.of_mulEquiv φ.symm hε)
    exact ⟨p, f, hp, hf, hp3,
      IsLThreeEpsAt.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq heq) hε⟩
  have hL3pi : ∀ {p e : ℕ} [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p e →
        ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pCore 2 ↥Y) p f := by
    intro p e hp he hiso
    obtain ⟨φ⟩ := key (Proof1515.multFree_of_isLThreePi ⟨p, e, hp, he, hiso⟩)
      (⟨MulEquiv.refl _⟩ : Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y))
    exact ⟨p, e, hp, he, Sec14.Ronan148K.ne_three_of_isoLThreePi he hiso,
      Sec14.isLThreeEpsAt_of_isoLThreePi148 (Proof1515.isoLThreePi_congr φ.symm hiso)⟩
  rcases Proof1515.cases148_of_mem_scriptY4 (h148 G A c L hR) hR.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ | ⟨⟨φ10⟩, -, -⟩ |
      ⟨c', L', n, m, hc', hL', hn, hm, hiso, -⟩
  ·
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e₀, hp, hf, he₀, hiso, hε⟩ | ⟨-, h6 | ⟨⟨φ⟩⟩⟩
    ·
      rcases (hR.chosen136.2 c' hc' L' hL').1 with ⟨⟨φJ⟩⟩ | ⟨p, e₀, hp, he, hiso⟩ | ⟨⟨φ7⟩⟩ | ⟨⟨φM⟩⟩ |
        ⟨⟨φM⟩⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl (key Proof1515.multFree_J2 ⟨φ.trans φJ⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (hL3pi he (Proof1515.isoLThreePi_congr φ.symm hiso))))))
      · exact Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_alternatingGroup_seven ⟨φ.trans φ7⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_M22 ⟨φ.trans φM⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (key Proof1515.multFree_M12 ⟨φ.trans φM⟩)))))))
    ·
      exact Or.inr (Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩)))
    ·
      have hf' : 1 ≤ f * e₀ := Nat.mul_pos hf he₀
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hL3eps hf (Sec14.Ronan148K.ne_three_of_isoLThreePi hf' hiso) hε)))))
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 1080 := by
        rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inr rfl) hp hp6
      exact Or.inr (Or.inl
        (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6))
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 60 := by
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hq hne fun p hp hp6 => by
          rw [hc]
          exact Proof1515.not_sq_dvd_small (Or.inl rfl) hp hp6
      exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq.symm).trans φ⟩
  ·
    rcases h3 with hON | ⟨⟨φ⟩⟩ | ⟨hp7, ⟨φ⟩⟩
    · have heq : CFSG.pPrimeCore 3 ↥Y = CFSG.pCore 2 ↥Y :=
        Proof1515.pPrimeCore_three_eq_pCore_two_of hq hne fun Z _ hZc hcop ⟨φ⟩ =>
          ks1515ONMult _ Z hperf hZc hcop (Proof1515.isTripleCover_congr φ.symm hON)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Proof1515.isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) hON))))))))
    · exact Or.inr (Or.inr (Or.inl (key Proof1515.multFree_alternatingGroup_seven ⟨φ⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        (hL3eps (p := 7) (f := 1) le_rfl (by norm_num) (Or.inl ⟨φ⟩))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (key Proof1515.multFree_alternatingGroup_ten ⟨φ10⟩))))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hL3pi (p := 2) (by omega) hiso)))))

theorem type153_of_item148R
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (hR : Sec15R G A c L) {Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    Listed315 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsL3Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨ IsM22Type153 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 10)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON := by
  rcases type153Fine_of_item148R h148 h134 h48 hR hY with hA5 | h6 | hA7 | hJ | ⟨p, f, hp, hf, -, hε⟩ |
    hM22 | hM12 | hA10 | hON
  · obtain ⟨φ⟩ := hA5
    obtain ⟨κ⟩ := nonempty_projSL_two_two_mulEquiv_alt5
    exact Or.inl (Or.inl ⟨2, by norm_num, ⟨1, rfl⟩, ⟨φ.trans κ.symm⟩⟩)
  · exact Or.inl (Or.inr (Or.inl h6))
  · exact Or.inl (Or.inr (Or.inr hA7))
  · exact Or.inr (Or.inl hJ)
  · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨p, f, hp, hε⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl hM22))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hM12))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA10)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hON)))))

end Reading

theorem step153PushRestR_of_inputs
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) (h149 : Sec16.Item149S14)
    (htwin : Claim153TwinR) : Step153PushRestR := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY hnL hJ hL3 hM22 hM12 hA10
  rcases type153_of_item148R h148 h134 h48 hR hY with h | ⟨⟨φ⟩⟩ | h | h | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | hON
  · exact (hnL h).elim
  · exact (hJ.false φ).elim
  · exact (hL3 h).elim
  · exact (hM22 h).elim
  · exact (hM12.false φ).elim
  · exact (hA10.false φ).elim
  · obtain ⟨-, ⟨e⟩⟩ := hON
    exact concl153Push_of_noFFModule h149 htwin hR hY hS hno hFF hSY
      (noFFModule_of_noIrrFFOffender FFSporadic.noIrrFFOffender_ONan_native) e

end CFSG.RankThree.PartTwo.Sec15.F153
