module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Assembly
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec15.Wales154Five

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem checkSL_a10 : ∀ q < 122, 2 ≤ q → q ^ 3 ∣ 1814400 →
    1814400 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_a10 : ∀ q < 122, 2 ≤ q → q ^ 3 ∣ 1814400 →
    1814400 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem not_isLThreeEpsAt_of_card_a10 {X : Type} [Group X] (hX : Nat.card X = 1814400)
    (p f : ℕ) [Fact p.Prime] : ¬ IsLThreeEpsAt X p f :=
  KFacts.KS14.not_isLThreeEpsAt_of_card hX
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_a10)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_a10) p f

omit [Finite G] in
theorem center_eq_bot_of_isQuasisimple_of_isSimple {Q : Type*} [Group Q]
    (hq : CFSG.IsQuasisimple Q) (hs : IsSimpleGroup Q) : Subgroup.center Q = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    have : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hq
    have : Group.IsPerfect Q := hq.1
    have hcomm : ∀ a b : Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
    exact Group.IsPerfect.not_isSolvable Q (isSolvable_of_comm hcomm)

@[expose] noncomputable def Item154L3Point (P : ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ Y ∈ scriptY0 A (lB A), ∀ X ∈ scriptY4 A (lB A), X ≤ Y →
      Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y →
      ∀ (c' : G) (L' : Subgroup G) (r e f : ℕ) (_ : Fact r.Prime), P r → 1 ≤ e → 1 ≤ f →
        f ∣ e → Subgroup.zpowers c' ∈ omegaA A →
        (∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) →
        L' ∈ lA A c' → Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') r e →
        IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) r f →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

section Five

@[expose] noncomputable def Item154L3Five : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ¬ AllPointsHJ A → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY0 A (lB A)),
      ∀ X ∈ scriptY4 A (lB A), X ≤ Y → Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y →
      ∀ (c₅ : G) (L₅ : Subgroup G) (n m : ℕ), Subgroup.zpowers c₅ ∈ omegaA A → L₅ ∈ lA A c₅ →
        1 ≤ n → 1 ≤ m → Sec4.IsoLThreePi (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) 2 (3 * n) →
        IsLThreeEpsAt (↥L₅ ⧸ aschbacherSolvableCore 3 ↥L₅) 2 (n * m) →
        (∀ a ∈ A, (∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) → a = 1) →
        (letI := ker148_normal hY.1.1.2; Case148Five A (lB A) Y) →
      ∀ R ∈ invariantPiSubgroups (Subgroup.normalizer (Y : Set G)) (A ⊔ X) (piOf 2),
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R

end Five

section Read


theorem item154ProperWhenNHJ_L3_of (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hodd : Item154L3Point (· ≠ 2)) (htwo : Item154L3Point (· = 2)) (h5 : Item154L3Five) :
    Item154ProperWhenNHJ fun Q _ =>
      ∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ≠ 3 ∧ IsLThreeEpsAt Q p f := by
  intro G _ _ A c L hR hNHJ Y hY X hX hXY hYX ⟨p, f, hp, hf, hp3, hε⟩ R hRm
  have hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.1.2.2.2
  have hs := Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε
  have hZ := center_eq_bot_of_isQuasisimple_of_isSimple hq hs
  have heq := pPrimeCore_eq_pCore_of_center_eq_bot hY.1 hZ
  set eY : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
    QuotientGroup.quotientMulEquivOfEq heq with heYdef
  have : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hq.1
  have : Group.IsPerfect (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  have : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have : Nontrivial (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := eY.symm.injective.nontrivial
  have hε3 : IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f := IsLThreeEpsAt.of_mulEquiv eY.symm hε
  have hdisp : ∀ (c' : G) (L' : Subgroup G) (r e f : ℕ) (_ : Fact r.Prime), 1 ≤ e → 1 ≤ f →
      f ∣ e → Subgroup.zpowers c' ∈ omegaA A →
      (∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) →
      L' ∈ lA A c' → Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') r e →
      IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) r f →
        ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ Case154Two L Y X ∨ Case154Three A L Y X R := by
    intro c' L' r e f' hr he hf' hfe hc' htriv hL' hiso hε'
    by_cases hr2 : r = 2
    · exact htwo G A c L hR hNHJ Y hY X hX hXY hYX c' L' r e f' hr hr2 he hf' hfe hc' htriv hL'
        hiso hε' R hRm
    · exact hodd G A c L hR hNHJ Y hY X hX hXY hYX c' L' r e f' hr hr2 he hf' hfe hc' htriv hL'
        hiso hε' R hRm
  rcases read154_nhj5 h148 h134 h48 hR hNHJ hY.1 with
    ⟨c', hc', htriv, L', hL', ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩ | ⟨r, f', e', hr, hf', he', hiso, hε'⟩⟩ | ⟨ψ⟩ |
      ⟨c₅, L₅, n, m, hc₅, hL₅, hn, hm, hiso, hε5, hC, hC5⟩
  · rcases (hR.chosen136.2 c' hc' L' hL').1 with ⟨⟨φJ⟩⟩ | ⟨r, e, hr, he, hiso⟩ | ⟨⟨φ7⟩⟩ |
        ⟨⟨φM⟩⟩ | ⟨⟨φM⟩⟩
    · exact (hNHJ (allPointsHJ_of_point h134 h48 hR.toSec14Std hc' hL' ⟨φJ⟩)).elim
    · have hiso' := Proof1515.isoLThreePi_congr ψ.symm hiso
      exact hdisp c' L' r e e hr he he dvd_rfl hc' htriv hL' hiso
        (Sec14.isLThreeEpsAt_of_isoLThreePi148 hiso')
    · exact (Proof1515.not_isLThreeEpsAt_of_card_2520
        (by rw [Nat.card_congr (ψ.trans φ7).toEquiv, card_alternatingGroup_seven]) p f hε3).elim
    · exact (KFacts.KS14.not_isLThreeEpsAt_M22 p f
        (IsLThreeEpsAt.of_mulEquiv (ψ.trans φM) hε3)).elim
    · exact (KFacts.KS14.not_isLThreeEpsAt_M12 p f
        (IsLThreeEpsAt.of_mulEquiv (ψ.trans φM) hε3)).elim
  · exact (Proof1515.not_isLThreeEpsAt_of_card_2520
      (by rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_seven]) p f hε3).elim
  · exact hdisp c' L' r (f' * e') f' hr (Nat.mul_pos hf' he') hf' (Dvd.intro e' rfl) hc' htriv
      hL' hiso hε'
  · obtain ⟨ψ⟩ := ψ
    exact (not_isLThreeEpsAt_of_card_a10
      (by rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_ten]) p f hε3).elim
  · exact h5 G A c L hR hNHJ Y hY X hX hXY hYX c₅ L₅ n m hc₅ hL₅ hn hm hiso hε5 hC hC5 R hRm

end Read

end CFSG.RankThree.PartTwo.Sec15.Wales154
