module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Types
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec14.Item143Proof
import CFSG.RankThree.PartTwo.Sec15.Wales154J2Branch
public import CFSG.Sporadic.FischerOddCore.AlmostSimple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem pow_three_dvd_card_of_isoLThreePi {Q : Type} [Group Q] {p e : ℕ} [Fact p.Prime]
    (h : Sec4.IsoLThreePi Q p e) : (p ^ e) ^ 3 ∣ Nat.card Q := by
  have hp : p.Prime := Fact.out
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨he, ⟨φ⟩⟩
  · have hc := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField p e)
    rcases Nat.eq_zero_or_pos e with rfl | he1
    · simp
    rw [GaloisField.card p e (by omega), ← Nat.card_congr φ.toEquiv] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e - 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      have hq1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      have h1 : Nat.Coprime (p ^ e - 1) (p ^ e - 1 + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
      rw [Nat.sub_add_cancel hq1] at h1
      exact h1.symm
    exact hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)
  · have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · simp at he
      · exact h
    have hc := KFacts.KS14.card_projSU_three_mul_gcd p e he1
    rw [← Nat.card_congr φ.toEquiv] at hc
    have hcop : Nat.Coprime ((p ^ e) ^ 3) (Nat.gcd 3 (p ^ e + 1)) := by
      refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
      exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    exact hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)

theorem card_quot_pPrimeCore_dvd {Z : Type*} [Group Z] [Finite Z] :
    Nat.card (Z ⧸ CFSG.pPrimeCore 3 Z) ∣ Nat.card (Z ⧸ CFSG.pCore 2 Z) := by
  rw [← Subgroup.index, ← Subgroup.index]
  exact Subgroup.index_dvd_of_le pCore_two_le_pPrimeCore_three

section Branch


theorem item154ProperWhen_M22 (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8)
    (hK : KS154M22A7) :
    Item154ProperWhen fun Q _ => Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.M22) := by
  intro G _ _ A c L hR Y hY X hX hXY hYX ⟨φ⟩ R hRm
  have hN : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) = 443520 := by
    rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
  have hdvd := card_quot_dvd hXY
  have hle := two_mul_card_quot_le hXY hYX
  rw [hN] at hdvd hle
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hRm.2.1
  have hXR : X ≤ Subgroup.normalizer (R : Set G) := (le_sup_right : X ≤ A ⊔ X).trans hRm.2.2
  have hHJ : ¬ AllPointsHJ A := fun hHJ => by
    have h := card_of_type154_hj h148 h134 h48 hR hHJ hY.1
    rw [hN] at h
    revert h
    decide
  have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
    lB_eq_bot_of_not_allPointsHJ' h134 h48 hR.toSec14Std hHJ hB
  have hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    CFSG.Sporadic.FischerOddCore.center_eq_bot_of_mulEquiv φ
      CFSG.Sporadic.Schreier.m22_center_eq_bot'
  have heqY := pPrimeCore_eq_pCore_of_center_eq_bot hY.1 hZ
  set eY : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* CFSG.Blueprint.NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq heqY).trans φ with heYdef
  obtain ⟨c', hc', htrivY, L', hL', hL'M⟩ : ∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      (∀ y ∈ Y, c' * y * c'⁻¹ * y⁻¹ ∈ pPrimeCoreOf 3 Y) ∧ ∃ L' ∈ lA A c',
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) := by
    rcases read154_nhj h148 h134 h48 hR hHJ hY.1 with
      ⟨c', hc', htriv, L', hL', ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩ | ⟨p, f, e₀, hp, hf, he₀, hiso, hε⟩⟩ | ⟨⟨ψ⟩⟩ |
        ⟨-, -, n, m, -, -, hn, -, hiso, -⟩
    · exact ⟨c', hc', htriv, L', hL', ⟨ψ.symm.trans eY⟩⟩
    · exfalso
      have h1 := Nat.card_congr (eY.symm.trans ψ).toEquiv
      rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h1
      norm_num at h1
    · exact (KFacts.KS14.not_isLThreeEpsAt_M22 p f (IsLThreeEpsAt.of_mulEquiv eY hε)).elim
    · exfalso
      have h1 := Nat.card_congr (eY.symm.trans ψ).toEquiv
      rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at h1
      norm_num at h1
    · exact (KFacts.KS14.not_isoLThreePi_M22 2 (3 * n)
        (Proof1515.isoLThreePi_congr eY hiso)).elim
  obtain ⟨hc'A, hc'3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
  have hc'o : orderOf c' = 3 := by rw [← Nat.card_zpowers]; exact hc'3
  have h3L' : 3 ∣ Nat.card L' := by
    obtain ⟨ψ⟩ := hL'M
    have hc := Nat.card_congr ψ.toEquiv
    rw [KFacts.KS14.card_nativeM22] at hc
    have hdvd' := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L')
    rw [hc] at hdvd'
    exact (by norm_num : (3 : ℕ) ∣ 443520).trans hdvd'
  have htrivX' := trivial_of_le hXY (hX.1.2 hc'A) htrivY
  have hq3 := card_quot_pPrimeCore_dvd (Z := ↥X)
  have h35 : 35 ∣ Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) := by
    rcases read154_nhj h148 h134 h48 hR hHJ hX with
      ⟨c'', hc'', htriv'', L'', hL'', h2⟩ | ⟨ψ⟩ | ⟨-, -, n, m, -, -, hn, -, hiso, -⟩
    · obtain ⟨hc''A, hc''3, -⟩ := zpowers_mem_omegaA_iff.mp hc''
      have hc''1 : c'' ≠ 1 := by
        intro h1
        rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at hc''3
        omega
      have hmem := mem_zpowers_of_trivial hR.toSec14Std hLB hX hc''A hc''1 hc'A htriv'' htrivX'
      have hzz : Subgroup.zpowers c'' = Subgroup.zpowers c' := by
        refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_).symm
        rw [hc''3, hc'3]
      have hLc'' : L' ∈ thetaComponentsAt 3 c'' :=
        (Proof1515.thetaComponentsAt_eq_of_zpowers_eq hzz.symm) ▸ hL'.1
      have hL : L' = L'' := (hR.chosen136.2 c'' hc'' L'' hL'').2 L' hLc'' h3L'
      subst hL
      rcases h2 with ⟨⟨ψ⟩⟩ | ⟨-, ⟨ψ⟩⟩ | ⟨p, f, e₀, hp, hf, he₀, hiso, hε⟩
      · exfalso
        obtain ⟨ψM⟩ := hL'M
        have h1 := Nat.card_congr (ψ.trans ψM).toEquiv
        rw [KFacts.KS14.card_nativeM22] at h1
        rw [h1] at hq3
        have := Nat.le_of_dvd Nat.card_pos hq3
        omega
      · rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hq3
        exact (by norm_num : (35 : ℕ) ∣ 2520).trans hq3
      · obtain ⟨ψM⟩ := hL'M
        exact (KFacts.KS14.not_isoLThreePi_M22 p (f * e₀)
          (Proof1515.isoLThreePi_congr ψM hiso)).elim
    · exfalso
      obtain ⟨ψ⟩ := ψ
      rw [Nat.card_congr ψ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hq3
      have := Nat.le_of_dvd Nat.card_pos hq3
      omega
    · exfalso
      have h1 := (pow_three_dvd_card_of_isoLThreePi hiso).trans (hq3.trans hdvd)
      have h2 : 2 ^ 9 ∣ (2 ^ (3 * n)) ^ 3 := by
        rw [← pow_mul]
        exact pow_dvd_pow 2 (by omega)
      have := h2.trans h1
      norm_num at this
  exact Or.inl (commutator_le_of_M22 hK ⟨φ⟩ hXY (isPerfect_of_mem_scriptY4 hX) h35 hRm.1 hR2 hXR)

end Branch

end CFSG.RankThree.PartTwo.Sec15.Wales154
