module

public import CFSG.RankThree.PartTwo.Sec21.Item21EarlyProofQuasi
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (localRank)
open scoped commutatorElement

@[expose] def Item213CenterRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → CFSG.pCore 2 L = ⊥ →
      3 ∣ Nat.card (Subgroup.center (lBar L)) → 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L)

namespace Item21Early2Proof

open Item21EarlyProof

section General

variable {X : Type*} [Group X] [Finite X]

theorem pCore_three_le_center [Group.IsPerfect X] (T : Subgroup X) [T.Normal]
    [IsSimpleGroup (X ⧸ centerPre T)] (hT3 : ¬ 3 ∣ Nat.card T) :
    CFSG.pCore 3 X ≤ Subgroup.center X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 3 X with hOdef
  have hON : O.Normal := CFSG.pCore_normal
  have hO3 : IsPGroup 3 O := CFSG.pCore_isPGroup
  have hsol : Group.IsSolvable O := by
    have := hO3.isNilpotent
    infer_instance
  have hle : O ≤ centerPre T := Sec4.Census.le_of_isSolvable_of_normal hON hsol
  have hinf : O ⊓ T = ⊥ := by
    have h1 : IsPGroup 3 (O ⊓ T : Subgroup X) := hO3.to_le inf_le_left
    obtain ⟨k, hk⟩ := h1.exists_card_eq
    have hdvd : Nat.card (O ⊓ T : Subgroup X) ∣ Nat.card T :=
      Subgroup.card_dvd_of_le inf_le_right
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
    · exfalso
      apply hT3
      rw [hk] at hdvd
      exact (dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  have hxyO : ⁅x, y⁆ ∈ O := by
    rw [commutatorElement_def]
    have h1 : y * x⁻¹ * y⁻¹ ∈ O := hON.conj_mem _ (O.inv_mem hx) y
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact O.mul_mem hx h1
  have hxyT : ⁅x, y⁆ ∈ T := by
    rw [← QuotientGroup.ker_mk' T, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hle hx) _).symm
  have h1 : ⁅x, y⁆ = 1 := by
    have : ⁅x, y⁆ ∈ O ⊓ T := ⟨hxyO, hxyT⟩
    rwa [hinf, Subgroup.mem_bot] at this
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

omit [Finite X] in
theorem centralizer_eq_top_of_le_center {N : Subgroup X} (hN : N ≤ Subgroup.center X) :
    Subgroup.centralizer (N : Set X) = ⊤ :=
  Subgroup.centralizer_eq_top_iff_subset.mpr hN

end General

end Item21Early2Proof

open Item21EarlyProof Item21Early2Proof

theorem item213Center_of (h211 : Item211) (hOrd : KS213Order)
    (hNine : KS213Nine) (hRank : Item213CenterRank) : Item213Center := by
  intro G _ _ A E U c L hpair hO2 h3Z
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hc1 : c ≠ 1 := hpairs.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hX : IsBar211 (lBar L) := isBar211_of_case211 (h211 G A E U c L hpair)
  obtain ⟨hTs, -, hT3, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  set K₀ := centerPre T with hK₀
  have hK₀s : Group.IsSolvable K₀ := isSolvable_centerPre T hTs
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ K₀) := (centerPreEquiv T).isSimpleGroup
  have hbig : 5616 < Nat.card (L ⧸ K₀) := by
    rw [Nat.card_congr (centerPreEquiv T).toEquiv]
    exact hOrd _ hX
  have hL4 : SectionFourHyp L := by
    have hLtop : L ≠ ⊤ := fun hLt =>
      Sec6.centralizer_ne_top_of_ne_one hpair.standing.toTheoremFourHyp hc1
        (top_le_iff.mp (hLt ▸ Sec6.le_centralizer_of_mem_thetaComponentsAt hLc))
    exact hpair.standing.toTheoremFourHyp.sectionFourHyp hLtop
  have hrank := hRank G A E U c L hpair hO2 h3Z
  have hK₀top : K₀ ≠ ⊤ := QuotientGroup.nontrivial_iff.mp inferInstance
  have hctop : ∀ N : Subgroup L, N ≤ Subgroup.center L →
      ¬ Subgroup.centralizer (N : Set L) ≤ K₀ := by
    intro N hN hle
    rw [centralizer_eq_top_of_le_center hN, top_le_iff] at hle
    exact hK₀top hle
  by_contra hq
  obtain ⟨p₀, hp₀, hS₀⟩ := Sec4.Census.exists_centralizer_pCore_le hK₀s hq
  have hSp : ∀ p : ℕ, p.Prime → Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀ →
      3 < p ∧ CFSG.pCore p L ≠ ⊥ := by
    intro p hp hpS
    have : Fact p.Prime := ⟨hp⟩
    have hne : CFSG.pCore p L ≠ ⊥ := by
      intro h
      rw [h] at hpS
      exact hctop ⊥ bot_le hpS
    refine ⟨?_, hne⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hne hO2
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hctop _ (pCore_three_le_center T hT3) hpS
    have := hp.two_le
    omega
  by_cases hO : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
      Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀ ∧
      ∃ D : Subgroup L, Sec4.Census.CriticalAt p D ∧
        Odd (Nat.card (Subgroup.centralizer (D : Set L)))
  ·
    obtain ⟨p, hp, hp3, -, D, hD, hodd⟩ := hO
    have : Fact p.Prime := ⟨hp⟩
    have := Sec4.Census.twoRank_le_three hL4.localRank_lt hp3 hD hodd
    omega
  ·
    push Not at hO
    have hlin : ∀ p : ℕ, p.Prime → Subgroup.centralizer (CFSG.pCore p L : Set L) ≤ K₀ →
        ∃ (N : Subgroup L) (_ : N.Normal), Sec4.Census.LinearOutcome L p N := by
      intro p hp hpS
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨hp3, hne⟩ := hSp p hp hpS
      obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt (by omega) hne
      have heven := hO p hp hp3 hpS D hD
      rw [Nat.not_odd_iff_even] at heven
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer (D : Set L)) 2
        (even_iff_two_dvd.mp heven)
      have ht' : orderOf (t : L) = 2 := by rwa [Subgroup.orderOf_coe]
      have hr := Sec4.Census.pRank_le_localRank_of_centralizes hp (by omega) ht'
        (fun h hh => Subgroup.mem_centralizer_iff.mp t.2 h hh)
      have := hL4.localRank_lt p hp hp3
      exact Sec4.Census.linearOutcome_of_criticalAt hK₀s hp3 hpS hD (by omega)
    rcases Sec4.Census.linear_endgame hK₀s hO2 hp₀ hS₀ hlin with ⟨⟨e⟩⟩ | ⟨p, hp, hp3, ⟨e⟩⟩ |
        ⟨⟨e⟩⟩
    ·
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) = 120 := by
        rw [Sec4.Census.card_SL2]
        norm_num
      exact Sec13.false_of_surjective_of_card_lt hK₀s (e.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)
    ·
      have : Fact p.Prime := ⟨hp⟩
      have e' : L ⧸ Sec4.oTwoP p L ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
        (QuotientGroup.quotientMulEquivOfEq (Sec4.Census.oTwoP_eq_of_pCore_two_eq_bot p hO2)).trans
          e
      obtain ⟨E', hE'3, hE'9⟩ := hNine _ hX
      obtain ⟨E₀, hE3, hE9⟩ := exists_nine_quotient T hE'3 hE'9
      exact Sec13.false_of_oTwoP_equiv_SL2 hp hp3 e' hE3 hE9
    ·
      have hc := Sec4.Census.card_SL3_three
      exact Sec13.false_of_surjective_of_card_lt hK₀s (e.toMonoidHom.comp (QuotientGroup.mk' _))
        (e.surjective.comp (QuotientGroup.mk'_surjective _)) (by omega) (by omega)

end CFSG.RankThree.PartTwo.Sec21
