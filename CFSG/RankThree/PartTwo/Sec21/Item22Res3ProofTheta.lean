module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofStatements
public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofRank
public import CFSG.RankThree.PartTwo.Sec21.Item228ResProofOne
public import CFSG.RankThree.PartTwo.Sec21.Item221Proof
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofPSp45Fact
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofInsp
import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofTheta
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools
public import CFSG.RankThree.PartTwo.Sec4.Item413Setup

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

namespace Item22Res3Proof

variable {G : Type} [Group G]

theorem odd_card_theta [Finite G] (h224 : Item224) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {X : Subgroup G}
    (hXa : X ∈ thetaComponentsAt 3 a) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    Odd (Nat.card (aschbacherSolvableCore 3 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hT3, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  set TG : Subgroup G := inSubgroup (aschbacherSolvableCore 3) X with hTG
  have hcardTG : Nat.card TG = Nat.card (aschbacherSolvableCore 3 X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  have hTG3 : ¬ 3 ∣ Nat.card TG := hcardTG ▸ hT3
  have hAT : A ≤ Subgroup.normalizer (TG : Set G) := le_normalizer_theta hAX
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hpair.mem_S.1.1
  let _ : MulDistribMulAction A TG := PartOne.conjActionOn hAT
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow 2 TG))
  have hcardSyl : ¬ 3 ∣ Nat.card (Sylow 2 TG) := fun h =>
    hTG3 ((h.trans (Sylow.card_dvd_index P₀)).trans (Subgroup.index_dvd_card _))
  obtain ⟨P, hP⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 TG) hcardSyl
  set P' : Subgroup G := (P : Subgroup TG).map TG.subtype with hP'def
  have hP'2 : IsPGroup 2 P' := P.isPGroup'.map TG.subtype
  have hAP' : A ≤ Subgroup.normalizer (P' : Set G) := by
    refine le_normalizer_of_forall_mul_mem fun e he p hp => ?_
    obtain ⟨p, hp, rfl⟩ := hp
    have hfix : (⟨e, he⟩ : A) • P = P := hP ⟨e, he⟩
    have hmem : (⟨e, he⟩ : A) • p ∈ (P : Subgroup TG) := by
      rw [← hfix, Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul p _ _ hp
    exact ⟨_, hmem, rfl⟩
  have hP'θ : P' ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) :=
    (Subgroup.map_subtype_le _).trans (theta_le_theta_centralizer hXa)
  have hcomm : ⁅P', A⁆ = ⊥ :=
    Sec6.commutator_eq_bot_of_mem_partTwoS hpair.mem_S haA ha1 le_rfl hP'θ hP'2 hAP'
  have hP'C : P' ≤ Subgroup.centralizer (A : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hodd := h224 G A E U c L hpair
  have hP'1 : P' = ⊥ := by
    obtain ⟨k, hk⟩ := hP'2.exists_card_eq
    have hdvd : Nat.card P' ∣ Nat.card (Subgroup.centralizer (A : Set G)) :=
      Subgroup.card_dvd_of_le hP'C
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.eq_bot_of_card_eq _ hk
    · exfalso
      have h2 : 2 ∣ Nat.card (Subgroup.centralizer (A : Set G)) :=
        (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hP1 : (P : Subgroup TG) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ TG.subtype_injective).mp hP'1
  rw [← hcardTG]
  by_contra hev
  have h2 : 2 ∣ Nat.card TG := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)
  exact P.ne_bot_of_dvd_card h2 hP1

theorem false_of_psp45 [Finite G] (h224 : Item224) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hP : StatedClassicalModel (X ⧸ aschbacherSolvableCore 3 X) .PSp 2 5 1) : False := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hA3 : IsPGroup 3 A := Sec5.isPGroup_of_isElemAbelian hAe
  obtain ⟨i, hi2, hfix⟩ := psp45AutThreeInv _ hP (Sec4.thetaAct hAX).range
    (Sec4.isElemAbelian_range_thetaAct hAX hAe)
  obtain ⟨y, hy, hyC⟩ := Item223KFactsProof.exists_lift_of_fixed hAX hA3 i
    (fun b => hfix _ ⟨b, rfl⟩)
  have h2 : 2 ∣ orderOf (y : G) := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) y
    rw [QuotientGroup.mk'_apply, hy, hi2] at h
    rwa [Subgroup.orderOf_coe]
  have hdvd : orderOf (y : G) ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : Subgroup.centralizer (A : Set G))
    rwa [Subgroup.orderOf_mk] at this
  exact (Nat.not_even_iff_odd.mpr (h224 G A E U c L hpair))
    (even_iff_two_dvd.mpr (h2.trans hdvd))

theorem eq_one_of_mem_center_of_isSimpleGroup {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : Group.IsPerfect Y) {z : Y} (hz : z ∈ Subgroup.center Y) : z = 1 := by
  rwa [Item223PrintProof.center_eq_bot_of_isSimpleGroup_of_isPerfect hY,
    Subgroup.mem_bot] at hz

theorem eq_one_of_mem_center_SL3 {Y : Type*} [Group Y] {m : ℕ} (e : Y ≃* SL3 m) {z : Y}
    (hz : z ∈ Subgroup.center Y) (hz2 : z ^ 2 = 1) : z = 1 := by
  have hz' : e z ∈ Subgroup.center (SL3 m) := Subgroup.mem_center_iff.mpr fun g => by
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz'
  rw [Fintype.card_fin] at hr3
  have h3 : (e z) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hr, ← map_pow, hr3, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have h2 : (e z) ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have h1 : e z = 1 := by
    calc e z = (e z) ^ 3 * ((e z) ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, inv_one, mul_one]
  exact e.injective (h1.trans (map_one e).symm)

theorem table_PSL_four_two :
    (Blueprint.Multiplier.genericOrders .PSL 4 2 1).1 *
        (Blueprint.Multiplier.genericOrders .PSL 4 2 1).2 *
        ((Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1).1 *
          (Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1).2) = 2 := by
  change Nat.gcd 4 (2 ^ 1 - 1) * 1 * (2 * 1) = 2
  norm_num

theorem table_PSL_five_two :
    (Blueprint.Multiplier.genericOrders .PSL 5 2 1).1 *
        (Blueprint.Multiplier.genericOrders .PSL 5 2 1).2 *
        ((Blueprint.Multiplier.exceptionalOrders .PSL 5 2 1).1 *
          (Blueprint.Multiplier.exceptionalOrders .PSL 5 2 1).2) = 1 := by
  change Nat.gcd 5 (2 ^ 1 - 1) * 1 * (1 * 1) = 1
  norm_num

theorem theta_eq_bot_of_PSL_two [Finite G]
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Subgroup G}
    (hq : IsQuasisimple X) (hodd : Odd (Nat.card (aschbacherSolvableCore 3 X))) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (h : StatedClassicalModel (lBar X) .PSL n 2 1) :
    inSubgroup (aschbacherSolvableCore 3) X = ⊥ := by
  have : IsSimpleGroup (lBar X) := Sec3.isSimpleGroup_of_statedClassicalModel_psl h
  have hZT := Item221Proof.center_eq_theta hq (Item221Proof.center_lBar_eq_bot hq)
  have hdvd := Item221Proof.card_center_dvd_table hGA hq.1
    (QuotientGroup.quotientMulEquivOfEq hZT) ⟨h.1, Or.inl h⟩
  have h2 : Nat.card (aschbacherSolvableCore 3 X) ∣ 2 := by
    rw [← hZT]
    rcases hn with rfl | rfl
    · rwa [table_PSL_four_two] at hdvd
    · rw [table_PSL_five_two] at hdvd
      exact hdvd.trans (one_dvd 2)
  have h1 : Nat.card (aschbacherSolvableCore 3 X) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
    · exact h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  exact Item221Proof.inSubgroup_theta_eq_bot (Subgroup.eq_bot_of_card_eq _ h1)

end Item22Res3Proof

open Item22Res3Proof

theorem item228ThetaTrivial_of
    (h224 : Item224) (h45 : Sec4.Item4_5)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h16 : List228Sixteen) : Item228ThetaTrivial := by
  intro G _ _ A E U c L hpair hA27 φ hφ X hX hKX m hm0 hme ⟨eK⟩ hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hpair.standing
  have hG := hst.toTheoremFourHyp
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨a, haA, ha1, hXa⟩ := mem_thetaComponentFamily_iff.mp hX.1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe haA ha1 X hXa
  have hXp : Group.IsPerfect X := Sec6.isPerfect_of_mem_thetaComponentsAt hXa
  have : Group.IsPerfect X := hXp
  have hXq : IsQuasisimple (lBar X) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXa
  have hodd := odd_card_theta h224 hpair haA ha1 hXa hAX
  have hnot2 : ¬ 2 ∣ Nat.card (aschbacherSolvableCore 3 X) := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hnP : ¬ StatedClassicalModel (lBar X) .PSp 2 5 1 := fun hP =>
    false_of_psp45 h224 hpair hAX hP
  obtain ⟨V, hV, n, hn4, hVn⟩ :
      ∃ V : Subgroup X, IsElemAbelian 2 V ∧ ∃ n : ℕ, 4 ≤ n ∧ Nat.card V = 2 ^ n := by
    by_cases hm2 : m = 2
    · subst hm2
      have hY : Nonempty (lBar X ≃* SL3 2) ∨ Nonempty (lBar X ≃* projSp 2 (GaloisField 2 2)) ∨
          Nonempty (lBar X ≃* projSU 4 2 2) ∨ Nonempty (lBar X ≃* projSU 5 2 2) ∨
          StatedClassicalModel (lBar X) .PSL 4 2 1 ∨
          StatedClassicalModel (lBar X) .PSL 5 2 1 := by
        rcases hL with (h | h | h | ⟨h4, -⟩ | ⟨-, h⟩) | ⟨-, hP⟩ | ⟨-, h | h⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · norm_num at h4
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact absurd hP hnP
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      obtain ⟨E', hE', hE'c⟩ := h16 (lBar X) hY
      obtain ⟨S, -, hS, hSc⟩ :=
        Classical2.exists_elemAbelian_lift (aschbacherSolvableCore 3 X) hnot2 hE'
      exact ⟨S, hS, 4, le_rfl, hSc.trans hE'c⟩
    · have hm4 : 4 ≤ m := by
        obtain ⟨k, rfl⟩ := hme
        omega
      obtain ⟨E₀, hE₀K, hE₀, hE₀c⟩ :=
        Item223PrintProof.exists_elemAbelian_of_mulEquiv_projSL (by omega) eK
      refine ⟨E₀.subgroupOf X, isElemAbelian_subgroupOf hE₀ X, m, hm4, ?_⟩
      rw [← hE₀c]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hE₀K.trans hKX)).toEquiv
  have hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s X < 3 := fun s hs hs3 =>
    lt_of_le_of_lt (localRank_subgroup_le hs X) (hG.localRank_lt s hs hs3)
  have key : (∀ z ∈ Subgroup.center (lBar X), z ^ 2 = 1 → z = 1) → IsQuasisimple X := fun hZ =>
    isQuasisimple_of_theta_le_center hXq (theta_le_center_of_rank hloc hXq hodd hZ hV hn4 hVn)
  have keyS : IsSimpleGroup (lBar X) → IsQuasisimple X := fun _ =>
    key fun _ hz _ => eq_one_of_mem_center_of_isSimpleGroup hXq.1 hz
  have hm2 : 2 ≤ m := by
    obtain ⟨k, rfl⟩ := hme
    omega
  rcases hL with (he | he | he | ⟨h4, he⟩ | ⟨-, he⟩) | ⟨-, hP⟩ | ⟨-, h | h⟩
  ·
    obtain ⟨e⟩ := he
    have hXqs := key fun _ hz hz2 => eq_one_of_mem_center_SL3 e hz hz2
    rcases Item221Proof.sl3_cases hGA hXqs hm0 hme e with heX | ⟨-, hT2, hT1⟩
    · obtain ⟨eX⟩ := heX
      exact Item222Proof.inSubgroup_theta_eq_bot_of_mulEquiv_SL3 hm0 hme eX
    · exfalso
      obtain ⟨k, hk⟩ := hT2.exists_card_eq
      rcases k with _ | k
      · exact hT1 (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
      · exact hnot2 (hk ▸ dvd_pow_self 2 (Nat.succ_ne_zero k))
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (projSp 2 (GaloisField 2 m)) := isSimpleGroup_projSp_two hm2
    have hXqs := keyS e.isSimpleGroup
    obtain ⟨eX⟩ := Item221Proof.nonempty_mulEquiv_projSp_two hGA hXqs hm2 e
    exact inSubgroup_theta_eq_bot_of_mulEquiv hXp eX
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (projSU 4 2 m) := isSimpleGroup_projSU le_rfl hm0
    have hXqs := keyS e.isSimpleGroup
    obtain ⟨eX⟩ := Item221Proof.nonempty_mulEquiv_of_center_eq_bot hXqs e fun e' =>
      Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hXqs.1 hm2 e'
    exact inSubgroup_theta_eq_bot_of_mulEquiv hXp eX
  ·
    obtain ⟨e⟩ := he
    have hm22 : 2 ≤ m / 2 := by omega
    have : IsSimpleGroup (projSU 4 2 (m / 2)) := isSimpleGroup_projSU le_rfl (by omega)
    have hXqs := keyS e.isSimpleGroup
    obtain ⟨eX⟩ := Item221Proof.nonempty_mulEquiv_of_center_eq_bot hXqs e fun e' =>
      Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hXqs.1 hm22 e'
    exact inSubgroup_theta_eq_bot_of_mulEquiv hXp eX
  ·
    obtain ⟨e⟩ := he
    have : IsSimpleGroup (projSU 5 2 2) := isSimpleGroup_projSU (by norm_num) (by norm_num)
    have hXqs := keyS e.isSimpleGroup
    obtain ⟨eX⟩ := Item221Proof.nonempty_mulEquiv_projSU_five hGA su54LocalRankFive hG hXqs e
    exact inSubgroup_theta_eq_bot_of_mulEquiv hXp eX
  ·
    exact absurd hP hnP
  ·
    have hXqs := keyS (Sec3.isSimpleGroup_of_statedClassicalModel_psl h)
    exact theta_eq_bot_of_PSL_two hGA hXqs hodd (Or.inl rfl) h
  ·
    have hXqs := keyS (Sec3.isSimpleGroup_of_statedClassicalModel_psl h)
    exact theta_eq_bot_of_PSL_two hGA hXqs hodd (Or.inr rfl) h

end CFSG.RankThree.PartTwo.Sec21
