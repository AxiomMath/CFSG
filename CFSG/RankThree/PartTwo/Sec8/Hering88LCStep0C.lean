module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCStep0B
public import CFSG.RankThree.PartTwo.Sec8.Hering88Swap
import CFSG.RankThree.PartTwo.Sec8.Hering88CCent
import CFSG.RankThree.PartTwo.Sec8.Hering88CInv
import CFSG.RankThree.PartTwo.Sec8.Hering88CEng
import CFSG.RankThree.PartTwo.Sec8.Hering88EM1
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeMain
import CFSG.LieType.Ree.ReeGenericPerfect
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofAssembly
import CFSG.HardMathSupport.Lang.E27Lie.TrialityTwo
import CFSG.RankThree.PartTwo.Sec8.Hering88NThm2P1
public import CFSG.RankThree.PartOne.D4RC.RxIso
public import CFSG.RankThree.PartOne.SEITZ7.D4Final
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofKFacts
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNF4G2
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityNFDefs
public import CFSG.RankThree.PartTwo.Sec8.Hering88FG2Two
public import CFSG.RankThree.PartTwo.Sec8.Hering88FReeAbs
public import CFSG.RankThree.PartTwo.Sec8.Hering88FSwap
public import CFSG.RankThree.PartTwo.Sec8.Hering88LCLift
public import CFSG.RankThree.PartTwo.Sec8.Hering88LCModelsB
public import CFSG.RankThree.PartTwo.Sec8.Hering88NThm2
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofOdd
public import CFSG.RankThree.PartTwo.Sec8.Item812Res6ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item83Proof
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDistinct
public import CFSG.RankThree.PartTwo.Sec8.Item84PairProofTheta419Assembly
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofAssembly
public import CFSG.RankThree.PartTwo.Sec8.Item87Res2Proof418
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2Final

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp projSU projImage)
open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open Hering88N
open Matrix


@[expose] def YbarOne (Q : Type) [Group Q] : Prop :=
  IsoTrialityD4 Q 1 ∨ IsoGTwoEven Q (3 * 1) ∨
    Nonempty (Q ≃* projSp 2 (GaloisField 2 (3 * 1))) ∨ IsoReeF4 Q (3 * 1)

theorem center_statedProj_sp4 {F : Type} [Field F] [Finite F] [CharP F 2]
    (z : StatedProj (StatedSp 2 F)) (hz : ∀ y, z * y = y * z) : z = 1 := by
  have hc' : projSpEquiv.symm z ∈ Subgroup.center (StatedSp 2 F) :=
    Subgroup.mem_center_iff.mpr fun y => by
      apply projSpEquiv.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact (hz (projSpEquiv y)).symm
  rw [KFacts.center_statedSp_eq_bot, Subgroup.mem_bot] at hc'
  rw [← MulEquiv.apply_symm_apply projSpEquiv z, hc', map_one]

theorem center_trivial_of_mulEquiv {Q M : Type*} [Group Q] [Group M] (e : Q ≃* M)
    (h : ∀ z : M, (∀ y, z * y = y * z) → z = 1) (z : Q) (hz : ∀ y, z * y = y * z) : z = 1 := by
  have : e z = 1 := h (e z) fun y => by
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz y]
  exact e.injective (this.trans (map_one e).symm)

theorem center_trivial_of_eq_bot {Q : Type*} [Group Q] (h : Subgroup.center Q = ⊥) (z : Q)
    (hz : ∀ y, z * y = y * z) : z = 1 := by
  have : z ∈ Subgroup.center Q := Subgroup.mem_center_iff.mpr fun y => (hz y).symm
  rwa [h, Subgroup.mem_bot] at this

theorem card_projSp_two_gt {m : ℕ} (hm : 3 ≤ m) :
    35942400 < Nat.card (projSp 2 (GaloisField 2 m)) := by
  rw [Sec19.Step1911Proof.card_projSp_two (by omega)]
  have hq : 8 ≤ 2 ^ m := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h1 : 4096 ≤ 2 ^ (m * 4) := by
    calc 4096 = 2 ^ (3 * 4) := by norm_num
      _ ≤ 2 ^ (m * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 63 ≤ (2 ^ m) ^ 2 - 1 := by
    have : 64 ≤ (2 ^ m) ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hq 2
    omega
  have h3 : 4095 ≤ (2 ^ m) ^ 4 - 1 := by
    have : 4096 ≤ (2 ^ m) ^ 4 := by
      calc 4096 = 8 ^ 4 := by norm_num
        _ ≤ (2 ^ m) ^ 4 := Nat.pow_le_pow_left hq 4
    omega
  calc 35942400 < 4096 * (63 * 4095) := by norm_num
    _ ≤ 2 ^ (m * 4) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)


theorem ybarOne_core (h45 : Sec4.Item4_5) (h83 : Item83) (h84 : Pair84A) (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} (h : Sec8Pair G A c L a b X 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {x : G}
    (hx : x = c ∨ x = b)
    (hxY : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    {A₀ : Subgroup G} {d' : G} {n' : ℕ} (hD : Data83 G a Y x A₀ d' n')
    {w : G} (hw : w = c ∨ w = b) {W : Subgroup G} (hJY : W ≤ Y)
    (hJb : W ≤ Subgroup.centralizer ({w} : Set G)) (hJp : Group.IsPerfect W)
    (hSW : SWFacts W)
    (hM1 : ∀ hS : IsSimpleGroup (inSubgroup perfectResidual
      (barCentralizer (Subgroup.zpowers w) Y)),
      Nat.card (W ⧸ aschbacherSolvableCore 3 W) =
        Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers w) Y))) :
    YbarOne (Y ⧸ aschbacherSolvableCore 3 Y) := by
  classical
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  obtain ⟨hbA', hb1', -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hbA : w ∈ A := by
    rcases hw with rfl | rfl
    · exact h.mem_A
    · exact hbA'
  have hb1 : w ≠ 1 := by
    rcases hw with rfl | rfl
    · exact h.ne_one
    · exact hb1'
  have hwcl : w ∈ Subgroup.closure ({c, b} : Set G) := by
    rcases hw with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  have hb3 : w ^ 3 = 1 := hA3 w hbA
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hbN : w ∈ Subgroup.normalizer (Y : Set G) := Hering88C.le_normalizer_of_pair h45 h hY hbA
  obtain ⟨hSJ, hNb⟩ := hSW
  have hN35 : Nat.card (W ⧸ aschbacherSolvableCore 3 W) ≤ 35942400 := by
    rcases hNb with h1 | h1 | ⟨-, h1⟩ <;> omega
  have hnot34 : ∀ {z : G} {A₁ : Subgroup G} {d₁ : G} {m : ℕ}, Data83 G a Y z A₁ d₁ m →
      ¬ (IsoSUThree (Y ⧸ aschbacherSolvableCore 3 Y) (2 ^ (3 * m)) ∨
        Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSU 3 2 (3 * m))) := by
    rintro z A₁ d₁ m hD₁ (hS | hP)
    · exact false_of_su3 hJY hD₁.odd hS hSJ
    · exact false_of_psu3 hJY hD₁.odd hP hSJ
  have hb_ne : barAut Y w hbN ≠ 1 := by
    intro h1
    have hSC := kF88SwapCent_holds h45 h84 G A c L a b X 1 h Y hY hIJ x hx hxY
    have hmem : w ∈ (Subgroup.zpowers a : Set G) := by
      rw [← hSC]
      refine ⟨hbA, fun z hz => ?_⟩
      have hzb := congrArg (fun φ : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) =>
        φ (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hz⟩)) h1
      simp only [MulAut.one_apply] at hzb
      rw [barAut_mk hbN hz (conj_mem_of_mem_normalizer hbN hz)] at hzb
      have hθ := (QuotientGroup.eq_iff_div_mem).mp hzb
      exact ⟨_, hθ, by simp [div_eq_mul_inv]⟩
    have hab : a ∈ Subgroup.zpowers w :=
      Item87Proof.mem_zpowers_of_mem_zpowers ha3 hb1 hmem
    exact Hering88C.a_not_mem_closure hF h ((Subgroup.zpowers_le.mpr hwcl) hab)
  have hb_out : ¬ KFacts.IsInnerAut (barAut Y w hbN) := by
    intro hin
    apply hb_ne
    have hs1 : (∃ s : W ⧸ aschbacherSolvableCore 3 W,
        (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) →
        ∃ s : W ⧸ aschbacherSolvableCore 3 W,
          (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 2 ^ 1 ≠ 1 := fun ⟨s, hs2, hs4⟩ =>
      ⟨s, hs2, fun h2 => hs4 (by rw [show (4 : ℕ) = 2 ^ 1 * 2 by norm_num, pow_mul, h2, one_pow])⟩
    have hs2 : (∃ s : W ⧸ aschbacherSolvableCore 3 W,
        (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) →
        ∃ s : W ⧸ aschbacherSolvableCore 3 W,
          (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 2 ^ 2 ≠ 1 := fun ⟨s, hs2, hs4⟩ =>
      ⟨s, hs2, by simpa using hs4⟩
    rcases hD.cases with h1 | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hP, -, -⟩ | ⟨⟨eS⟩, -, -⟩
    ·
      have hY1 := h1.1
      have hZ := center_trivial_of_eq_bot (Hering88F.center_eq_bot_of_case1 hY1)
      rcases hSJ with h8 | h5
      · exact barAut_eq_one_of_centExp hZ (centExp_case1 hD.odd hY1) hbN hb3 hJY hJb hJp
          (hs2 h8) hin
      · exact barAut_eq_one_of_centFive hZ (centFive_case1 hD.odd hY1) hbN hb3 hJY hJb hJp h5 hin
    ·
      obtain ⟨k, K, _, _, _, hkm, hK, ⟨e⟩⟩ := hR
      have hK' : Nat.card K = 2 ^ (2 * k + 1) := by rw [hK, hkm]
      have hZ := center_trivial_of_mulEquiv e (center_trivial_of_eq_bot
        (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial k K hK'))
      rcases hSJ with h8 | h5
      · exact barAut_eq_one_of_centExp hZ (CentExp.of_mulEquiv e (centExp_reeGamma hK')) hbN hb3
          hJY hJb hJp (hs2 h8) hin
      · exact barAut_eq_one_of_centFive hZ (CentFive.of_mulEquiv e (centFive_reeGamma hK')) hbN
          hb3 hJY hJb hJp h5 hin
    · exact (hnot34 hD (Or.inl hS)).elim
    · exact (hnot34 hD (Or.inr hP)).elim
    ·
      set F := GaloisField 2 (3 * n') with hFdef
      have hn1 : 1 ≤ n' := hD.odd.pos
      have hFc : Nat.card F = 2 ^ (3 * n') := GaloisField.card 2 _ (by omega)
      have hF4 : 4 ≤ Nat.card F := by
        rw [hFc]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (3 * n') := Nat.pow_le_pow_right (by norm_num) (by omega)
      set e : Y ⧸ aschbacherSolvableCore 3 Y ≃* StatedProj (StatedSp 2 F) :=
        eS.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).symm with he
      have hZ := center_trivial_of_mulEquiv e center_statedProj_sp4
      rcases hSJ with h8 | h5
      · exact barAut_eq_one_of_centExp hZ (CentExp.of_mulEquiv e (centExp_sp4 hF4)) hbN hb3 hJY
          hJb hJp (hs1 h8) hin
      · exact barAut_eq_one_of_centFive hZ
          (CentFive.of_mulEquiv e (centFive_sp4 hFc (Odd.mul (by decide) hD.odd) hF4)) hbN hb3
          hJY hJb hJp h5 hin
  have hbout : Sec4.InducesOuterTheta w Y := ⟨hbN, hb_out⟩
  have hbY : KFacts.InducesStdKind Y w .field ∨ KFacts.InducesStdKind Y w .graphField := by
    rcases hD.cases with h1 | ⟨hR, -, -⟩ | ⟨hS, -, -⟩ | ⟨hP, -, -⟩ | ⟨hSp, -, -⟩
    · rcases h1.1 with hDY | hGY
      · obtain ⟨hm1, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hDY
        exact Or.inr (KFacts.InducesStdKind.triality n' hm1 K hK σ hσ
          (KFacts.inducesKindTriality_graphField hm1 hK hσ Y hb3 hbout e))
      · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hGY
        haveI : CharP K 2 :=
          CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
            Nat.prime_two (k := 3 * n') (by have := hD.odd.pos; omega) hK
        have hK3 : ringChar K ≠ 3 := by rw [ringChar.eq K 2]; norm_num
        have hK4 : 4 ≤ Nat.card K := by
          rw [hK]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (3 * n') := Nat.pow_le_pow_right (by norm_num) (by have := hD.odd.pos; omega)
        exact Or.inl (KFacts.InducesStdKind.g2 K hK3 hK4
          (KFacts.inducesKindG2_field Y hK3 hK4 hb3 hbout e))
    · obtain ⟨k, K, _, _, _, hkm, hK, ⟨e⟩⟩ := hR
      have hk1 : 1 ≤ k := by have := hD.odd.pos; omega
      have hK' : Nat.card K = 2 ^ (2 * k + 1) := by rw [hK, hkm]
      exact Or.inl (KFacts.InducesStdKind.largeRee k hk1 K hK'
        (KFacts.inducesKindLargeRee_field Y hk1 hK'
          (CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj k K hK') hb3 hbout e))
    · exact (hnot34 hD (Or.inl hS)).elim
    · exact (hnot34 hD (Or.inr hP)).elim
    · exact Or.inl (KFacts.barCentralizer_mulEquiv_projSp (by have := hD.odd.pos; omega) hb3
        hbout hSp).1
  obtain ⟨A₀', d'', m, hD'⟩ := kF88Data83Y_of h83 (kF88SwapCent_holds h45 h84)
    (kF88SwapInv_holds h45 h84) h hY hIJ hw hbY
  have hm1 : 1 ≤ m := hD'.odd.pos
  rcases hD'.cases with ⟨hY1, -, hC⟩ | ⟨hR, hRC, -⟩ | ⟨hS, -, -⟩ | ⟨hP, -, -⟩ |
      ⟨hSp, ⟨ι⟩, -⟩
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by omega
      rcases hY1 with hD4 | hG2
      · exact Or.inl hD4
      · exact Or.inr (Or.inl hG2)
    · exfalso
      rcases hC with hG2 | ⟨-, hP, -⟩
      · have hS := Hering88E.isSimpleGroup_perfectResidual_of_isoGTwoEven hm2 hG2
        have := card_inSubgroup_perfectResidual_ge_of_isoGTwoEven hm2 hG2
        rw [← hM1 hS] at this
        omega
      · have hS := isSimpleGroup_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
        have hNY := hM1 hS
        have h3 := card_le_three_mul_card_inSubgroup_perfectResidual_of_isoPGUThree hm2 hP
        have hle := Subgroup.card_le_of_le
          (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers w) Y))
        have hcard := CFSG.HardMathSupport.Lang.E27Lie.card_isoPGUThree (by omega) hP
        rw [← hNY, hcard] at h3
        rw [← hNY, hcard] at hle
        exact false_of_pgu_bounds hD'.odd hm2 h3 hle hNb
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by omega
      exact Or.inr (Or.inr (Or.inr hR))
    · exfalso
      obtain ⟨k, K, _, _, _, hkm, hK, ⟨φ⟩⟩ := hRC
      have hk1 : 1 ≤ k := by omega
      have hK' : Nat.card K = 2 ^ (2 * k + 1) := by rw [hK, hkm]
      haveI : Group.IsPerfect (ReeTag.F4.reeGamma K k) :=
        ⟨ReeTag.commutator_reeGamma_eq_top (t := ReeTag.F4) hk1 hK'⟩
      haveI : IsSimpleGroup (ReeTag.F4.reeGamma K k) :=
        CFSG.SignalizerFunctorTheorem.CatalogBridge.isSimpleGroup_reeGamma_F4 hk1 hK'
      have hpC : Group.IsPerfect (barCentralizer (Subgroup.zpowers w) Y) :=
        Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      have hsC : IsSimpleGroup (barCentralizer (Subgroup.zpowers w) Y) := φ.isSimpleGroup
      have hres : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers w) Y) =
          barCentralizer (Subgroup.zpowers w) Y := inSubgroup_perfectResidual_of_isPerfect hpC
      have hS : IsSimpleGroup (inSubgroup perfectResidual
          (barCentralizer (Subgroup.zpowers w) Y)) := by
        rw [hres]
        exact hsC
      have hNY := hM1 hS
      rw [hres, Nat.card_congr φ.toEquiv] at hNY
      have hge := Item812Res2.card_reeGamma_ge_pow hK'
      have hq : 8 ≤ 2 ^ (2 * k + 1) :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h12 : 35942400 < (2 ^ (2 * k + 1)) ^ 12 :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_left hq 12)
      have hle : Nat.card (ReeTag.F4.reeGamma K k) ≤ 35942400 := by
        rw [← hNY]
        exact hN35
      exact absurd (h12.trans_le (hge.trans hle)) (lt_irrefl _)
  · exact (hnot34 hD' (Or.inl hS)).elim
  · exact (hnot34 hD' (Or.inr hP)).elim
  ·
    rcases Nat.lt_or_ge m 2 with hm | hm2
    · obtain rfl : m = 1 := by omega
      exact Or.inr (Or.inr (Or.inl hSp))
    · exfalso
      obtain ⟨hsC, hpC⟩ := isSimpleGroup_isPerfect_of_projSp hm2 ι
      have hres : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers w) Y) =
          barCentralizer (Subgroup.zpowers w) Y := inSubgroup_perfectResidual_of_isPerfect hpC
      have hS : IsSimpleGroup (inSubgroup perfectResidual
          (barCentralizer (Subgroup.zpowers w) Y)) := by
        rw [hres]
        exact hsC
      have hNY := hM1 hS
      rw [hres, Nat.card_congr ι.toEquiv] at hNY
      have h3m : 3 ≤ m := by
        obtain ⟨j, hj⟩ := hD'.odd
        omega
      have := card_projSp_two_gt h3m
      omega


theorem ybarOne_of (h45 : Sec4.Item4_5) (h83 : Item83) (h84 : Pair84A) (hF : KF84Field)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} (h : Sec8Pair G A c L a b X 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y) {x : G}
    (hx : x = c ∨ x = b)
    (hxY : KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField)
    {A₀ : Subgroup G} {d' : G} {n' : ℕ} (hD : Data83 G a Y x A₀ d' n') :
    YbarOne (Y ⧸ aschbacherSolvableCore 3 Y) := by
  classical
  obtain ⟨-, hA3⟩ := Hering88C.pair_commute_pow_three h
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  by_cases hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3
  ·
    obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
    have hbN : b ∈ Subgroup.normalizer (Y : Set G) := Hering88C.le_normalizer_of_pair h45 h hY hbA
    have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
    have hXb : X ≤ Subgroup.centralizer ({b} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp hX).1
    have hJX : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
    have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
    have hJ : sec8J X a ≠ ⊥ := Item812Res6.sec8J_ne_bot_of_gTwoPartner kF87INontriv_holds h84 h
    exact ybarOne_core h45 h83 h84 hF h hY hIJ hx hxY hD (Or.inr rfl) hJY (hJX.trans hXb)
      (Item87Proof.isPerfect_residual _) (xside_facts_of_unitary h84 h hU) fun hS =>
        card_quot_theta_eq_of_isSimpleGroup hJY
          (Hering88E.imageModTheta_sec8J_eq_perfectResidual kF87Cent_holds h84 h hJ hY hJY hbN
            hS) hS
  ·
    have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
      Hering88C.le_normalizer_of_pair h45 h hY h.mem_A
    have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
      (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
    have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
    have hIdef : sec8I L a =
        inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
      simp only [sec8I, hU, ↓reduceIte]
    have hIL : sec8I L a ≤ L := by
      rw [hIdef]
      exact (Item87Proof.residual_le _).trans inf_le_left
    have hIY : sec8I L a ≤ Y := le_sup_left.trans hIJ
    have hIp : Group.IsPerfect (sec8I L a) := by
      rw [hIdef]
      exact Item87Proof.isPerfect_residual _
    have hIL_img : imageModTheta L (sec8I L a) =
        inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) L) := by
      rw [hIdef]
      exact KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
    have hI : sec8I L a ≠ ⊥ := by
      intro hbot
      apply kF87INontriv_holds G L a 1 le_rfl
        (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) hU ha3 h.inducesStdKind h.gTwo
      rw [← hIL_img, hbot, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    exact ybarOne_core h45 h83 h84 hF h hY hIJ hx hxY hD (Or.inl rfl) hIY (hIL.trans hLc) hIp
      (lside_facts h hU) fun hS =>
        card_quot_theta_eq_of_isSimpleGroup hIY
          (Hering88E.imageModTheta_sec8I_eq_perfectResidual kF87Cent_holds h hU hI hY hIY hcN
            hS) hS

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
