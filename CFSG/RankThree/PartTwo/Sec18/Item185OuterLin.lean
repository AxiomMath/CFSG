module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterBase
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank
import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryRank
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
import CFSG.Quasithin.Background.Harris.OrdinaryProofs.CoverSU3
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Easy

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL linearAutGroup)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU)
open CFSG.RankThree.PartTwo.KFacts (psuConj)

@[expose] def FixedFactsAt {S : Type} [Group S] (σ : MulAut S) : Prop :=
  (∃ N : Subgroup (fixedSubgroup σ), N.Normal ∧ IsSimpleGroup N ∧
      ¬ (∀ x y : N, x * y = y * x) ∧ Subgroup.centralizer (N : Set (fixedSubgroup σ)) = ⊥) ∨
    ¬ 9 ∣ Nat.card (fixedSubgroup σ)

@[expose] def GapL3Field : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ n → Even n → 3 ∣ n →
    ∀ σ : MulAut (projectiveSL 3 K), σ ^ 3 = 1 → σ ∉ linearAutGroup 3 K → FixedFactsAt σ

@[expose] def GapU3Field : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K), Odd f → 9 ≤ f → 3 ∣ f →
    ∀ σ : MulAut (unitaryPSU h 3), σ ^ 3 = 1 → σ ∉ (psuConj h).range → FixedFactsAt σ

private theorem isElemAbelian_comm_lin {p : ℕ} {G : Type} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private theorem four_pow_mod_three_lin (m : ℕ) : 4 ^ m % 3 = 1 := by
  rw [Nat.pow_mod]
  norm_num

private theorem two_pow_mod_three_of_even_lin {n : ℕ} (h : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨m, rfl⟩ := h
  have h4 : (2 : ℕ) ^ (m + m) = 4 ^ m := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [h4]
  exact four_pow_mod_three_lin m

private theorem two_pow_mod_three_of_odd_lin {n : ℕ} (h : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := h
  have h4 : (2 : ℕ) ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  rw [h4]
  have := four_pow_mod_three_lin m
  omega

private theorem three_dvd_two_pow_sub_one_of_even_lin {n : ℕ} (h : Even n) :
    3 ∣ 2 ^ n - 1 := by
  have h1 := two_pow_mod_three_of_even_lin h
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  omega

private theorem two_lt_two_pow_lin {n : ℕ} (hn : 2 ≤ n) : 2 < 2 ^ n :=
  calc 2 < 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

private theorem false_of_diag_lin {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (L : Subgroup (MulAut S)) (hinn : innerAut S ≤ L)
    (hL : ∀ B' : Subgroup (MulAut S), B' ≤ L → IsElemAbelian 3 B' → Nat.card B' ≤ 9)
    {σ : MulAut S} (hσL : σ ∈ L) (hσ : σ ∉ innerAut S) (hσ3 : σ ^ 3 = 1)
    (B : Subgroup S) (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 9)
    (hBO : B ≤ oTwoThreeFixed σ) : False := by
  have hκ : Function.Injective (MulAut.conj : S →* MulAut S) :=
    Sec4.RonanK429.conj_injective_of_center_eq_bot hZ
  set T : Subgroup (MulAut S) := B.map (MulAut.conj : S →* MulAut S) with hT
  have hTc : Nat.card T = 9 := by
    rw [hT, Subgroup.card_map_of_injective hκ]
    exact hBc
  have hTinn : T ≤ innerAut S := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact MonoidHom.mem_range.mpr ⟨b, rfl⟩
  have hfix : ∀ b ∈ B, σ b = b := by
    intro b hb
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp (hBO hb)
    exact x.2
  have hcomm : ∀ b ∈ B, σ * MulAut.conj b = MulAut.conj b * σ := by
    intro b hb
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix b hb]
  set G0 : Set (MulAut S) := insert σ (T : Set (MulAut S)) with hG0def
  have hG0 : ∀ x ∈ G0, ∀ y ∈ G0, x * y = y * x := by
    intro x hx y hy
    simp only [hG0def, Set.mem_insert_iff, SetLike.mem_coe] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy]
    · rw [hx]
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      exact hcomm b hb
    · rw [hy]
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      exact (hcomm b hb).symm
    · obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hy
      rw [← map_mul, ← map_mul, isElemAbelian_comm_lin hB hb hb']
  set B' : Subgroup (MulAut S) := Subgroup.closure G0 with hB'def
  have hcent : Subgroup.closure G0 ≤ Subgroup.centralizer G0 := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact hG0 h hh g hg
  have hcc : Subgroup.closure G0 ≤
      Subgroup.centralizer (Subgroup.centralizer G0 : Set (MulAut S)) := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hh
    exact (hh g hg).symm
  have hBcomm : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hcc hy) x (hcent hx)
  have hexp : ∀ x ∈ B', x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => x ^ 3 = 1)
      (fun g hg => ?_) ?_ (fun x y hx hy ihx ihy => ?_) (fun x _ ihx => ?_) hx
    · show g ^ 3 = 1
      simp only [hG0def, Set.mem_insert_iff, SetLike.mem_coe] at hg
      rcases hg with hg | hg
      · rw [hg]
        exact hσ3
      · obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hg
        rw [← map_pow, hB.2 b hb, map_one]
    · exact one_pow 3
    · have ihx' : x ^ 3 = 1 := ihx
      have ihy' : y ^ 3 = 1 := ihy
      show (x * y) ^ 3 = 1
      rw [(show Commute x y from hBcomm x hx y hy).mul_pow, ihx', ihy', one_mul]
    · have ihx' : x ^ 3 = 1 := ihx
      show x⁻¹ ^ 3 = 1
      rw [inv_pow, ihx', inv_one]
  have hBE : IsElemAbelian 3 B' :=
    ⟨⟨⟨fun a b => Subtype.ext (hBcomm a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hexp x hx⟩
  have hB'L : B' ≤ L := by
    rw [hB'def, Subgroup.closure_le]
    intro g hg
    simp only [hG0def, Set.mem_insert_iff, SetLike.mem_coe] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact hσL
    · exact hinn (hTinn hg)
  have hσB' : σ ∈ B' := Subgroup.subset_closure (Set.mem_insert σ _)
  have hTB' : T ≤ B' := by
    intro x hx
    exact Subgroup.subset_closure (Set.mem_insert_of_mem σ hx)
  have hle : Nat.card B' ≤ Nat.card T := by
    rw [hTc]
    exact hL B' hB'L hBE
  have heq : T = B' := Subgroup.eq_of_le_of_card_ge hTB' hle
  have hσT : σ ∈ T := by
    rw [heq]
    exact hσB'
  exact hσ (hTinn hσT)

private theorem false_of_fixedFactsAt_lin {S : Type} [Group S] [Finite S] {σ : MulAut S}
    (hF : FixedFactsAt σ) (B : Subgroup S) (hBc : Nat.card B = 9)
    (hBO : B ≤ oTwoThreeFixed σ) : False := by
  unfold FixedFactsAt at hF
  rcases hF with ⟨N, hN, hsimp, hna, hcent⟩ | hnd
  · haveI := hN
    have hO := oTwoP_le_centralizer_of_simple_normal N hsimp hna
    rw [hcent] at hO
    have hB0 : B ≤ ⊥ := by
      intro b hb
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (hBO hb)
      have hx1 : x = 1 := Subgroup.mem_bot.mp (hO hx)
      rw [Subgroup.mem_bot]
      simp [hx1]
    have hBbot : B = ⊥ := le_bot_iff.mp hB0
    rw [hBbot, Subgroup.card_bot] at hBc
    omega
  · apply hnd
    have hBH : B ≤ fixedSubgroup σ := fun b hb => Subgroup.map_subtype_le _ (hBO hb)
    have hdvd := Subgroup.card_dvd_of_le hBH
    rw [hBc] at hdvd
    exact hdvd

private theorem fixedFactsAt_of_quasisimple_lin {S : Type} [Group S] {σ : MulAut S}
    (hZ : Subgroup.center (fixedSubgroup σ) = ⊥) (hq : CFSG.IsQuasisimple (fixedSubgroup σ)) :
    FixedFactsAt σ := by
  obtain ⟨-, hsimp, a, b, hab⟩ := hq
  have hsC : IsSimpleGroup (fixedSubgroup σ) := by
    haveI := hsimp
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  unfold FixedFactsAt
  left
  refine ⟨⊤, inferInstance, ?_, ?_, ?_⟩
  · haveI := hsC
    exact Subgroup.topEquiv.isSimpleGroup
  · rintro h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hxy : x * y = y * x :=
      congrArg Subtype.val (h ⟨x, Subgroup.mem_top x⟩ ⟨y, Subgroup.mem_top y⟩)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]
  · rw [Subgroup.coe_top, Subgroup.centralizer_univ, hZ]

private theorem noOmega_of_diag_fixed_lin {S : Type} [Group S] [Finite S]
    (hZ : Subgroup.center S = ⊥) (L : Subgroup (MulAut S)) (hinn : innerAut S ≤ L)
    (hL : ∀ B' : Subgroup (MulAut S), B' ≤ L → IsElemAbelian 3 B' → Nat.card B' ≤ 9)
    (h : ∀ σ : MulAut S, σ ∉ innerAut S → σ ^ 3 = 1 → σ ∉ L → FixedFactsAt σ) : NoOmega S := by
  intro σ hσ hσ3 B hB hBc hBO
  by_cases hσL : σ ∈ L
  · exact false_of_diag_lin hZ L hinn hL hσL hσ hσ3 B hB hBc hBO
  · exact false_of_fixedFactsAt_lin (h σ hσ hσ3 hσL) B hBc hBO

section Classical


private theorem noOmega_projSL_odd_lin {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    NoOmega (projSL 3 (GaloisField 2 n)) := by
  have hcard : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n (by omega)]
    exact two_pow_mod_three_of_odd_lin hodd
  refine noOmega_of_fixed_facts (fun σ hσ hσ3 => ?_)
  obtain ⟨h0, hq⟩ := KFacts.fixedPoints_facts_of_mulEquiv_projSL hcard (MulEquiv.refl _) hσ3 hσ
  exact fixedFactsAt_of_quasisimple_lin (σ := σ) h0 hq

private theorem noOmega_projectiveSL_even_lin (hK2 : GapL3Field) {n : ℕ} (hn : 1 ≤ n)
    (heven : Even n) (h3 : 3 ∣ n) : NoOmega (projectiveSL 3 (GaloisField 2 n)) := by
  haveI : Finite (projectiveSL 3 (GaloisField 2 n)) :=
    Finite.of_equiv (projSL 3 (GaloisField 2 n)) (Sec4.projSLEquivProjectiveSL 3 _).toEquiv
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have hK3 : 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [hcard]
    exact three_dvd_two_pow_sub_one_of_even_lin heven
  refine noOmega_of_diag_fixed_lin
    (RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := GaloisField 2 n) le_rfl)
    (linearAutGroup 3 (GaloisField 2 n)) (KFacts.innAut_le_linearAutGroup 3 _)
    (fun B' hB' hE => Sec19.Item19Res5Proof.card_le_nine_of_le_linearAutGroup hK3 B' hB'
      (fun x hx y hy => isElemAbelian_comm_lin hE hx hy) (fun x hx => hE.2 x hx))
    (fun σ _ hσ3 hσL => hK2 n (GaloisField 2 n) hcard heven h3 σ hσ3 hσL)

private theorem noOmega_unitaryPSU_even_lin {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) : NoOmega (unitaryPSU hU 3) := by
  haveI : Finite (unitaryPSU hU 3) :=
    Finite.of_equiv (projSU 3 2 n) (Sec4.projSUEquivUnitaryPSU 2 n hU).toEquiv
  have hq : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even_lin heven
  have hq2 : 2 < 2 ^ n := two_lt_two_pow_lin hn
  refine noOmega_of_fixed_facts (fun σ hσ hσ3 => ?_)
  obtain ⟨h0, hq'⟩ :=
    KFacts.fixedPoints_facts_of_mulEquiv_unitaryPSU hU hq hq2 (MulEquiv.refl _) hσ3 hσ
  exact fixedFactsAt_of_quasisimple_lin (σ := σ) h0 hq'

private theorem noOmega_unitaryPSU_odd_lin {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n) (h3 : 3 ∣ n)
    (h9 : 9 ≤ n) (hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n))) (hK3 : GapU3Field) :
    NoOmega (unitaryPSU hU 3) := by
  haveI : Finite (unitaryPSU hU 3) :=
    Finite.of_equiv (projSU 3 2 n) (Sec4.projSUEquivUnitaryPSU 2 n hU).toEquiv
  have hq2 : 2 < 2 ^ n := two_lt_two_pow_lin hn
  have hZ : Subgroup.center (unitaryPSU hU 3) = ⊥ :=
    KFacts.center_unitaryPSU_three_eq_bot hU hq2
  have hdiv : 3 ∣ Nat.card (GaloisField 2 (2 * n)) - 1 := by
    rw [GaloisField.card 2 (2 * n) (by omega)]
    exact three_dvd_two_pow_sub_one_of_even_lin (even_two_mul n)
  refine noOmega_of_diag_fixed_lin hZ (psuConj hU).range
    (fun α hα => Sec19.Item19Res6Proof.mem_psuConj_range_of_isInnerAut hα)
    (fun B' hB' hE => Sec19.Item19Res6Proof.card_le_nine_of_le_psuConj_range hdiv B' hB'
      (fun x hx y hy => isElemAbelian_comm_lin hE hx hy) (fun x hx => hE.2 x hx))
    (fun σ _ hσ3 hσL => hK3 n (GaloisField 2 (2 * n)) hU hodd h9 h3 σ hσ3 hσL)

theorem not_isSimpleGroup_projSL_two_two_one :
    ¬ IsSimpleGroup (projSL 2 (GaloisField 2 1)) := by
  intro hS
  have h6 : Nat.card (projSL 2 (GaloisField 2 1)) = 6 := by
    rw [Sec8.Item812Res2.card_projSL_two (le_refl 1)]
    norm_num
  haveI : Finite (projSL 2 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  obtain ⟨P, hPn, hP3, -⟩ :=
    Quasithin.B1Red.exists_normal_card_three_of_card_six (Y := projSL 2 (GaloisField 2 1)) h6
  haveI := hPn
  rcases hS.eq_bot_or_eq_top_of_normal P with h | h
  · rw [h, Subgroup.card_bot] at hP3
    norm_num at hP3
  · rw [h, Subgroup.card_top, h6] at hP3
    norm_num at hP3

theorem not_isSimpleGroup_projSU_three_two_one : ¬ IsSimpleGroup (projSU 3 2 1) := by
  apply Quasithin.Background.Harris.OrdinaryProofs.not_isSimpleGroup_of_card_72
  have h := KFacts.KS14.card_projSU_three_mul_gcd 2 1 le_rfl
  norm_num at h
  omega

theorem autNoE27_or_noOmega_projSL_three_two (hK2 : GapL3Field) {n : ℕ} (hn : 1 ≤ n) :
    AutNoE27 (projSL 3 (GaloisField 2 n)) ∨ NoOmega (projSL 3 (GaloisField 2 n)) := by
  by_cases h3 : 3 ∣ n
  · right
    rcases Nat.even_or_odd n with heven | hodd
    · haveI : Finite (projectiveSL 3 (GaloisField 2 n)) :=
        Finite.of_equiv (projSL 3 (GaloisField 2 n))
          (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n)).toEquiv
      exact NoOmega.of_mulEquiv (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 n))
        (noOmega_projectiveSL_even_lin hK2 hn heven h3)
    · exact noOmega_projSL_odd_lin hn hodd
  · left
    exact autNoE27_of_card_le_nine (fun B hB =>
      Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (p := 2) (f := n) (by norm_num) hn h3 B hB)

theorem autNoE27_or_noOmega_projSU_three_two (hK3 : GapU3Field) {n : ℕ} (hn : 2 ≤ n)
    (hn3 : n ≠ 3) :
    AutNoE27 (projSU 3 2 n) ∨ NoOmega (projSU 3 2 n) := by
  have hn1 : 1 ≤ n := by omega
  have hq2 : 2 < 2 ^ n := two_lt_two_pow_lin hn
  by_cases h3 : 3 ∣ n
  · right
    have hU : UnitaryFieldData 2 n (GaloisField 2 (2 * n)) :=
      Sec4.unitaryFieldData_galoisField 2 n hn1
    rcases Nat.even_or_odd n with heven | hodd
    · exact NoOmega.of_mulEquiv (Sec4.projSUEquivUnitaryPSU 2 n hU)
        (noOmega_unitaryPSU_even_lin hn heven hU)
    · have h9 : 9 ≤ n := by
        obtain ⟨k, hk⟩ := h3
        obtain ⟨m, hm⟩ := hodd
        omega
      exact NoOmega.of_mulEquiv (Sec4.projSUEquivUnitaryPSU 2 n hU)
        (noOmega_unitaryPSU_odd_lin hn hodd h3 h9 hU hK3)
  · left
    exact autNoE27_of_card_le_nine (fun B hB =>
      Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (p := 2) (f := n) (by norm_num) hn1 hq2
        h3 B hB)

end Classical

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
