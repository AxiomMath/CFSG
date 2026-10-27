module

public import CFSG.RankThree.PartTwo.Sec4.Item426A6Models
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
public import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.RankThree.PartTwo.Sec4.Item426A6FieldSU
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
import CFSG.RankThree.PartTwo.KFacts.K412TripleCover
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.J3
import CFSG.Sporadic.McL.Simple
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec4.Item426A6
public import CFSG.RankThree.PartTwo.Sec4.Item426A6Inner

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem center_eq_bot_of_isSimpleGroup {Y : Type*} [Group Y] [IsSimpleGroup Y]
    (hY : ¬ (Nat.card Y).Prime) : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Y :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hY (Group.is_simple_iff_prime_card.mp inferInstance)

theorem center_J3_McL_ON :
    Subgroup.center Blueprint.NativeSporadic.J3 = ⊥ ∧
      Subgroup.center Blueprint.NativeSporadic.McL = ⊥ ∧
      Subgroup.center Blueprint.NativeSporadic.ON = ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · have := CFSG.Sporadic.J3.fam_j3_simplicity.2.2
    exact center_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.J3.card_J3]; norm_num)
  · have := CFSG.Sporadic.McL.fam_mcl_simplicity.2.2
    exact center_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.McL.card_McL]; norm_num)
  · have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
    exact center_eq_bot_of_isSimpleGroup (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)

theorem card_M22 : Nat.card Blueprint.NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem not_five_dvd_card_of_G2_three
    {S : Type} [Group S]
    (hS : Blueprint.ChevalleyExceptionalModel S .G2 3 1) : ¬ 5 ∣ Nat.card S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  intro h5
  have h5' : 5 ∣ Nat.card (Blueprint.Chevalley.adjointGroup .G2 K) := by
    have h1 : Nat.card S = Nat.card (Blueprint.AdjointQuotient .G2 K) := Nat.card_congr e.toEquiv
    have h2 : Nat.card (Blueprint.AdjointQuotient .G2 K) ∣
        Nat.card (Blueprint.Chevalley.adjointGroup .G2 K) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (Blueprint.Chevalley.adjointGroup .G2 K))]
      exact Dvd.intro _ rfl
    exact (h1 ▸ h5).trans h2
  rw [(CFSG.LieType.Chevalley.exact_G2_finite_order K hK).2.1] at h5'
  norm_num at h5'

namespace Config426

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem card_quotient_center_dvd_of_isExtOf (h : Config426 X α P) {S : Type*} [Group S]
    (hext : IsExtOf X S (Multiplicative (ZMod 3))) :
    Nat.card (X ⧸ Subgroup.center X) ∣ Nat.card S := by
  obtain ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ := hext
  have hNZ : N ≤ Subgroup.center X := le_center_of_normal_mulEquiv_zmod3 h.quasisimple hN eN
  rw [← Nat.card_congr eQ.toEquiv]
  exact card_quotient_center_dvd hNZ

theorem false_of_inner_eps (h : Config426 X α P) {y : X} (hα : α = MulAut.conj y)
    (hy : y ∉ Subgroup.center X) {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hSL : IsSLThreeEpsAt X (p ^ e)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hK⟩ := hSL
  have := Fintype.ofFinite K
  rcases hK with ⟨hKc, ⟨eK⟩⟩ | ⟨hKc, ⟨eK⟩⟩
  · have : CharP K p := charP_of_card_eq_prime_pow (f := e)
      (by rw [← Nat.card_eq_fintype_card, hKc])
    exact h.false_of_inner_matrix hα hy (three_ne_zero_of_charP hp hp3) eK
  · have : CharP K p := charP_of_card_eq_prime_pow (f := 2 * e)
      (by rw [← Nat.card_eq_fintype_card, hKc, ← pow_mul, mul_comm])
    exact h.false_of_inner_matrix hα hy (three_ne_zero_of_charP hp hp3) eK

theorem isTripleCover_ON_of_inner
    (hMcL : K426.McLThreeCentralizer) (hJ3 : K426.J3CoverCentralizer) (h : Config426 X α P)
    (hlist : IsList46 X) {y : X}
    (hα : α = MulAut.conj y) (hy : y ∉ Subgroup.center X) :
    IsTripleCover X Blueprint.NativeSporadic.ON := by
  have h27 := h.twentySeven_dvd_of_inner hα hy
  have hnot27 : ∀ {S : Type} [Group S], IsExtOf X S (Multiplicative (ZMod 3)) →
      ¬ 27 ∣ Nat.card S → False :=
    fun hext hS => hS (h27.trans (h.card_quotient_center_dvd_of_isExtOf hext))
  obtain ⟨hZJ3, hZMcL, hZON⟩ := center_J3_McL_ON
  rcases hlist with ⟨p, e, _, -, -, ⟨e1⟩⟩ |
      ⟨p, e, _, hp3, he1, -, hSL | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨p, _, hp3, hG2 | ⟨⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩⟩ |
      (⟨n, -, ⟨e1⟩⟩ | hA6 | hA7) | (⟨s, hs, ⟨e1⟩⟩ | ⟨s, hs, hext⟩) |
      (hchev | ⟨n, -, hSL⟩) | (⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩) |
      ((⟨e, he1, -, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩) | ⟨⟨e1⟩⟩ | ⟨hZ3, hG23 | hU43'⟩)
  ·
    exact (h.false_of_projSL e1).elim
  ·
    exact (h.false_of_inner_eps hα hy Fact.out (by omega) hSL).elim
  · exact (h.false_of_projSL e1).elim
  · exact (h.false_of_projSU le_rfl he1 e1).elim
  ·
    exact (h.false_of_chevalleyExceptional (Or.inl rfl) hG2).elim
  · refine (h.false_of_projSp (by norm_num) (Or.inl (Or.inr ?_)) e1).elim
    rw [GaloisField.card p 1 one_ne_zero, pow_one]
    omega
  · exact (h.false_of_projSU (by norm_num) le_rfl e1).elim
  · exact (h.false_of_projSL e1).elim
  ·
    exact (h.false_of_alternating e1).elim
  · exact (hnot27 hA6 (by rw [KFacts.K412.card_alternating_six_seven.1]; norm_num)).elim
  · exact (hnot27 hA7 (by rw [KFacts.K412.card_alternating_six_seven.2]; norm_num)).elim
  ·
    exact (h.false_of_sporadic46 hs e1).elim
  · simp only [sporadicCovers46, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    ·
      refine (hnot27 hext ?_).elim
      change ¬ 27 ∣ Nat.card Blueprint.NativeSporadic.M22
      rw [card_M22]
      norm_num
    ·
      exfalso
      obtain ⟨h3, ⟨eJ⟩⟩ := (isTripleCover_iff_isExtOf h.quasisimple hZJ3).mpr hext
      have hPC : P ≤ Subgroup.centralizer {y} := fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (h.commute_of_eq_conj hα hx).symm
      have hbot := hJ3 X h.quasisimple h3 ⟨eJ⟩ y hy (h.pow_three_mem_center hα) P hPC
        h.isPerfect
      obtain ⟨a, ha, b, hb, hcZ, hc1, -⟩ := h.comm
      have hcP : a * b * a⁻¹ * b⁻¹ ∈ P :=
        mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
      have hmem : a * b * a⁻¹ * b⁻¹ ∈ P ⊓ Subgroup.center X := ⟨hcP, hcZ⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hc1 hmem
    ·
      exfalso
      obtain ⟨-, ⟨eM⟩⟩ := (isTripleCover_iff_isExtOf h.quasisimple hZMcL).mpr hext
      exact h.false_of_inner_of_section hα hy eM hMcL
    ·
      exact (isTripleCover_iff_isExtOf h.quasisimple hZON).mpr hext
  ·
    exfalso
    rcases hchev with ⟨n, hn, ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩⟩ |
      ⟨f, hG2 | hD4 | hSz | hF4 | hTits⟩
    · exact h.false_of_projSL e1
    · exact h.false_of_projSL e1
    · exact h.false_of_projSU le_rfl hn e1
    · exact h.false_of_projSp_two hn e1
    · exact h.false_of_projSU (by norm_num) hn e1
    · exact h.false_of_chevalleyExceptional (Or.inl rfl) hG2
    · exact h.false_of_chevalleyExceptional (Or.inr rfl) hD4
    · exact h.false_of_suzuki hSz
    · exact h.false_of_reeTits (Or.inl rfl) hF4
    · exact h.false_of_reeTits (Or.inr rfl) hTits
  ·
    exact (h.false_of_inner_eps hα hy Nat.prime_two (by norm_num) hSL).elim
  ·
    exact (h.false_of_projSL e1).elim
  · exact (h.false_of_projSp (by norm_num)
      (Or.inr (Or.inr ⟨GaloisField.card 2 1 one_ne_zero, le_rfl⟩)) e1).elim
  · exact (h.false_of_projSU (by norm_num) (by norm_num) e1).elim
  ·
    exact (h.false_of_projSL e1).elim
  · exact (h.false_of_projSU le_rfl he1 e1).elim
  · exact (h.false_of_projSL e1).elim
  ·
    exfalso
    have hZ3' : Nat.card (Subgroup.center X) = 3 := by
      have h3 := h.three_dvd_card_center
      obtain ⟨k, hk⟩ := h3
      have hpos : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
      omega
    apply h.false_of_not_five_dvd
    intro h5
    have hXcard : Nat.card X = Nat.card (X ⧸ Subgroup.center X) * 3 := by
      rw [← hZ3']
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hXcard] at h5
    have h5' : 5 ∣ Nat.card (X ⧸ Subgroup.center X) :=
      ((Nat.Prime.dvd_mul Nat.prime_five).mp h5).resolve_right (by norm_num)
    exact not_five_dvd_card_of_G2_three hG23 h5'
  ·
    exfalso
    obtain ⟨eU⟩ := hU43'
    refine h.false_of_inner_of_section hα hy eU fun x hx H hH f hf => ?_
    have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 :=
      KFacts.K412.card_alternating_six_seven.1
    have hHc : Nat.card H = 360 * Nat.card f.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv, hA6]
    have h5 : 5 ∣ Nat.card H := by
      rw [hHc]
      exact ⟨72 * Nat.card f.ker, by ring⟩
    exact u43ThreeCentralizer x hx (h5.trans (Subgroup.card_dvd_of_le hH))

theorem false_of_outer_eps (h : Config426 X α P) (hout : ¬ IsInnerAut α)
    {p e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (he : 1 ≤ e) {K : Type} [Field K] [Finite K]
    (hK : (Nat.card K = p ^ e ∧ Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ∨
      (Nat.card K = (p ^ e) ^ 2 ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ e) K))) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  rcases hK with ⟨hKc, ⟨eK⟩⟩ | ⟨hKc, ⟨eK⟩⟩
  · have : CharP K p := charP_of_card_eq_prime_pow (f := e)
      (by rw [← Nat.card_eq_fintype_card, hKc])
    exact h.false_of_outer_SL slThreeFieldComponent hout (three_ne_zero_of_charP hp hp3)
      (eK.trans (statedSLEquiv 3 K))
  · have hU : UnitaryFieldData p e K := ⟨hp, he, by rw [hKc, ← pow_mul, mul_comm]⟩
    by_cases hq : 2 < p ^ e
    · exact h.false_of_outer_SU suThreeFieldComponent hout hU hq hp3 eK
    ·
      have h2 : p ^ e = 2 ^ 1 := by
        have hp2 := hp.two_le
        have : p ≤ p ^ e := Nat.le_self_pow (by omega) p
        have hpe : p ^ e = 2 := by omega
        rw [hpe, pow_one]
      rw [h2] at hKc eK
      exact false_of_mulEquiv_statedSU_three_two h.quasisimple hKc eK

end Config426

theorem false_of_alt47W
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (h : Config426 (L ⧸ aschbacherSolvableCore 3 L) (thetaAut L hcN) P)
    (hout : ¬ IsInnerAut (thetaAut L hcN)) (halt : Alt47W L c) : False := by
  rcases halt with ⟨p, e, _, -, -, ⟨e1⟩, -⟩ |
      ⟨p, e, _, hp3, he1, -, ⟨K, _, _, hSL⟩ | hIso, -⟩ |
      ⟨(⟨m, hm, ⟨⟨e1⟩⟩ | ⟨K, _, _, hKc, hSU⟩ | ⟨⟨e1⟩⟩ | ⟨K, _, _, hKc, hSL'⟩⟩ |
        ⟨n, hn, hSz | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | hG2 | hF4⟩), -⟩ |
      ⟨n, hn, ⟨K, _, _, hSL⟩ | hIso, -⟩ | ⟨n, -, hD4⟩
  ·
    exact h.false_of_projSL e1
  ·
    have hp : p.Prime := Fact.out
    rcases hSL with ⟨hKc, -, hK⟩ | ⟨hKc, -, hK⟩
    · exact h.false_of_outer_eps hout hp (by omega) he1 (Or.inl ⟨hKc, hK⟩)
    · exact h.false_of_outer_eps hout hp (by omega) he1 (Or.inr ⟨hKc, hK⟩)
  ·
    rcases hIso with ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩
    · exact h.false_of_projSL e1
    · exact h.false_of_projSU le_rfl he1 e1
  ·
    exact h.false_of_projSL e1
  ·
    exact h.false_of_outer_eps hout Nat.prime_two (by norm_num) hm (Or.inr ⟨hKc, hSU⟩)
  ·
    exact h.false_of_projSU le_rfl hm e1
  ·
    exact h.false_of_outer_eps hout Nat.prime_two (by norm_num) (e := 2 * m)
      (by omega) (Or.inl ⟨hKc, hSL'⟩)
  ·
    exact h.false_of_suzuki hSz
  ·
    exact h.false_of_projSL e1
  ·
    exact h.false_of_projSp_two hn.pos e1
  ·
    exact h.false_of_chevalleyExceptional (Or.inl rfl) hG2
  ·
    exact h.false_of_reeTits (Or.inl rfl) hF4
  ·
    rcases hSL with ⟨hKc, -, hK⟩ | ⟨hKc, -, hK⟩
    · exact h.false_of_outer_eps hout Nat.prime_two (by norm_num) hn
        (Or.inl ⟨hKc, hK⟩)
    · exact h.false_of_outer_eps hout Nat.prime_two (by norm_num) hn
        (Or.inr ⟨hKc, hK⟩)
  ·
    rcases hIso with ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩
    · exact h.false_of_projSL e1
    · exact h.false_of_projSU le_rfl hn e1
  ·
    exact h.false_of_chevalleyExceptional (Or.inr rfl) hD4

theorem rank3II_4_26_A6_of
    (h46 : Item4_6) (h47 : Item4_7W) (hMcL : K426.McLThreeCentralizer)
    (hJ3 : K426.J3CoverCentralizer) : Item4_26ThetaA6 := by
  intro G _ _ hG L hL c hc K hK hA6 hZne hZc
  obtain ⟨h3G, hKL, hcN, hcfg⟩ := config426_of hL hc hK hA6 hZne hZc
  by_cases hout : InducesOuterTheta c L
  · exfalso
    obtain ⟨hx, hni⟩ := id hout
    exact false_of_alt47W hcN hcfg hni (h47 G hG h3G L hL c hc hout)
  · have hin : IsInnerAut (thetaAut L hcN) := by
      by_contra hni
      exact hout ⟨hcN, hni⟩
    obtain ⟨y, hy⟩ := hin
    by_cases hyZ : y ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
    · left
      apply eq_sup_of_map_eq_top L hKL
      apply hcfg.eq_top_of_eq_one
      rw [← hy]
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hyZ x).symm,
        mul_inv_cancel_right]
    · right
      right
      exact ⟨hcfg.isTripleCover_ON_of_inner hMcL hJ3 (h46 G hG h3G L hL) hy.symm hyZ, hA6⟩

end CFSG.RankThree.PartTwo.Sec4.Item426
