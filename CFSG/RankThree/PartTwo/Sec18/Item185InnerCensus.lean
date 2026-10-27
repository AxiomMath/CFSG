module

public import CFSG.RankThree.PartTwo.Sec18.Item185InnerBase
public import CFSG.RankThree.PartTwo.Sec19.SimsC198Cases
public import CFSG.RankThree.PartTwo.Sec19.SimsC198RankOdd
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
public import CFSG.RankThree.PartTwo.Sec19.SimsC198RankSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowSpor
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowAlt
import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.RankThree.PartTwo.Sec10.Item1015Proof

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late (IsE27)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.RankThree.PartTwo.Sec19.SimsC198 (RankHyp Alt42One Alt42Two Alt42Three Alt42Four
  Alt42Five Alt42Six Alt42Nine)
open CFSG.RankThree.PartTwo.Sec4.RonanK429 (NoE27 AutNoE27)

section Rank

theorem noE27_projSL_two_of_ne_three {p e : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) :
    NoE27 (projSL 2 (GaloisField p e)) := by
  intro D hD
  have h3 : ((3 : ℕ) : GaloisField p e) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (GaloisField p e) p] at h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h)
  have hle := CFSG.RankThree.PartOne.LIT.pRank_projSL_two_le Nat.prime_three (by norm_num) h3
  have hD3 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : D ≤ ⊤) hD.1
    (k := 3) (by rw [hD.2]; norm_num)
  omega

theorem noE27_projSL_two_three_of_le_two {e : ℕ} (he1 : 1 ≤ e) (he2 : e ≤ 2) :
    NoE27 (projSL 2 (GaloisField 3 e)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sec4.RonanK429.noE27_of_not_dvd ?_
  have hφ : Nat.card (projSL 2 (GaloisField 3 e)) =
      Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSL 2 (GaloisField 3 e))) :=
    (Nat.card_congr ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 2 _))
        |>.toEquiv)).symm
  rw [hφ, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num),
    GaloisField.card 3 e (by omega)]
  obtain rfl | rfl : e = 1 ∨ e = 2 := by omega
  · norm_num
  · norm_num

theorem four_le_pRank_projSL_two_three {e : ℕ} (he : 4 ≤ e) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projSL 2 (GaloisField 3 e))) := by
  have h := Sec6.Res611Res3.le_pRank_projSL_two (n := e) (by omega)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem noE27_projSL_three_three : NoE27 (projSL 3 (GaloisField 3 1)) := by
  intro D hD
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 (by norm_num)]
    norm_num
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (projSL 3 (GaloisField 3 1))) ≤ 2 := by
    let φ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 3 1) ≃*
        projSL 3 (GaloisField 3 1) :=
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3
          (GaloisField 3 1)).trans
        ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
          (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 _)))
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) φ]
    have h1 : CFSG.Open.pRank 3
        (⊤ : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 3 1))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 3 1))) :=
      CFSG.SectionRank.pRank_quotient_eq _ (by
        rw [CFSG.RankThree.PartTwo.Census.center_SL_three_card_eq_one hK]
        norm_num)
    rw [h1]
    exact CFSG.RankThree.PartTwo.Census.pRank_three_SL_three_le hK
  have hD3 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : D ≤ ⊤) hD.1
    (k := 3) (by rw [hD.2]; norm_num)
  omega

theorem noE27_projSU_three_three : NoE27 (projSU 3 3 1) := by
  intro D hD
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.pRank_three_le_of_mulEquiv_projSU
    (MulEquiv.refl (projSU 3 3 1))
  have hD3 := CFSG.SectionRank.le_pRank (by norm_num) (le_top : D ≤ ⊤) hD.1
    (k := 3) (by rw [hD.2]; norm_num)
  omega

end Rank

section Cases


theorem innerCase_one (hL227 : NormIrred (projSL 2 (GaloisField 3 3))) : InnerCase Alt42One := by
  intro X _ _ hX A B c hd hP
  obtain ⟨p, e, hp, hp2, he, ⟨φ⟩⟩ := hP
  by_cases hp3 : p = 3
  · subst hp3
    by_cases he2 : e ≤ 2
    · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_projSL_two_three_of_le_two he he2))
        _ _ _ (hd.quotient hX)
    · by_cases he3 : e = 3
      · subst he3
        exact (NormIrred.of_mulEquiv φ hL227).noInnerData _ _ _ (hd.quotient hX)
      · exact false_of_four_le_pRank hX (hd.three_not_dvd_card_center hX) φ
          (four_le_pRank_projSL_two_three (by omega))
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_projSL_two_of_ne_three hp3))
      _ _ _ (hd.quotient hX)

theorem innerCase_two : InnerCase Alt42Two := InnerCase.of_autNoE27 fun S _ _ hP => by
  obtain ⟨p, e, hp, hp3, he1, he2, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hP
  all_goals have h3e : ¬ 3 ∣ e := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  · exact autNoE27_of_mulEquiv φ (autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSL (Nat.ne_of_gt hp3) he1 h3e))
  · exact autNoE27_of_mulEquiv φ (autNoE27_of_card_le_nine
      (Sec10.Item1015Proof.card_le_nine_of_mulAut_projSU (Nat.ne_of_gt hp3) he1
        (lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega : e ≠ 0) p)) h3e))

theorem innerCase_three : InnerCase Alt42Three :=
  InnerCase.of_rankHyp fun X _ _ hX hP => by
    obtain ⟨hr, ⟨φ⟩⟩ := hP
    exact Sec19.SimsC198.false_of_rankHyp_ree27 hX hr φ

theorem innerCase_four : InnerCase Alt42Four :=
  InnerCase.of_rankHyp fun X _ _ hX hP => by
    obtain ⟨p, hp, hp3, ⟨q, hq, hq1, hG⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hP
    · exact Sec19.SimsC198.false_of_rankHyp_G2_large hX (by omega) hq1 hG
    · exact Sec19.SimsC198.false_of_rankHyp_PSp4 hX hp3 φ
    · exact Sec19.SimsC198.false_of_rankHyp_PSL4 hX hp3 φ
    · exact Sec19.SimsC198.false_of_rankHyp_PSU4 hX hp3 φ

theorem innerCase_nine : InnerCase Alt42Nine := by
  intro X _ _ hX A B c hd hP
  rcases hP with ⟨e, he1, he3, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · by_cases he : e = 1
    · subst he
      exact noInnerData_of_noE27 (noE27_of_mulEquiv φ noE27_projSL_three_three) _ _ _
        (hd.quotient hX)
    · exact Sec19.SimsC198.false_of_rankHyp_PSL3_three hX (by omega) φ
  · by_cases he : e = 1
    · subst he
      exact noInnerData_of_noE27 (noE27_of_mulEquiv φ noE27_projSU_three_three) _ _ _
        (hd.quotient hX)
    · exact Sec19.SimsC198.false_of_rankHyp_PSU3_three hX (by omega) φ
  · exact Sec19.SimsC198.false_of_rankHyp_G2_three hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSL4_three hX φ
  · exact Sec19.SimsC198.false_of_rankHyp_PSU4_three hX φ

end Cases

theorem noE27_alternatingGroup_of_le_eight {n : ℕ} (h5 : 5 ≤ n) (h8 : n ≤ 8) :
    NoE27 (alternatingGroup (Fin n)) :=
  Sec4.RonanK429.noE27_of_not_dvd (Sec4.RonanK429.not_dvd_card_alternatingGroup_le_eight h5 h8)

section AltE81

open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm

private def e81Perm (v : Fin 4 → ZMod 3) : Equiv.Perm (Fin 12) :=
  vecPerm 12 ![v 0, v 1, v 2] * dd 12 ^ (v 3).val

private theorem dd_pow_val_add (x y : ZMod 3) :
    dd 12 ^ (x + y).val = dd 12 ^ x.val * dd 12 ^ y.val := by
  revert x y
  decide +kernel

private theorem commute_dd_vecPerm (w : Fin 3 → ZMod 3) : Commute (dd 12) (vecPerm 12 w) := by
  have hc1 : Commute (dd 12) (c1 12) := w12Facts.dd_c1
  have hc2 : Commute (dd 12) (c2 12) := w12Facts.dd_c2
  have hc3 : Commute (dd 12) (c3 12) := w12Facts.dd_c3
  unfold vecPerm
  exact ((hc1.pow_right _).mul_right (hc2.pow_right _)).mul_right (hc3.pow_right _)

private theorem mul_mul_mul_comm_aux {G : Type*} [Group G] (A B a b : G)
    (h : B * a = a * B) : A * B * (a * b) = A * a * (B * b) := by
  calc A * B * (a * b) = A * (B * a) * b := by group
    _ = A * (a * B) * b := by rw [h]
    _ = A * a * (B * b) := by group

private theorem e81Perm_add (v w : Fin 4 → ZMod 3) :
    e81Perm (v + w) = e81Perm v * e81Perm w := by
  have hv : ![(v + w) 0, (v + w) 1, (v + w) 2] = ![v 0, v 1, v 2] + ![w 0, w 1, w 2] := by
    ext i
    fin_cases i <;> rfl
  have hc : Commute (dd 12 ^ (v 3).val) (vecPerm 12 ![w 0, w 1, w 2]) :=
    (commute_dd_vecPerm _).pow_left _
  unfold e81Perm
  rw [hv, (w12Facts.w.toA0Facts).add, Pi.add_apply, dd_pow_val_add]
  exact mul_mul_mul_comm_aux _ _ _ _ hc.symm.eq

private theorem sign_e81Perm (v : Fin 4 → ZMod 3) : Equiv.Perm.sign (e81Perm v) = 1 := by
  have h1 : Equiv.Perm.sign (c1 12) = 1 := by decide +kernel
  have h2 : Equiv.Perm.sign (c2 12) = 1 := by decide +kernel
  have h3 : Equiv.Perm.sign (c3 12) = 1 := by decide +kernel
  have h4 : Equiv.Perm.sign (dd 12) = 1 := by decide +kernel
  unfold e81Perm vecPerm
  simp [map_mul, map_pow, h1, h2, h3, h4]

private theorem e81Perm_inj : ∀ v : Fin 4 → ZMod 3, e81Perm v = 1 → v = 0 := by
  decide +kernel

private def e81Hom : Multiplicative (Fin 4 → ZMod 3) →* alternatingGroup (Fin 12) where
  toFun v :=
    ⟨e81Perm (Multiplicative.toAdd v), Equiv.Perm.mem_alternatingGroup.mpr (sign_e81Perm _)⟩
  map_one' := Subtype.ext (by simp [e81Perm, vecPerm])
  map_mul' u w := Subtype.ext (by
    show e81Perm (Multiplicative.toAdd (u * w)) =
      e81Perm (Multiplicative.toAdd u) * e81Perm (Multiplicative.toAdd w)
    rw [toAdd_mul]
    exact e81Perm_add _ _)

private theorem e81Hom_injective : Function.Injective e81Hom := by
  rw [injective_iff_map_eq_one]
  intro v hv
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  exact e81Perm_inj _ (congrArg Subtype.val hv)

theorem four_le_pRank_alternatingGroup_twelve :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 12))) :=
  CFSG.SectionRank.le_pRank (by norm_num) (le_top : e81Hom.range ≤ ⊤)
    (isElemAbelian_range e81Hom) (card_range_of_injective e81Hom e81Hom_injective)

end AltE81

theorem innerCase_five (h9 : NormIrred (alternatingGroup (Fin 9)))
    (h10 : NormIrred (alternatingGroup (Fin 10))) (h11 : NormIrred (alternatingGroup (Fin 11))) :
    InnerCase Alt42Five := by
  intro X _ _ hX A B c hd hP
  obtain ⟨n, h5, h12, ⟨φ⟩⟩ := hP
  have hq := hd.quotient hX
  by_cases h8 : n ≤ 8
  · exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (noE27_alternatingGroup_of_le_eight h5 h8))
      _ _ _ hq
  · have h9' : 9 ≤ n := by omega
    interval_cases n
    · exact (NormIrred.of_mulEquiv φ h9).noInnerData _ _ _ hq
    · exact (NormIrred.of_mulEquiv φ h10).noInnerData _ _ _ hq
    · exact (NormIrred.of_mulEquiv φ h11).noInnerData _ _ _ hq
    · exact false_of_four_le_pRank hX (hd.three_not_dvd_card_center hX) φ
        four_le_pRank_alternatingGroup_twelve

section Spor


theorem four_le_pRank_mcl [Finite (Sec4.Spor .McL)] : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Sec4.Spor .McL)) := by
  have h := Sec4.Census.SporadicTwoCover.three_lt_pRank_mcl
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

theorem four_le_pRank_onan [Finite (Sec4.Spor .ONan)] : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Sec4.Spor .ONan)) := by
  have h := Sec4.Census.SporadicTwoCover.three_lt_pRank_onan
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  omega

open RankThree.PartTwo.Sec4.RonanK429 in
theorem innerCase_six (hJ3 : NoInnerData (Sec4.Spor .J3)) : InnerCase Alt42Six := by
  intro X _ _ hX A B c hd hP
  obtain ⟨s, hs, ⟨φ⟩⟩ := hP
  have hq := hd.quotient hX
  haveI : Finite (Sec4.Spor s) := Finite.of_equiv _ φ.toEquiv
  simp only [Sec4.sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_m11).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_m12).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_m22).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_m23).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_m24).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_j1).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_j2).2) _ _ _ hq
  ·
    exact NoInnerData.of_mulEquiv φ hJ3 _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_j4).2) _ _ _ hq
  ·
    exact false_of_four_le_pRank hX (hd.three_not_dvd_card_center hX) φ four_le_pRank_mcl
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_hs).2) _ _ _ hq
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_he).2) _ _ _ hq
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  ·
    exact noInnerData_of_noE27 (noE27_of_mulEquiv φ (spor_ru).2) _ _ _ hq
  ·
    exact false_of_four_le_pRank hX (hd.three_not_dvd_card_center hX) φ four_le_pRank_onan
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ
  ·
    exact Sec19.SimsC198.false_of_rankHyp_spor hX (by simp) φ

end Spor

end CFSG.RankThree.PartTwo.Sec18.Item185Proof
