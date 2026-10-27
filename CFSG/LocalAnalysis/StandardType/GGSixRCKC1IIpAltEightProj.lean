module

public import CFSG.Open.StatedDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.StandardType.AlternatingEightCoverOrder
import CFSG.RankThree.GF2n.Stroth80.Sec7ArtinOrders
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LieType.SemisimpleCentralizers.HeldLangU64Ord
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltFin
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Open (StatedLieTag)

theorem rckIIp_eq_four_one_of_alt_eight_equiv_statedProjSL {K : Type} [Field K] [Finite K]
    {m q : ℕ} (hq : 1 ≤ q) (hK : Nat.card K = 2 ^ q)
    (e : alternatingGroup (Fin 8) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSL m K)) :
    m = 4 ∧ q = 1 := by
  classical
  have hcardProj : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL m K)) = 20160 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.card_alternatingGroup_fin_eight
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    ·
      have : Subsingleton (GL (Fin 0) K) :=
        ⟨fun a b => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩
      have : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 K)) :=
        inferInstance
      have hProj1 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 0 K)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      omega
    ·
      have : Subsingleton (CFSG.Open.StatedSL 1 K) := by
        constructor
        intro a b
        apply Subtype.ext
        apply Units.ext
        ext i j
        fin_cases i
        fin_cases j
        have ha : ((a : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
          have h := CFSG.Open.StatedAPI.det_of_mem_statedSL a.2
          rwa [Matrix.det_fin_one] at h
        have hb : ((b : GL (Fin 1) K) : Matrix (Fin 1) (Fin 1) K) 0 0 = 1 := by
          have h := CFSG.Open.StatedAPI.det_of_mem_statedSL b.2
          rwa [Matrix.det_fin_one] at h
        simpa using ha.trans hb.symm
      have : Subsingleton (CFSG.Open.StatedProj (CFSG.Open.StatedSL 1 K)) :=
        inferInstance
      have hProj1 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 1 K)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
      omega
  ·
    have hpad := CFSG.RankThree.GF2n.Stroth80.padicValNat_two_card_statedProj (K := K)
      (a := m) (f := q) hm hq hK
    have hval : padicValNat 2 20160 = 6 := by
      rw [show 20160 = 2 ^ 6 * 315 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]
    have hMul : q * (m * (m - 1) / 2) = 6 := hpad.symm.trans (by rw [hcardProj, hval])
    have hmle : m ≤ 4 := by
      have hle : m * (m - 1) / 2 ≤ 6 := by
        calc m * (m - 1) / 2 = 1 * (m * (m - 1) / 2) := (one_mul _).symm
          _ ≤ q * (m * (m - 1) / 2) := Nat.mul_le_mul_right _ hq
          _ = 6 := hMul
      by_contra h
      have h5 : 5 ≤ m := by omega
      have h4 : 4 ≤ m - 1 := by omega
      have h20 : 20 ≤ m * (m - 1) := by
        calc 20 = 5 * 4 := by norm_num
          _ ≤ m * (m - 1) := Nat.mul_le_mul h5 h4
      have h2 : m * (m - 1) = 2 * (m * (m - 1) / 2) :=
        (Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))).symm
      omega
    have hm2 : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases hm2 with rfl | rfl | rfl
    ·
      have hq6 : q = 6 := by
        norm_num at hMul
        omega
      subst hq6
      have hcard2 : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) = 262080 := by
        rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
          (by norm_num), hK]
        norm_num
      rw [hcardProj] at hcard2
      norm_num at hcard2
    ·
      have hq2 : q = 2 := by
        norm_num at hMul
        omega
      subst hq2
      have hF4 : Nat.card K = 4 := by rw [hK]; norm_num
      exfalso
      exact CFSG.HardMathSupport.Solomon.Coordinator.false_of_projectiveSL_alt_eight
        (F := K) hF4
        ((QuotientGroup.quotientMulEquivOfEq
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K)).trans
          ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).trans
            e.symm))
    ·
      have hq1 : q = 1 := by
        norm_num at hMul
        omega
      subst hq1
      exact ⟨rfl, rfl⟩

theorem rckIIp_false_of_alt_eight_equiv_statedProjSU {K : Type} [Field K] [Finite K]
    {m q : ℕ} (hq : 1 ≤ q) (hK : Nat.card K = (2 ^ q) ^ 2)
    (e : alternatingGroup (Fin 8) ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU m (2 ^ q) K)) :
    False := by
  classical
  let N : Subgroup (CFSG.Open.StatedSU m (2 ^ q) K) :=
    (CFSG.Open.StatedScalars (Fin m) K).subgroupOf (CFSG.Open.StatedSU m (2 ^ q) K)
  have hcardProj : Nat.card (CFSG.Open.StatedProj
      (CFSG.Open.StatedSU m (2 ^ q) K)) = 20160 := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.StandardType.card_alternatingGroup_fin_eight
  have hcardSU : Nat.card (CFSG.Open.StatedSU m (2 ^ q) K) =
      Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU m (2 ^ q) K)) * Nat.card N := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((CFSG.Open.StatedScalars (Fin m) K).subgroupOf (CFSG.Open.StatedSU m (2 ^ q) K))
    dsimp only [N]
    exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card K = 2 ^ (2 * q) := by
    rw [hK, ← pow_mul, Nat.mul_comm]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * q) (by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard)
  have h2N : ¬ 2 ∣ Nat.card N :=
    CFSG.Open.StatedAPI.not_dvd_card_statedScalars_subgroupOf
      (M := CFSG.Open.StatedSU m (2 ^ q) K) (d := Nat.card K - 1) (p := 2)
      Nat.prime_two (by
        rw [hKcard]
        exact CFSG.RankThree.GF2n.Stroth80.two_pow_sub_one_odd (by omega))
      (fun c _ => by rw [← Nat.card_units]; exact pow_card_eq_one')
  have hvalSU : padicValNat 2 (Nat.card (CFSG.Open.StatedSU m (2 ^ q) K)) = 6 := by
    have h20160 : padicValNat 2 20160 = 6 := by
      rw [show 20160 = 2 ^ 6 * 315 by norm_num,
        padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd (by norm_num), add_zero]
    have hNpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
    rw [hcardSU, hcardProj, padicValNat.mul (by norm_num) hNpos, h20160,
      padicValNat.eq_zero_of_not_dvd h2N, add_zero]
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Subsingleton (GL (Fin 0) K) :=
      ⟨fun a b => Units.ext (Matrix.ext fun i => Fin.elim0 i)⟩
    have hSU1 : Nat.card (CFSG.Open.StatedSU 0 (2 ^ q) K) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
    rw [hSU1] at hvalSU
    norm_num at hvalSU
  have hm : 1 ≤ m := by omega
  have hpad := CFSG.LieType.SemisimpleCentralizers.HeldLang.padicValNat_card_statedSU
    (K := K) (a := q) (d := m) hq hm hK
  have hMul : q * (m * (m - 1) / 2) = 6 := hpad.symm.trans hvalSU
  have hm1 : m ≠ 1 := by
    rintro rfl
    norm_num at hMul
  have hmle : m ≤ 4 := by
    have hle : m * (m - 1) / 2 ≤ 6 := by
      calc m * (m - 1) / 2 = 1 * (m * (m - 1) / 2) := (one_mul _).symm
        _ ≤ q * (m * (m - 1) / 2) := Nat.mul_le_mul_right _ hq
        _ = 6 := hMul
    by_contra h
    have h5 : 5 ≤ m := by omega
    have h4 : 4 ≤ m - 1 := by omega
    have h20 : 20 ≤ m * (m - 1) := by
      calc 20 = 5 * 4 := by norm_num
        _ ≤ m * (m - 1) := Nat.mul_le_mul h5 h4
    have h2 : m * (m - 1) = 2 * (m * (m - 1) / 2) :=
      (Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self m))).symm
    omega
  have hm2 : m = 2 ∨ m = 3 ∨ m = 4 := by omega
  have h7 : 7 ∣ Nat.card (CFSG.Open.StatedSU m (2 ^ q) K) := by
    rw [hcardSU, hcardProj]
    exact dvd_mul_of_dvd_left (by norm_num : 7 ∣ 20160) _
  rcases hm2 with rfl | rfl | rfl
  ·
    have hq6 : q = 6 := by
      norm_num at hMul
      omega
    subst hq6
    let π : CFSG.Open.StatedSU 2 (2 ^ 6) K →* alternatingGroup (Fin 8) :=
      e.symm.toMonoidHom.comp (QuotientGroup.mk' N)
    have hπsurj : Function.Surjective π :=
      e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
    have hrange : π.range = ⊤ := MonoidHom.range_eq_top.mpr hπsurj
    have hZ : Subgroup.center ↥π.range = ⊥ := by
      rw [hrange]
      have hmap := Subgroup.map_center_eq
        (Subgroup.topEquiv (G := alternatingGroup (Fin 8)))
      rw [alternatingGroup.center_eq_bot (by norm_num)] at hmap
      exact (Subgroup.map_eq_bot_iff_of_injective _
        (Subgroup.topEquiv (G := alternatingGroup (Fin 8))).injective).mp hmap
    have hA8 : Nonempty ((↥π.range ⧸ Subgroup.center ↥π.range) ≃*
        alternatingGroup (Fin 8)) := by
      refine ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans
        (QuotientGroup.quotientBot.trans ?_)⟩
      rw [hrange]
      exact Subgroup.topEquiv
    exact rckIIp_false_of_alt_eight_of_GL_two
      (G := CFSG.Open.StatedSU 2 (2 ^ 6) K) (X := alternatingGroup (Fin 8))
      (F := K) (ι := Fin 2) (by norm_num)
      (Subgroup.subtype (CFSG.Open.StatedSU 2 (2 ^ 6) K))
      (Subgroup.subtype_injective _) π hA8
  ·
    have hq2 : q = 2 := by
      norm_num at hMul
      omega
    subst hq2
    have hcard3 : Nat.card (CFSG.Open.StatedSU 3 (2 ^ 2) K) = 62400 := by
      rw [CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 2) hK]
      norm_num
    rw [hcard3] at h7
    norm_num at h7
  ·
    have hq1 : q = 1 := by
      norm_num at hMul
      omega
    subst hq1
    have hUFD : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K := by
      refine ⟨Nat.prime_two, le_rfl, ?_⟩
      rw [hK]
      norm_num
    have hcard4 : Nat.card (CFSG.Open.StatedSU 4 (2 ^ 1) K) = 25920 := by
      have h := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hUFD (n := 4)
        (by norm_num)
      rw [Finset.prod_Icc_succ_top (a := 2) (b := 3) (by norm_num),
        Finset.prod_Icc_succ_top (a := 2) (b := 2) (by norm_num)] at h
      simp only [Finset.Icc_self, Finset.prod_singleton] at h
      norm_num at h
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast h
    rw [hcard4] at h7
    norm_num at h7

theorem rckIIp_false_of_alt_eight_statedClassicalModel {G : Type} [Group G] {t : StatedLieTag}
    {m f : ℕ} (ht : t = .PSL ∨ t = .PSU) (hf : 2 ≤ f)
    (h : CFSG.Open.StatedClassicalModel G t m 2 f)
    (hA8 : Nonempty (G ≃* alternatingGroup (Fin 8))) : False := by
  obtain ⟨eA⟩ := hA8
  rcases ht with rfl | rfl
  · rw [CFSG.Open.StatedClassicalModel] at h
    obtain ⟨-, K, hfield, hfin, hcard, ⟨e'⟩⟩ := h
    have e : alternatingGroup (Fin 8) ≃* CFSG.Open.StatedProj
        (CFSG.Open.StatedSL m K) := eA.symm.trans e'
    exact absurd (rckIIp_eq_four_one_of_alt_eight_equiv_statedProjSL
      (q := f) (by omega) hcard e).2 (by omega)
  · rw [CFSG.Open.StatedClassicalModel] at h
    obtain ⟨-, K, hfield, hfin, hcard, ⟨e'⟩⟩ := h
    have e : alternatingGroup (Fin 8) ≃* CFSG.Open.StatedProj
        (CFSG.Open.StatedSU m (2 ^ f) K) := eA.symm.trans e'
    exact rckIIp_false_of_alt_eight_equiv_statedProjSU
      (q := f) (by omega) hcard e

end CFSG.StandardType.RCKC1
