module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1Sp4
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.GH74.GLS.IVK (fixedField fixedField_card_pow)
open Matrix

namespace L3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_one_of_commute_mulEquiv (hK : Nat.card K % 3 = 2) {S' : Type} [Group S']
    (e : S' ≃* SpecialLinearGroup (Fin 3) K) {y c : S'} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hyc : y * c = c * y) (hc2 : c ^ 2 = 1) : c = 1 := by
  have h := RonanKChevTwo.sl_three_eq_one_of_commute hK (x := e y) (c := e c)
    (by rw [← map_pow, hy3, map_one]) (by rw [Ne, map_eq_one_iff e e.injective]; exact hy1)
    (by rw [← map_mul, ← map_mul, hyc]) (by rw [← map_pow, hc2, map_one])
  exact (map_eq_one_iff e e.injective).mp h

theorem false_of_quasisimple_le (hK : Nat.card K % 3 = 2) {S' : Type} [Group S'] [Finite S']
    (e : S' ≃* SpecialLinearGroup (Fin 3) K) {y : S'} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (Q : Subgroup S') (hQC : Q ≤ Subgroup.centralizer ({y} : Set S')) (hQ : IsQuasisimple Q) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hev := CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hQ
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 (even_iff_two_dvd.mp hev)
  have hc2 : (c : S') ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
  have hcy : y * c = c * y := (Subgroup.mem_centralizer_singleton_iff.mp (hQC c.2)).symm
  have h1 := eq_one_of_commute_mulEquiv hK e hy3 hy1 hcy hc2
  have : c = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hc
  norm_num at hc

theorem noCfgS427_sl3 (hK : Nat.card K % 3 = 2) :
    NoCfgS427 (SpecialLinearGroup (Fin 3) K) := by
  intro σ h3 h1
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  by_cases hin : CFSG.RankThree.PartTwo.KFacts.IsInnerAut σ
  · obtain ⟨x, rfl, hx3, hx1⟩ := RonanKChevTwo.exists_conj_of_isInnerAut
      (RonanKChevTwo.conj_injective_of_center_eq_bot (RonanKChevTwo.center_sl_three_eq_bot hK))
      hord hin
    rw [autFix_conj]
    intro Q hQC hQ _ _
    exact false_of_quasisimple_le hK (MulEquiv.refl _) hx3 hx1 Q hQC hQ
  · obtain ⟨τσ, hτσ, τ, hτ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_congr_eq_fieldAut_of_mulEquiv_projSL
      hK (RonanKChevTwo.nonempty_sl_three_mulEquiv_projSL hK).some h3 hin
    have hinj : Function.Injective
        ((CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 K).comp
          (SpecialLinearGroup.map (fixedField τσ).subtype)) :=
      (CFSG.RankThree.PartTwo.KFacts.proj_three_injective hK).comp
        (CFSG.RankThree.PartTwo.KFacts.sl_map_subtype_injective τσ)
    obtain ⟨eC⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_eqLocus_mulEquiv τ σ _ hinj fun y => by
      rw [hτ]
      exact CFSG.RankThree.PartTwo.KFacts.mem_range_proj_comp_map_iff hK τσ y
    obtain ⟨hZ, hq⟩ := CFSG.RankThree.PartTwo.KFacts.fixedPoints_facts_of_mulEquiv_projSL hK
      (RonanKChevTwo.nonempty_sl_three_mulEquiv_projSL hK).some h3 hin
    have hfix : Sec4.autFix σ = σ.toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext y
      rfl
    rw [hfix]
    obtain ⟨hs, hna⟩ := CFSG.RankThree.OddKernel.isSimpleGroup_of_isQuasisimple hq hZ
    haveI := hs
    refine good427_of_le_simple le_rfl hna ?_ fun _ hQC _ => hQC
    rw [Nat.card_congr eC.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL,
      CFSG.Open.StatedAPI.card_statedSL_three]
    have hq2 : 2 ≤ Nat.card (fixedField τσ) := Finite.one_lt_card
    intro h
    have a1 : 8 ≤ Nat.card (fixedField τσ) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ Nat.card (fixedField τσ) ^ 3 := Nat.pow_le_pow_left hq2 3
    have a2 : 4 ≤ Nat.card (fixedField τσ) ^ 2 := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ Nat.card (fixedField τσ) ^ 2 := Nat.pow_le_pow_left hq2 2
    have a3 : 3 * 7 ≤ (Nat.card (fixedField τσ) ^ 2 - 1) * (Nat.card (fixedField τσ) ^ 3 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have := Nat.mul_le_mul a1 a3
    omega

theorem statedScalars_subgroupOf_statedSL3_eq_bot (hK : Nat.card K % 3 = 2) :
    (CFSG.Open.StatedScalars (Fin 3) K).subgroupOf (CFSG.Open.StatedSL 3 K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  have hdet : Matrix.GeneralLinearGroup.det (x : GL (Fin 3) K) = 1 :=
    MonoidHom.mem_ker.mp ((CFSG.Open.StatedAPI.statedSL_eq_ker_det 3 K).le x.2)
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc1 : c = 1 := CFSG.RankThree.PartTwo.KFacts.units_eq_one_of_pow_three_eq_one hK hdet
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

theorem center_eq_bot_of_sl3
    (hK : Nat.card K % 3 = 2) {L : Type} [Group L] [Finite L]
    (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* projSL 3 K) : Subgroup.center L = ⊥ := by
  haveI : Group.IsPerfect L := hL.1
  have hodd : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨φ, -, -, hD⟩ := CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map
    (K := K) (n := 3) (by norm_num) hodd (e.trans (CFSG.PGLModel.projSLEquivStatedProj 3 K))
  rw [← hD, statedScalars_subgroupOf_statedSL3_eq_bot hK, Subgroup.map_bot]

end L3

open L3

section Rows




theorem two_pow_mod_three_of_odd'
    {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem rowOf427_sl3_odd
    : ∀ n : ℕ, Odd n → RowOf427 (projSL 3 (GaloisField 2 n)) := by
  intro n hn S _ _ _ _ ⟨eSX⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact (Nat.not_odd_zero hn).elim
  have hK : Nat.card (GaloisField 2 n) % 3 = 2 := by
    rw [GaloisField.card 2 n hn0]
    exact two_pow_mod_three_of_odd' hn
  let eSL : SpecialLinearGroup (Fin 3) (GaloisField 2 n) ≃* projSL 3 (GaloisField 2 n) :=
    (RonanKChevTwo.nonempty_sl_three_mulEquiv_projSL hK).some
  refine row427_of_noCfg_qs ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_eq_bot_of_sl3 hK hL hZ3 (e'.trans eSX)
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv ((e'.trans eSX).trans eSL.symm) (noCfgS427_sl3 hK)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3 Q hQC hQ _
    exact (false_of_quasisimple_le hK ((e'.trans eSX).trans eSL.symm) hy3 hy1 Q hQC hQ).elim

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
