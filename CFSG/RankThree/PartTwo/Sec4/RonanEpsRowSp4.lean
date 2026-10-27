module

public import CFSG.RankThree.PartTwo.Sec4.RonanEpsLieOrders
public import CFSG.RankThree.PartTwo.Sec8.Item84KFacts4ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanEps

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projSp)

theorem card_statedProj_statedSp_two (F : Type) [Field F] [Finite F] [CharP F 2] :
    Nat.card (StatedProj (StatedSp 2 F)) =
      Nat.card F ^ 4 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
    show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
  ring_nf

theorem noCfgSEps_statedSp_two {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) : NoCfgSEps (StatedProj (StatedSp 2 F)) := by
  intro A α K hc
  haveI := hc.isPerfect
  haveI := hc.nontrivial
  have hcardT := card_statedProj_statedSp_two F
  rw [hF] at hcardT
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  · refine noCfgSEps_of_card_lt ?_ A α K hc
    rw [hcardT]
    norm_num
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hZT : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ := by
    have hsT : IsSimpleGroup (StatedProj (StatedSp 2 F)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have hnaT : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
      by_contra h
      push Not at h
      have hKab : ∀ a b : K, a * b = b * a := fun a b => Subtype.ext (h a b)
      exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hKab)
    exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnaT).2
  have hα3 : α ^ 3 = 1 := hc.pow_three
  by_cases hD : α ∈ (conjAut 2 F).range
  ·
    obtain ⟨H, hH⟩ := hD
    obtain ⟨y, hy⟩ : IsInnerAut α := hH ▸ conjAut_mem_inner_of_charTwo H
    have hinj := conj_injective_of_center_eq_bot hZT
    have hy3 : y ^ 3 = 1 := hinj (by rw [map_pow, hy, hα3, map_one])
    have hy1 : y ≠ 1 := fun h => hc.ne_one (by rw [← hy, h, map_one])
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
    have hfix : autFix α = Subgroup.centralizer ({y} : Set (StatedProj (StatedSp 2 F))) := by
      rw [← hy]
      exact RowV.autFix_conj_eq_centralizer y
    obtain ⟨ι⟩ := Sec8.Item84KFacts4.kF84Sp4ThreeCent_holds F h4 y hyo
    set N := inSubgroup perfectResidual (Subgroup.centralizer ({y} : Set (StatedProj (StatedSp 2 F)))) with hN
    have hKN : K ≤ N := by rw [hN, ← hfix]; exact hc.le_perfectResidual
    have hNC : N ≤ autFix α := by rw [hN, hfix]; exact Subgroup.map_subtype_le _
    have hNq : IsQuasisimple N := CFSG.LocalCores.isQuasisimple_of_mulEquiv ι.symm
      (RonanKChevTwo.SpFour.isQuasisimple_sl2 h4)
    have hNZ : Subgroup.center N = ⊥ :=
      center_eq_bot_of_mulEquiv ι Sec19.Item19Res2Proof.center_sl2_eq_bot
    have hcube := hc.isTypeEpsCube_of_le hKN hNC hNq hNZ
    refine not_isTypeEpsCube_of_card_sl2_even (n := n) hn ?_ hcube
    rw [Nat.card_congr ι.toEquiv, card_SL_two, hF]
  ·
    obtain ⟨φ, hφ, H, hαH⟩ := sp4_even_order_three_field_descent α hα3 hD
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hF hφ
    obtain ⟨m, rfl⟩ := h3n
    have hm : 1 ≤ m := by omega
    have hcard : Nat.card (fixedField φ) = 2 ^ m :=
      card_fixedField_of_orderOf_eq_three hφ (by rw [hF, ← pow_mul, mul_comm])
    haveI : CharP (fixedField φ) 2 := by
      have := Fintype.ofFinite (fixedField φ)
      exact charP_of_card_eq_prime_pow (p := 2) (f := m) (by rw [← Nat.card_eq_fintype_card, hcard])
    have hfixeq : Sec4.autFix (fieldAut 2 F φ) = ((proj 2 F).comp (spIncl φ)).range := by
      ext y
      rw [Sec4.mem_autFix, mem_range_proj_spIncl_iff φ y]
    have eSp : StatedSp 2 (fixedField φ) ≃* StatedProj (StatedSp 2 (fixedField φ)) :=
      MulEquiv.ofBijective (proj 2 (fixedField φ)) ⟨proj_injective_of_charTwo, proj_surjective⟩
    have eα : Sec4.autFix α ≃* StatedProj (StatedSp 2 (fixedField φ)) := by
      rw [hαH]
      exact (((autFixConjEquiv (conjAut 2 F H) (fieldAut 2 F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (proj_spIncl_injective φ)).symm).trans eSp
    have hcardC : Nat.card (autFix α) = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
      rw [Nat.card_congr eα.toEquiv, card_statedProj_statedSp_two, hcard]
    rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
    ·
      have h1 := le_card_of_isTypeEpsCube (isTypeEpsCube_of_cfgSEps hc)
      have h2 : Nat.card (K ⧸ CFSG.pCore 2 K) ∣ Nat.card (autFix α) :=
        (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hc.le_autFix)
      rw [hcardC] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      norm_num at this
      omega
    · have h4' : 4 ≤ Nat.card (fixedField φ) := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      haveI hCs : IsSimpleGroup (StatedProj (StatedSp 2 (fixedField φ))) :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (fixedField φ) 2
          (by norm_num) (Or.inl (Or.inr h4'))
      have hna : ∃ a b : StatedProj (StatedSp 2 (fixedField φ)), a * b ≠ b * a := by
        by_contra h
        push Not at h
        haveI : IsMulCommutative (StatedProj (StatedSp 2 (fixedField φ))) := ⟨⟨h⟩⟩
        have hab : ∀ a b : autFix α, a * b = b * a := fun a b =>
          eα.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
        have hKab : ∀ a b : K, a * b = b * a := fun a b => Subtype.ext
          (show (a : StatedProj (StatedSp 2 F)) * b = b * a from
            congrArg Subtype.val (hab ⟨a, hc.le_autFix a.2⟩ ⟨b, hc.le_autFix b.2⟩))
        exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hKab)
      obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
      have hcube := hc.isTypeEpsCube_of_le hc.le_autFix le_rfl
        (CFSG.LocalCores.isQuasisimple_of_mulEquiv eα.symm hq) (center_eq_bot_of_mulEquiv eα hZ)
      exact not_isTypeEpsCube_of_card_sp4_even hm hcardC hcube

theorem rowSEpsOf_seven_Sp4 (n : ℕ) (hn : 1 ≤ n) : RowSEpsOf (projSp 2 (GaloisField 2 n)) := by
  intro S _ _ _ _ ⟨eS⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  set τ := eS.trans (CFSG.PGLModel.projSpEquivStatedProj 2 (GaloisField 2 n))
  haveI : Finite (StatedProj (StatedSp 2 (GaloisField 2 n))) := Finite.of_equiv _ τ.toEquiv
  exact (noCfgSEps_statedSp_two hn hF).of_mulEquiv τ

end CFSG.RankThree.PartTwo.Sec4.RonanEps
