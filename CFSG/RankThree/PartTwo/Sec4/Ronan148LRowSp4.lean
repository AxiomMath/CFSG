module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.RankThree.PartTwo.KFacts.K71Sp4
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.RankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Assembly.RankThreeEven (projSp projSU)

section Sp4

theorem padicValNat_ordSp4_two_pow {n : ℕ} (hn : 1 ≤ n) :
    padicValNat 2 ((2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1))) = 4 * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Odd ((2 ^ n) ^ 2 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have h2 : Odd ((2 ^ n) ^ 4 - 1) := CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)
  have hodd := h1.mul h2
  rw [padicValNat.mul (by positivity) hodd.pos.ne',
    padicValNat.eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero, ← pow_mul,
    padicValNat.prime_pow, mul_comm]

theorem charP_fixedField_of_card {F : Type} [Field F] [Finite F] (φ : F ≃+* F) {m : ℕ}
    (hm : Nat.card (fixedField φ) = 2 ^ m) (hm1 : 1 ≤ m) : CharP (fixedField φ) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite (fixedField φ)
  exact charP_of_card_eq_prime_pow (p := 2) (f := m) (by rw [← Nat.card_eq_fintype_card, hm])

theorem false_of_sp4_cover (k : Type) [Field k] [Finite k] [CharP k 2] {n : ℕ}
    (hk : Nat.card k = 2 ^ n) (hn : 1 ≤ n) {G : Type*} [Group G] {C Y : Subgroup G}
    (eC : C ≃* StatedProj (StatedSp 2 k)) (hYC : Y ≤ C) [Group.IsPerfect Y]
    (hsub : (Y.subgroupOf C).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardC : Nat.card C = (2 ^ n) ^ 4 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 4 - 1)) := by
    rw [Nat.card_congr eC.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hk,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, Finset.prod_pair (by norm_num)]
    norm_num
  have hU := padicValNat_card_projSU (by omega : 1 ≤ m)
  have hU1 := one_lt_card_projSU (by omega : 1 ≤ m)
  have hdU : Nat.card (projSU 3 2 m) ∣ Nat.card Y := Subgroup.card_dvd_of_surjective hπ
  have hdY : Nat.card Y ∣ Nat.card C := Subgroup.card_dvd_of_le hYC
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | hn2
  ·
    have h := hdU.trans hdY
    rw [hcardC] at h
    have h2 : 2 ^ (3 * m) ∣ Nat.card (projSU 3 2 m) := hU ▸ pow_padicValNat_dvd
    have hm3 : 3 ≤ m := by
      obtain ⟨j, rfl⟩ := hmo
      omega
    have h512 : 2 ^ 9 ∣ 2 ^ (3 * m) := pow_dvd_pow 2 (by omega)
    have := (h512.trans h2).trans h
    norm_num at this
  ·
    have h4 : 4 ≤ Nat.card k := by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    haveI : IsSimpleGroup (StatedProj (StatedSp 2 k)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp k 2 (by norm_num)
        (Or.inl (Or.inr h4))
    haveI hCs : IsSimpleGroup C := eC.isSimpleGroup
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hCs hsub with h | h
    ·
      have hY1 : Y = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        have : (⟨y, hYC hy⟩ : C) ∈ Y.subgroupOf C := hy
        rw [h, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      rw [hY1, Subgroup.card_bot] at hdU
      have := Nat.le_of_dvd (by norm_num) hdU
      omega
    ·
      have hYeq : Y = C := by
        refine le_antisymm hYC fun y hy => ?_
        have : (⟨y, hy⟩ : C) ∈ Y.subgroupOf C := by
          rw [h]
          exact Subgroup.mem_top _
        exact this
      have eY : Y ≃* C := MulEquiv.subgroupCongr hYeq
      haveI : IsSimpleGroup Y := eY.isSimpleGroup
      have hcY := card_eq_of_isSimpleGroup_surj π hπ hU1
      have hv := padicValNat_ordSp4_two_pow hn
      rw [← hcardC, ← Nat.card_congr eY.toEquiv, hcY, hU] at hv
      obtain ⟨j, rfl⟩ := hmo
      omega

end Sp4

section Sp4Row

theorem rowU3_Sp4 {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) {n : ℕ} (hn : 1 ≤ n) (eS : S ≃* projSp 2 (GaloisField 2 n))
    {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ)
    [Group.IsPerfect Y] (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ}
    (hmo : Odd m) (hm1 : 1 < m) (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, σ k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 n with hF
  have hFcard : Nat.card F = 2 ^ n := GaloisField.card 2 n (by omega)
  set τ : S ≃* StatedProj (StatedSp 2 F) :=
    eS.trans (CFSG.PGLModel.projSpEquivStatedProj 2 F) with hτ
  have hnaP : ∃ a b : StatedProj (StatedSp 2 F), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨τ a, τ b, fun h => hab (τ.injective (by rw [map_mul, map_mul, h]))⟩
  have hsP : IsSimpleGroup (StatedProj (StatedSp 2 F)) := τ.symm.isSimpleGroup
  have hZ := RonanK429Lie.center_trivial_of_isSimpleGroup hsP hnaP
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hFcard]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hD : α ∈ (conjAut 2 F).range
  ·
    obtain ⟨H, hH⟩ := hD
    have hin : IsInnerAut α := hH ▸ conjAut_mem_inner_of_charTwo H
    refine RonanK429Lie.false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hσ1 hEY hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact RonanK429Lie.card_le_nine_inn (fun E hE h27 =>
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.noE27_projSp_two h3F
        ⟨E, hE, h27⟩) hZ hB h3B hcB
  ·
    obtain ⟨φ, hφ, H, hαH⟩ := sp4_even_order_three_field_descent α hα3 hD
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two hn hFcard hφ
    obtain ⟨m', rfl⟩ := h3n
    have hm' : 1 ≤ m' := by omega
    have hcard : Nat.card (fixedField φ) = 2 ^ m' :=
      card_fixedField_of_orderOf_eq_three hφ (by rw [hFcard, ← pow_mul, mul_comm])
    haveI := charP_fixedField_of_card φ hcard hm'
    have hfixeq : Sec4.autFix (fieldAut 2 F φ) = ((proj 2 F).comp (spIncl φ)).range := by
      ext y
      rw [Sec4.mem_autFix, mem_range_proj_spIncl_iff φ y]
    have eSp : StatedSp 2 (fixedField φ) ≃* StatedProj (StatedSp 2 (fixedField φ)) :=
      MulEquiv.ofBijective (proj 2 (fixedField φ)) ⟨proj_injective_of_charTwo, proj_surjective⟩
    have eα : Sec4.autFix α ≃* StatedProj (StatedSp 2 (fixedField φ)) := by
      rw [hαH]
      exact (((RonanK429Lie.autFixConjEquiv (conjAut 2 F H) (fieldAut 2 F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (proj_spIncl_injective φ)).symm).trans eSp
    exact false_of_sp4_cover (fixedField φ) hcard hm'
      ((Sec4.autFixCongrEquiv τ σ).symm.trans eα) hYC hsub hmo hm1 π hπ

end Sp4Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
