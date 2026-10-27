module

public import CFSG.Quasithin.Vol2.Ch11SecAKind
public import CFSG.Quasithin.Vol2.Ch11SecFBlock

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)

theorem card_statedSL_three (F : Type) [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  rw [← CFSG.BrauerLinearThree.card_SL_three]
  have e : ↥(StatedSL 3 F) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulEquiv.subgroupCongr (CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL 3 F)).trans
      (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm
  exact Nat.card_congr e.toEquiv

theorem false_of_card_eq {m n : ℕ} (hn : 1 ≤ n)
    (h : 2 ^ (3 * m) * (2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1) =
      2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1))) : False := by
  have hR : 0 < 2 ^ (4 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (4 * n) - 1)) := by
    have h1 : 2 ≤ 2 ^ (2 * n) := Nat.le_self_pow (by omega) 2
    have h2 : 2 ≤ 2 ^ (4 * n) := Nat.le_self_pow (by omega) 2
    have h1' : 0 < 2 ^ (2 * n) - 1 := by omega
    have h2' : 0 < 2 ^ (4 * n) - 1 := by omega
    positivity
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have h0 : 2 ^ (3 * 0) * (2 ^ (3 * 0) - 1) * (2 ^ (2 * 0) - 1) = 0 := by norm_num
      rw [h0] at h
      omega
    · exact hm
  have h3 : 3 * m = 4 * n := by
    refine SecA.eq_of_two_pow_mul_odd ((SecA.odd_two_pow_sub_one (e := 3 * m) (by omega)).mul
      (SecA.odd_two_pow_sub_one (e := 2 * m) (by omega)))
      ((SecA.odd_two_pow_sub_one (e := 2 * n) (by omega)).mul
      (SecA.odd_two_pow_sub_one (e := 4 * n) (by omega))) ?_
    rw [← mul_assoc]
    exact h
  rw [h3, mul_assoc] at h
  have hpos : 0 < 2 ^ (4 * n) := by positivity
  have h4 := Nat.eq_of_mul_eq_mul_left hpos h
  have h5 : 0 < 2 ^ (4 * n) - 1 := by
    have : 2 ≤ 2 ^ (4 * n) := Nat.le_self_pow (by omega) 2
    omega
  rw [mul_comm (2 ^ (2 * n) - 1)] at h4
  have h6 := Nat.eq_of_mul_eq_mul_left h5 h4
  have h7 : 2 ^ (2 * m) = 2 ^ (2 * n) := by
    have : 1 ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
    have : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
    omega
  have h8 := Nat.pow_right_injective (le_refl 2) h7
  omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem not_isSL3Block (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n) :
    ¬ IsSL3Block L := by
  rintro ⟨-, m, F, _, _, hF, α, hα, hker, -⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
  obtain ⟨q⟩ := hset.quot
  have hn : 1 ≤ n := by have := hset.one_lt; omega
  have e₁ : ↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  have hc := (Nat.card_congr e₁.toEquiv).symm.trans (Nat.card_congr (q.trans e).toEquiv)
  rw [card_statedSL_three, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    Nat.card_eq_fintype_card (α := F), hF, hK] at hc
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num)] at hc
  apply false_of_card_eq (m := m) hn
  rw [← pow_mul, ← pow_mul, ← pow_mul] at hc
  convert hc using 2 <;> ring_nf

theorem pCoreOf_eq_fsuV_of_not_le (hF : Sp4Facts) (h13 : ASInputs.AS_I_1_3_Sp4)
    (h1102 : Stmt11_0_2) (h1115 : Stmt11_1_5) (h : Hyp11 G T L I n)
    (hset : SecD.NatSetting11 G T L I n) (hk : KindSp4 L (fsuV T I) n) {V₁ V₂ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hR : ¬ Subgroup.normalizer (ROf T L V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 L = fsuV T I := by
  rcases h1115 G T L I n V₁ h hV₁ with h1 | ⟨-, hb, -, -⟩
  · exact absurd h1 hR
  · rcases hb with hb | hb
    · exact absurd hb (not_isSL3Block hset hk)
    · exact pCoreOf_eq_fsuV_of_isSp4Block hF h13 h1102 h hset hk hV₂ hb

end CFSG.Quasithin.Vol2.Ch11.SecF
