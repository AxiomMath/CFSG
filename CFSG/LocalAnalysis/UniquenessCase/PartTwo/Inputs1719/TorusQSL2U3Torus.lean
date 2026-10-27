module

public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedSmallProjOrders
public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)

private theorem l2u3_dvd_of_dvd_mul_self {d k m : ℕ} (hkm : Nat.Coprime k m)
    (h₁ : d ∣ k * k) (h₂ : d ∣ k * m) : d ∣ k := by
  have h := Nat.dvd_gcd h₁ h₂
  rwa [Nat.gcd_mul_left, hkm.gcd_eq_one, mul_one] at h

private theorem l2u3_two_pow_eq (n : ℕ) : ∃ k, 2 ^ n = k + 1 :=
  ⟨2 ^ n - 1, by have := pow_pos (two_pos : (0 : ℕ) < 2) n; omega⟩

private theorem l2u3_coprime {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ n) ∧ Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) ∧
      Nat.Coprime (2 ^ n - 1) ((2 ^ n) ^ 3 + 1) := by
  have hev : 2 ^ n % 2 = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, Nat.mul_mod_left]
  obtain ⟨k, hk⟩ := l2u3_two_pow_eq n
  have h2 : Nat.Coprime k 2 := Nat.coprime_two_right.mpr (Nat.odd_iff.mpr (by omega))
  rw [hk, Nat.add_sub_cancel]
  refine ⟨Nat.coprime_self_add_right.mpr (Nat.coprime_one_right k), ?_, ?_⟩
  · rw [show k + 1 + 1 = k + 2 by ring]
    exact Nat.coprime_self_add_right.mpr h2
  · rw [show (k + 1) ^ 3 + 1 = 2 + (k ^ 2 + 3 * k + 3) * k by ring]
    exact (Nat.coprime_add_mul_right_right k 2 _).mpr h2

private theorem l2u3_card_l2 {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    Nat.card X = (2 ^ n - 1) * (2 ^ n * (2 ^ n + 1)) := by
  rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)]
  obtain ⟨k, hk⟩ := l2u3_two_pow_eq n
  rw [hk, show (k + 1) ^ 2 = k * (k + 2) + 1 by ring]
  simp only [Nat.add_sub_cancel]
  ring

private theorem l2u3_card_u3 {X : Type} [Group X] {n : ℕ} (heven : Even n)
    (h : IsU3 X n) :
    Nat.card X = (2 ^ n - 1) * ((2 ^ n) ^ 3 * (2 ^ n + 1) * ((2 ^ n) ^ 3 + 1)) := by
  have hc := CFSG.Open.StatedAPI.card_mul_gcd_of_statedClassicalModel_psu_three
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)
  have hg : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have := CFSG.two_pow_mod_three_of_even heven
    rw [Nat.gcd_rec, show (2 ^ n + 1) % 3 = 2 by omega]
    all_goals norm_num
  rw [hg, mul_one] at hc
  rw [hc]
  obtain ⟨k, hk⟩ := l2u3_two_pow_eq n
  rw [hk, show (k + 1) ^ 2 = k * (k + 2) + 1 by ring]
  simp only [Nat.add_sub_cancel]
  ring

theorem torus_l2u3 {P₁ P₂ : Type} [Group P₁] [Group P₂] [Finite P₁] [Finite P₂] {n : ℕ}
    (hn : 2 ≤ n) (heven : Even n) (h₁ : IsL2 P₁ n) (h₂ : IsU3 P₂ n) {T : Subgroup (P₁ × P₂)}
    (hT : IsZModSq T n) :
    Nat.card (T.map (MonoidHom.fst P₁ P₂)) = 2 ^ n - 1 ∧
      Nat.card (T.map (MonoidHom.snd P₁ P₂)) = 2 ^ n - 1 ∧
      T = (T.map (MonoidHom.fst P₁ P₂)).prod (T.map (MonoidHom.snd P₁ P₂)) := by
  have hTc := S19.card_eq_of_isZModSq hT
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hk0 : 0 < 2 ^ n - 1 := by omega
  obtain ⟨c₁, c₂, c₃⟩ := l2u3_coprime (n := n) (by omega)
  have hd₁ : Nat.card (T.map (MonoidHom.fst P₁ P₂)) ∣ 2 ^ n - 1 := by
    refine l2u3_dvd_of_dvd_mul_self (c₁.mul_right c₂) ?_ ?_
    · rw [← hTc]; exact Subgroup.card_map_dvd T _
    · rw [← l2u3_card_l2 h₁]; exact Subgroup.card_subgroup_dvd_card _
  have hd₂ : Nat.card (T.map (MonoidHom.snd P₁ P₂)) ∣ 2 ^ n - 1 := by
    refine l2u3_dvd_of_dvd_mul_self (((c₁.pow_right 3).mul_right c₂).mul_right c₃) ?_ ?_
    · rw [← hTc]; exact Subgroup.card_map_dvd T _
    · rw [← l2u3_card_u3 heven h₂]; exact Subgroup.card_subgroup_dvd_card _
  have hle : T ≤ (T.map (MonoidHom.fst P₁ P₂)).prod (T.map (MonoidHom.snd P₁ P₂)) :=
    fun x hx => Subgroup.mem_prod.mpr ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩
  have hprod : Nat.card ((T.map (MonoidHom.fst P₁ P₂)).prod (T.map (MonoidHom.snd P₁ P₂))) =
      Nat.card (T.map (MonoidHom.fst P₁ P₂)) * Nat.card (T.map (MonoidHom.snd P₁ P₂)) := by
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  have hcard := Subgroup.card_le_of_le hle
  rw [hprod, hTc] at hcard
  have l₁ := Nat.le_of_dvd hk0 hd₁
  have l₂ := Nat.le_of_dvd hk0 hd₂
  have e₁ : Nat.card (T.map (MonoidHom.fst P₁ P₂)) = 2 ^ n - 1 :=
    le_antisymm l₁ (Nat.le_of_mul_le_mul_right (hcard.trans (Nat.mul_le_mul le_rfl l₂)) hk0)
  have e₂ : Nat.card (T.map (MonoidHom.snd P₁ P₂)) = 2 ^ n - 1 :=
    le_antisymm l₂ (Nat.le_of_mul_le_mul_left (hcard.trans (Nat.mul_le_mul l₁ le_rfl)) hk0)
  exact ⟨e₁, e₂, Subgroup.eq_of_le_of_card_ge hle (by rw [hprod, e₁, e₂, hTc])⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
