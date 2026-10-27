module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin
open scoped Matrix

theorem coe_eq_neg_one_of_mul_self {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)} (hg : g * g = 1) (hg1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hm : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = Matrix.adjugate g := by
    rw [← Matrix.SpecialLinearGroup.coe_inv, hinv]
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := g.2
  rw [Matrix.adjugate_fin_two] at hm
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10
  have hb : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
    have : (2 : ZMod p) * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
      linear_combination e01
    exact (mul_eq_zero.mp this).resolve_left h2
  have hc : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
    have : (2 : ZMod p) * (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
      linear_combination e10
    exact (mul_eq_zero.mp this).resolve_left h2
  have ha : ((g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 - 1) *
      ((g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 + 1) = 0 := by
    rw [hb, hc, ← e00] at hdet
    linear_combination hdet
  have h01 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 := by
    rw [hb, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
  have h10 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 =
      (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 := by
    rw [hc, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  rcases mul_eq_zero.mp ha with ha | ha
  · exfalso
    apply hg1
    have h00 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = 1 := sub_eq_zero.mp ha
    have h11 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = 1 := by rw [← e00]; exact h00
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00.trans (Matrix.one_apply_eq 0).symm
    · exact h01
    · exact h10
    · exact h11.trans (Matrix.one_apply_eq 1).symm
  · have h00 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = -1 := eq_neg_of_add_eq_zero_left ha
    have h11 : (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = -1 := by rw [← e00]; exact h00
    have n00 : (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 = -1 := by
      rw [Matrix.neg_apply, Matrix.one_apply_eq]
    have n11 : (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 = -1 := by
      rw [Matrix.neg_apply, Matrix.one_apply_eq]
    have n01 : (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 = 0 := by
      rw [Matrix.neg_apply, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact neg_zero
    have n10 : (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 = 0 := by
      rw [Matrix.neg_apply, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
      exact neg_zero
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00.trans n00.symm
    · exact hb.trans n01.symm
    · exact hc.trans n10.symm
    · exact h11.trans n11.symm

theorem conj_eq_inv_of_natural {p : ℕ} {X : Type} [Group X] {F : Subgroup X} [F.Normal]
    (e : F ≃* Multiplicative (Fin 2 → ZMod p))
    (ψ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p))
    (hψ : ∀ (x : X) (f : F), e (MulAut.conjNormal x f) =
      Multiplicative.ofAdd
        ((((ψ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p))) *ᵥ (Multiplicative.toAdd (e f))))
    {x : X} (hx : ((ψ x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = -1) (f : F) :
    x * (f : X) * x⁻¹ = (f : X)⁻¹ := by
  have h := hψ x f
  rw [hx, Matrix.neg_mulVec, Matrix.one_mulVec] at h
  have h' : MulAut.conjNormal x f = f⁻¹ := by
    apply e.injective
    rw [h, map_inv]
    rfl
  have := congrArg Subtype.val h'
  rwa [MulAut.conjNormal_apply] at this

theorem card_sl2_zmod (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  rw [CFSG.GorensteinWalter.sl2_card_formula, Nat.card_zmod]

theorem not_isPGroup_two_sl2_five :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro h
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp h
  rw [card_sl2_zmod] at hn
  have h3 : (3 : ℕ) ∣ 2 ^ n := by rw [← hn]; norm_num
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem eq_five_of_sl2_equiv {p : ℕ} [Fact p.Prime]
    (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
    p = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc := Nat.card_congr e.toEquiv
  rw [card_sl2_zmod, card_sl2_zmod] at hc
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : p ≤ 5 := by
    by_contra hlt
    have h36 : 36 ≤ p ^ 2 := by nlinarith [not_le.mp hlt]
    have : 6 * 35 ≤ p * (p ^ 2 - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  interval_cases p
  all_goals first | rfl | (norm_num at hc)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
