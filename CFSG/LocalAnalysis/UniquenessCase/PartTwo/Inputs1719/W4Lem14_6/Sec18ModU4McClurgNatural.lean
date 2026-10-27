module

public import CFSG.HardMathSupport.U4FF.Disp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.HardMathSupport.U4FF.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg

open CFSG.LocalAnalysis.RankThreeUC CFSG.HardMathSupport.U4FF

theorem two_pow_two_mul_disp_le_card {S : Type} [CommGroup S] [Finite S]
    [Fact (∀ s : S, s * s = 1)] {t : MulAut S} (ht : t * t = 1) :
    2 ^ (2 * disp t) ≤ Nat.card S := by
  have hsq : ∀ v : S, v * v = 1 := Fact.out
  let δ : S →* S :=
    { toFun := fun v => t v * v⁻¹
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl }
  have hfix : ∀ v : S, t (δ v) = δ v := by
    intro v
    have htapply : t (t v) = v := by
      have := congrArg (fun a : MulAut S => a v) ht
      simpa using this
    have hinv1 : (t v)⁻¹ = t v := (eq_inv_iff_mul_eq_one.2 (hsq (t v))).symm
    have hinv2 : v⁻¹ = v := (eq_inv_iff_mul_eq_one.2 (hsq v)).symm
    change t (t v * v⁻¹) = t v * v⁻¹
    calc t (t v * v⁻¹) = t (t v) * t v⁻¹ := map_mul t _ _
      _ = t (t v) * (t v)⁻¹ := by rw [map_inv]
      _ = v * (t v)⁻¹ := by rw [htapply]
      _ = t v * v⁻¹ := by
          rw [hinv1, hinv2]
          exact mul_comm v (t v)
  have hpow : ∀ (k : ℤ) (v : S), (t ^ k) (δ v) = δ v := by
    intro k
    induction k using Int.induction_on with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [zpow_add_one, MulAut.mul_apply, hfix v]
        exact ih v
    | pred k ih =>
        intro v
        have hinvt : t⁻¹ = t := by
          rw [inv_eq_iff_mul_eq_one]
          exact ht
        rw [zpow_sub_one, MulAut.mul_apply, hinvt, hfix v]
        exact ih v
  have hle : δ.range ≤ CFSG.Quasithin.fixV (Subgroup.zpowers t) := by
    intro x hx
    obtain ⟨v, rfl⟩ := hx
    rw [CFSG.Quasithin.mem_fixV]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hpow k v
  have hcard : Nat.card δ.range = 2 ^ disp t := by
    rw [show Nat.card δ.range = Nat.card (Set.range fun v : S => t v * v⁻¹) from rfl]
    rw [CFSG.QuasithinUnique.Setup.Family.card_range_displacement t]
    rfl
  have h1 : 2 ^ disp t ≤ Nat.card (CFSG.Quasithin.fixV (Subgroup.zpowers t)) := by
    rw [← hcard]
    exact Subgroup.card_le_of_le hle
  have h2 := card_eq_fixV_zpowers_mul t
  calc 2 ^ (2 * disp t) = 2 ^ (disp t + disp t) := by rw [two_mul]
    _ = 2 ^ disp t * 2 ^ disp t := by rw [pow_add]
    _ ≤ Nat.card (CFSG.Quasithin.fixV (Subgroup.zpowers t)) * 2 ^ disp t :=
        Nat.mul_le_mul_right _ h1
    _ = Nat.card S := h2.symm

theorem disp_le_of_naturalU4Mod {S : Type} [CommGroup S] [Finite S]
    [Fact (∀ s : S, s * s = 1)] {n : ℕ} {L : Subgroup (MulAut S)} (h : NaturalU4Mod n L)
    {t : MulAut S} (ht : t * t = 1) : disp t ≤ 4 * n := by
  have h2 := two_pow_two_mul_disp_le_card (S := S) (t := t) ht
  rcases h with ⟨F, _hF, _hFin, hcardF, ε, ψ, _hψ⟩ |
      ⟨F, _hF, _hFin, b, c, hcardF, _hno, ε, ψ, _hψ⟩
  · have hcard : Nat.card S = Nat.card F ^ 4 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      simp
    have hS : Nat.card S = 2 ^ (8 * n) := by
      rw [hcard, hcardF]
      calc ((2 ^ n) ^ 2) ^ 4 = (2 ^ n) ^ (2 * 4) := by rw [pow_mul]
        _ = (2 ^ n) ^ 8 := by norm_num
        _ = 2 ^ (n * 8) := by rw [pow_mul]
        _ = 2 ^ (8 * n) := by rw [Nat.mul_comm]
    rw [hS] at h2
    have h3 : 2 * disp t ≤ 8 * n := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    omega
  · have hcard : Nat.card S = Nat.card F ^ 6 := by
      rw [Nat.card_congr ψ.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun]
      norm_num
    have hS : Nat.card S = 2 ^ (6 * n) := by
      rw [hcard, hcardF]
      calc (2 ^ n) ^ 6 = 2 ^ (n * 6) := by rw [pow_mul]
        _ = 2 ^ (6 * n) := by rw [Nat.mul_comm]
    rw [hS] at h2
    have h3 : 2 * disp t ≤ 6 * n := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.McClurg
