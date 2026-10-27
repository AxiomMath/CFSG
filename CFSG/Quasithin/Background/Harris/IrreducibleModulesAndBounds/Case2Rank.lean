module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22
public import CFSG.Quasithin.Background.G9Stmts
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case2_rank
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22) :
    m ≤ 5 ∧ (m = 5 → ¬ A ≤ L) := by
  obtain ⟨hAN, hAel, hAcard, hirr⟩ := exists_mulaut_data
    (fun γ hγ l hl => h.H_normal γ hγ l hl) h.A_le h.A_elem h.A_card h.H_irr
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hq := isQuasisimple_toMulSub h.L_comp.2.2
  have e' : CQ (toMulSub L) ≃* S22 := cqEquiv_toMulSub_comp e
  have hc := card_le_two_mul_inf hW hq.1 hirr hAN hAel e' m22_center_eq_bot' m22_mulAut_card
  have hel0 : IsElemAbelian2 (toMulSub A ⊓ toMulSub L) :=
    ⟨fun a ha b hb => hAel.1 a ha.1 b hb.1, fun a ha => hAel.2 a ha.1⟩
  have h4 := card_le_two_pow_of_le hW hirr inf_le_right hel0 e' m22_rank_le
  rw [hAcard] at hc
  have hm5 : m ≤ 5 := by
    have : 2 ^ m ≤ 2 ^ 5 := by
      calc 2 ^ m ≤ 2 * Nat.card ↥(toMulSub A ⊓ toMulSub L) := hc
        _ ≤ 2 * 2 ^ 4 := Nat.mul_le_mul le_rfl h4
        _ = 2 ^ 5 := by norm_num
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine ⟨hm5, fun hm5' hAL => ?_⟩
  have hle : toMulSub A ≤ toMulSub L := Subgroup.map_mono hAL
  have h4' := card_le_two_pow_of_le hW hirr hle hAel e' m22_rank_le
  rw [hAcard, hm5'] at h4'
  omega

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
