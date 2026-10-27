module

public import CFSG.Quasithin.Background.G11Bridge
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

instance finite_GLV [Finite V] : Finite (GLV V) :=
  Finite.of_injective (fun g : GLV V => (g : V → V)) (fun a b h => LinearEquiv.ext (congrFun h))

theorem mul_self_eq_one_multiplicative (w : Multiplicative V) : w * w = 1 := by
  have h : Multiplicative.toAdd w + Multiplicative.toAdd w = 0 := by
    rw [← two_smul (ZMod 2)]
    have h2 : (2 : ZMod 2) = 0 := by decide
    rw [h2, zero_smul]
  have h' := congrArg Multiplicative.ofAdd h
  simpa [ofAdd_add] using h'

theorem orderOf_two_le_finrank_of_orderOf [Finite V] {g : GLV V} {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hg : orderOf g = p) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  have hW : ∀ w : Multiplicative V, w * w = 1 := mul_self_eq_one_multiplicative
  have hg' : orderOf (linEquivMulAut g) = p := by rw [MulEquiv.orderOf_eq]; exact hg
  have h1 := CFSG.QuasithinUnique.Setup.X1.two_pow_orderOf_le_index_fixV hW hp2 hg'
  have h2 := CFSG.QuasithinUnique.Setup.X1.index_fixV_le_card
    (W := Multiplicative V) (Subgroup.zpowers (linEquivMulAut g))
  have h3 : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [Nat.card_zmod] at this
    exact this
  rw [h3] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans h2)

theorem orderOf_two_le_finrank_of_dvd_card [Finite V] (L : Subgroup (GLV V)) {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpL
  exact orderOf_two_le_finrank_of_orderOf (g := (x : GLV V)) hp2 (by rw [Subgroup.orderOf_coe]; exact hx)

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
