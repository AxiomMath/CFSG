module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

theorem odd_nsmul_eq_self {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {n : ℕ} (hn : Odd n)
    (x : M) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
  have h1 : ((2 * k + 1 : ℕ) : ZMod 2) = 1 := by
    have h2 : (2 : ZMod 2) = 0 := rfl
    push_cast
    rw [h2, zero_mul, zero_add]
  rw [h1, one_smul]

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem crossedHom_principal_on_odd (T : Subgroup G) [Fintype T] (hT : Odd (Fintype.card T))
    (act : G →* AddMonoid.End M)
    (f : G → M) (hf : ∀ g h, f (g * h) = f g + act g (f h)) :
    ∃ w : M, ∀ t : T, f (t : G) = w - act t w := by
  classical
  set h : T → M := fun s => f (s : G) with hh
  have hcocycle : ∀ t s : T, h (t * s) = h t + act (t : G) (h s) := by
    intro t s
    simp only [hh, Subgroup.coe_mul]
    exact hf _ _
  refine ⟨∑ s : T, h s, fun t => ?_⟩
  have hsum : ∑ s : T, h (t * s) = ∑ s : T, h s :=
    Equiv.sum_comp (Equiv.mulLeft t) h
  have hexp : ∑ s : T, h (t * s) = Fintype.card T • h t + act t (∑ s : T, h s) := by
    simp only [hcocycle, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, map_sum]
  have hw : ∑ s : T, h s = Fintype.card T • h t + act t (∑ s : T, h s) := by
    rw [← hexp, hsum]
  have h3 := eq_sub_of_add_eq hw.symm
  rw [odd_nsmul_eq_self hT] at h3
  exact h3

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
