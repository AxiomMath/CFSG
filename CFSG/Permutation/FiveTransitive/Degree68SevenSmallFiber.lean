module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.Degree68SevenSmallFiber

theorem eq_one
    {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (a : MulAut G) (p : ℕ) (hp : p.Prime)
    (hap : a ^ p = 1) (hpres : ∀ x : G, f (a x) = f x)
    (hsmall : Nat.card f.ker < p) : a = 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  apply MulEquiv.ext
  intro x
  let Y := f ⁻¹' {f x}
  have hstable (y : G) : a y ∈ Y ↔ y ∈ Y := by
    change f (a y) = f x ↔ f y = f x
    rw [hpres]
  let u : Equiv.Perm Y := Equiv.Perm.subtypePerm a.toEquiv hstable
  have hpow (n : ℕ) (y : Y) : ((u ^ n) y).val = (a ^ n) y.val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change a (((u ^ n) y).val) = _
      rw [ih,pow_succ',MulAut.mul_apply]
  have hup : u ^ p = 1 := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    rw [hpow,hap]
    rfl
  have hY : Nat.card Y = Nat.card f.ker := Nat.card_congr (f.fiberEquivKer x)
  have hu : u = 1 := by
    by_contra hn
    have huorder : orderOf u = p := orderOf_eq_prime hup hn
    have hd : p ∣ Nat.card (Equiv.Perm Y) := huorder ▸ orderOf_dvd_natCard u
    rw [Nat.card_perm] at hd
    have hle := hp.dvd_factorial.mp hd
    rw [hY] at hle
    exact (not_le_of_gt hsmall) hle
  have he := congrArg (fun v : Equiv.Perm Y => (v ⟨x,rfl⟩).val) hu
  exact he

end FiveTransitive.Degree68SevenSmallFiber

end CFSG
