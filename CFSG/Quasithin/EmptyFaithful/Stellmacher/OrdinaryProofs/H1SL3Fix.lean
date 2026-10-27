module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

variable {G : Type*} [Group G] {M : Type*} [AddCommGroup M]

theorem crossedHom_eq_zero_of_commute (act : G →* AddMonoid.End M)
    (f : G → M) (hf : ∀ g h, f (g * h) = f g + act g (f h))
    (t u : G) (hcomm : t * u = u * t) (ht : f t = 0)
    (hfix : ∀ v : M, act t v = v → v = 0) :
    f u = 0 := by
  have h1 : f (t * u) = act t (f u) := by
    rw [hf, ht, zero_add]
  have h2 : f (u * t) = f u := by
    rw [hf, ht, map_zero, add_zero]
  have h3 : act t (f u) = f u := by
    rw [← h1, hcomm, h2]
  exact hfix (f u) h3

theorem crossedHom_one (act : G →* AddMonoid.End M) (f : G → M)
    (hf : ∀ g h, f (g * h) = f g + act g (f h)) : f 1 = 0 := by
  have h := hf 1 1
  simpa using h

@[expose] def crossedHomKer (act : G →* AddMonoid.End M) (f : G → M)
    (hf : ∀ g h, f (g * h) = f g + act g (f h)) : Subgroup G where
  carrier := {g | f g = 0}
  one_mem' := crossedHom_one act f hf
  mul_mem' := by
    intro a b ha hb
    show f (a * b) = 0
    rw [hf, ha, hb]
    simp
  inv_mem' := by
    intro a ha
    show f a⁻¹ = 0
    have h := hf a a⁻¹
    rw [mul_inv_cancel, crossedHom_one act f hf, ha, zero_add] at h
    have hinv : act a⁻¹ * act a = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
    have hx : act a⁻¹ (act a (f a⁻¹)) = f a⁻¹ := by
      simpa using DFunLike.congr_fun hinv (f a⁻¹)
    rw [← hx, ← h, map_zero]

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
