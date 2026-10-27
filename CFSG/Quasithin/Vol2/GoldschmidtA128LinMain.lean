module

public import CFSG.Quasithin.Vol2.GoldschmidtA128LinSupp
public import CFSG.Quasithin.Vol2.GoldschmidtA128LinComb
public import Mathlib.Algebra.Order.Ring.Star

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.A128.Lin

theorem rep_bound {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {n : ℕ} {R : (Fin n → ZMod 2) → Module.End F V}
    (hR : IsRep R) (hinj : Function.Injective R)
    (hfix : ∀ x : Fin n → ZMod 2, x ≠ 0 → Module.finrank F (LinearMap.ker (R x - 1)) ≤ 2) :
    n ≤ 3 ∧ (n = 3 → ∃ x, R x = -1) := by
  have h1 := fun x (hx : x ≠ 0) => hR.exists_supp_dot_eq_one h2 hinj hx
  have h2' := fun x (hx : x ≠ 0) => hR.card_supp_filter_le h2 (hfix x hx)
  refine ⟨le_three_of_dot (supp R) h1 h2', fun hn => ?_⟩
  obtain ⟨x, -, hx1⟩ := exists_dot_eq_one_of_three hn (supp R) h1 h2'
  exact ⟨x, hR.eq_neg_one_of_supp h2 hx1⟩

theorem exists_mulEquiv_zmod_two {E : Type*} [Group E] [Finite E] (hsq : ∀ e : E, e * e = 1)
    (hcomm : ∀ a b : E, a * b = b * a) :
    ∃ d : ℕ, Nonempty (Multiplicative (Fin d → ZMod 2) ≃* E) := by
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  let : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul, ← ofMul_toMul x, ← ofMul_mul, hsq, ofMul_one]
  have : Module.Finite (ZMod 2) (Additive E) := Module.Finite.of_finite
  exact ⟨_, ⟨(AddEquiv.toMultiplicativeRight
    (Module.finBasis (ZMod 2) (Additive E)).equivFun.toAddEquiv).symm⟩⟩

end CFSG.Quasithin.Vol2.A128.Lin

namespace CFSG.Quasithin.Vol2.A128

theorem elemAbelian_two_bound {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {E : Type*} [Group E] [Finite E]
    (hsq : ∀ e : E, e * e = 1) (hcomm : ∀ a b : E, a * b = b * a)
    (ρ : E →* Module.End F V) (hinj : Function.Injective ρ)
    (hfix : ∀ e : E, e ≠ 1 → Module.finrank F (LinearMap.ker (ρ e - 1)) ≤ 2) :
    Nat.card E ≤ 8 ∧ (Nat.card E = 8 → ∃ e : E, ρ e = -1) := by
  obtain ⟨d, ⟨φ⟩⟩ := Lin.exists_mulEquiv_zmod_two hsq hcomm
  let R : (Fin d → ZMod 2) → Module.End F V := fun x => ρ (φ (Multiplicative.ofAdd x))
  have hR : Lin.IsRep R :=
    ⟨by simp [R], fun x y => by simp [R, ofAdd_add]⟩
  have hRinj : Function.Injective R := fun x y h =>
    Multiplicative.ofAdd.injective (φ.injective (hinj h))
  have hRfix : ∀ x : Fin d → ZMod 2, x ≠ 0 →
      Module.finrank F (LinearMap.ker (R x - 1)) ≤ 2 := fun x hx =>
    hfix _ fun h => hx (Multiplicative.ofAdd.injective (φ.injective (h.trans φ.map_one.symm)))
  obtain ⟨hd, h3⟩ := Lin.rep_bound h2 hR hRinj hRfix
  have hcard : Nat.card E = 2 ^ d := by
    rw [← Nat.card_congr φ.toEquiv]
    simp
  refine ⟨?_, fun h8 => ?_⟩
  · rw [hcard]
    calc 2 ^ d ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hd
      _ = 8 := by norm_num
  · have hd3 : d = 3 := by
      rw [hcard] at h8
      exact Nat.pow_right_injective (le_refl 2) (by simpa using h8)
    obtain ⟨x, hx⟩ := h3 hd3
    exact ⟨φ (Multiplicative.ofAdd x), hx⟩

end CFSG.Quasithin.Vol2.A128
