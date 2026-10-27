module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

variable {X : Type*} [Group X]

structure IsStrothInvolution (t : X) (a : ℕ) : Prop where
  orderOf_eq_two : orderOf t = 2
  orderOf_mul_conj (g : X) :
    orderOf (t * (g * t * g⁻¹)) ∣ 4 ∨ Odd (orderOf (t * (g * t * g⁻¹)))
  isConj_sq (g : X) : orderOf (t * (g * t * g⁻¹)) = 4 → IsConj ((t * (g * t * g⁻¹)) ^ 2) t
  dvd_of_inv (g : X) (y : ℕ) : 1 ≤ y → orderOf g = 2 ^ y + 1 → t * g * t⁻¹ = g⁻¹ → y ∣ a

structure IsA2PlaneKernel (t : X) (a : ℕ) (N : Subgroup X) : Prop where
  le_centralizer : N ≤ Subgroup.centralizer {t}
  conj_mem (c : X) : c ∈ Subgroup.centralizer {t} → ∀ h ∈ N, c * h * c⁻¹ ∈ N
  radical (S : Set X) (P R : Subgroup X) : (∀ s ∈ S, ∃ k : ℕ, s ^ 2 ^ k = 1) →
    Subgroup.closure S = P → P ≤ Subgroup.centralizer {t} → R ≤ P →
    (∀ p ∈ P, ∀ r ∈ R, p * r * p⁻¹ ∈ R) → IsPGroup 2 R → R ≤ N ∨ ⁅P, P⁆ ≤ N
  card_dvd (L : Subgroup X) : L ≤ Subgroup.centralizer {t} → L ⊓ N = ⊥ →
    Nat.card L ∣ 2 ^ a * (2 ^ a - 1) * (2 ^ (2 * a) - 1)

structure IsKLConfig (t : X) (a : ℕ) (N A : Subgroup X) : Prop where
  involution : IsStrothInvolution t a
  kernel : IsA2PlaneKernel t a N
  isPGroup : IsPGroup 2 A
  comm (x : X) : x ∈ A → ∀ y ∈ A, x * y = y * x
  mem : t ∈ A
  conj_mem (h : X) : h ∈ N → ∀ x ∈ A, h * x * h⁻¹ ∈ A
  eq_one (h : X) : h ∈ N → Odd (orderOf h) → (∀ x ∈ A, h * x = x * h) → h = 1

structure IsLBImage (t : X) (a n : ℕ) (N : Subgroup X) (E : Subgroup (MulAut X)) : Prop where
  sq_eq_one (e : MulAut X) : e ∈ E → e ^ 2 = 1
  conj_mem : MulAut.conj t ∈ E
  conj_conj_mem (h : X) : h ∈ N → ∀ e ∈ E, MulAut.conj h * e * (MulAut.conj h)⁻¹ ∈ E
  card_le : 2 ^ (a * (n - 2)) ≤ Nat.card E

end CFSG.RankThree.GF2n.Stroth80
