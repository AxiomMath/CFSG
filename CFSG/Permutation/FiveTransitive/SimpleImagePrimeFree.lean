module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG

namespace FiveTransitive.SimpleImagePrimeFree

theorem simple_card_dvd
    (L A B : Type) [Group L] [Group A] [Group B]
    [Finite L] [Finite A] [Finite B]
    (f : L →* A) (g : L →* B) (Q : Subgroup A) [IsSimpleGroup Q]
    (hQ : Q ≤ f.range) (p : ℕ) (hp : p.Prime)
    (hker : ¬ p ∣ Nat.card (f.ker.map g))
    (a : L) (ha : f a ∈ Q) (k : ℕ) (hpow : a ^ (p ^ k) = 1)
    (hne : g a ≠ 1) :
    Nat.card Q ∣ Nat.card g.range := by
  by_contra hnot
  obtain ⟨c, hc, hgc⟩ := SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
    L A B f g Q hQ hnot (f a) ha
  have hac : a * c⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
  have hz : g a ∈ f.ker.map g :=
    Subgroup.mem_map.mpr ⟨a * c⁻¹, hac, by simp only [map_mul, map_inv, hgc, inv_one, mul_one]⟩
  let z : f.ker.map g := ⟨g a, hz⟩
  have hzpow : z ^ (p ^ k) = 1 := by
    apply Subtype.ext
    change (g a) ^ (p ^ k) = 1
    rw [← map_pow, hpow, map_one]
  have hcop : (Nat.card (f.ker.map g)).Coprime (p ^ k) :=
    ((hp.coprime_iff_not_dvd.mpr hker).symm).pow_right k
  have hord : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_natCard z) (orderOf_dvd_of_pow_eq_one hzpow)
  exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp hord))

end FiveTransitive.SimpleImagePrimeFree

end CFSG
