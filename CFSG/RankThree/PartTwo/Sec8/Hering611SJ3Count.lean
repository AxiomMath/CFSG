module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

theorem card_range_and_map {A' J : Type*} [Group A'] [Group J] [Finite A'] (Φ : A' →* J)
    (hA : Nat.card A' = 81) (hker : Nat.card Φ.ker = 3) (B : Subgroup A') (hB : Nat.card B = 9)
    (hBker : Disjoint B Φ.ker) : Nat.card Φ.range = 27 ∧ Nat.card (B.map Φ) = 9 := by
  constructor
  · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Φ.ker
    have h2 : Nat.card (A' ⧸ Φ.ker) = Nat.card Φ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Φ).toEquiv
    rw [hA, hker, h2] at h1
    omega
  · have hinj : Function.Injective (Φ.comp B.subtype) := by
      rw [injective_iff_map_eq_one]
      intro b hb
      have h1 : (b : A') ∈ B ⊓ Φ.ker := ⟨b.2, hb⟩
      rw [disjoint_iff.mp hBker, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    have hrange : (Φ.comp B.subtype).range = B.map Φ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hB]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isElemAbelian_range {A' J : Type*} [Group A'] [Group J] (Φ : A' →* J)
    (hcomm : ∀ x y : A', x * y = y * x) (hexp : ∀ x : A', x ^ 3 = 1) :
    (∀ x y : Φ.range, x * y = y * x) ∧ ∀ x : Φ.range, x ^ 3 = 1 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp y.2
    apply Subtype.ext
    show (x : J) * (y : J) = (y : J) * (x : J)
    rw [← ha, ← hb, ← map_mul, ← map_mul, hcomm a b]
  · obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp x.2
    apply Subtype.ext
    show (x : J) ^ 3 = 1
    rw [← ha, ← map_pow, hexp a, map_one]

end CFSG.RankThree.PartTwo.Sec8.Hering611
