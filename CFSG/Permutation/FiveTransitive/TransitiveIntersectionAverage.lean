module

public import CFSG.Permutation.FiveTransitive.SupportEightInvolutionClosure

public section

namespace CFSG

namespace FiveTransitive.TransitiveIntersectionAverage

open scoped BigOperators

private theorem sum_card_filter_smul
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [MulAction G Ω]
    [DecidableEq Ω] [MulAction.IsPretransitive G Ω]
    (x₀ : Ω) (A B : Finset Ω) :
    Fintype.card Ω * (∑ g : G, (A.filter fun a => g • a ∈ B).card) =
      Fintype.card G * (A.card * B.card) := by
  classical
  have hstab (x : Ω) :
      Nat.card (MulAction.stabilizer G x) =
        Nat.card (MulAction.stabilizer G x₀) := by
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) x x₀
    exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv
  have hswap :
      (∑ g : G, (A.filter fun a => g • a ∈ B).card) =
        ∑ a ∈ A, (Finset.univ.filter fun g : G => g • a ∈ B).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  simp_rw [SupportEightInvolutionClosure.card_smul_mem_finset, hstab]
  rw [Finset.sum_const_nat (m := B.card * Nat.card (MulAction.stabilizer G x₀))
    (fun _ _ => rfl)]
  have horbit :
      Fintype.card Ω * Fintype.card (MulAction.stabilizer G x₀) = Fintype.card G := by
    simpa [MulAction.orbit_eq_univ G x₀] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x₀
  simp only [Nat.card_eq_fintype_card]
  calc
    Fintype.card Ω * (A.card * (B.card * Fintype.card (MulAction.stabilizer G x₀))) =
      (Fintype.card Ω * Fintype.card (MulAction.stabilizer G x₀)) *
        (A.card * B.card) := by ring
    _ = Fintype.card G * (A.card * B.card) := by rw [horbit]

theorem exists_card_filter_smul_le
    {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [MulAction G Ω]
    [DecidableEq Ω] [MulAction.IsPretransitive G Ω]
    (x₀ : Ω) (A B : Finset Ω) :
    ∃ g : G, Fintype.card Ω * (A.filter fun a => g • a ∈ B).card ≤ A.card * B.card := by
  classical
  by_contra hn
  push Not at hn
  have hstrict := Finset.sum_lt_sum_of_nonempty
    (s := (Finset.univ : Finset G)) Finset.univ_nonempty (fun g _ => hn g)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at hstrict
  rw [sum_card_filter_smul x₀ A B] at hstrict
  exact (Nat.lt_irrefl _ hstrict)

end FiveTransitive.TransitiveIntersectionAverage

end CFSG
