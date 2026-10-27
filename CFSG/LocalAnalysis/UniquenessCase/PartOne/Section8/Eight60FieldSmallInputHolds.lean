module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight60FieldAssembly
import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.Milestones.ASVolI.A3Spor.Out

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

private theorem eight60FieldSmall_odd {X : Type} [Group X] (α : MulAut X)
    (h : IsPGroup 3 (Subgroup.zpowers α)) : Odd (orderOf α) := by
  obtain ⟨k, hk⟩ := h ⟨α, Subgroup.mem_zpowers α⟩
  have hpow : α ^ 3 ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hpow)
  rw [hj]
  exact Odd.pow (by decide)

private theorem eight60FieldSmall_mem_inner {X : Type} [Group X] {α : MulAut X}
    (h : ∃ l : X, α = MulAut.conj l) : α ∈ inner X := by
  obtain ⟨l, rfl⟩ := h
  exact ⟨l, rfl⟩

private theorem eight60FieldSmall_factorization {N : ℕ} (hN0 : N ≠ 0) (h1 : 3 ^ 2 ∣ N)
    (h2 : ¬ 3 ^ 3 ∣ N) : N.factorization 3 = 2 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have a := (hp.pow_dvd_iff_le_factorization hN0).1 h1
  have b : ¬ 3 ≤ N.factorization 3 := fun h => h2 ((hp.pow_dvd_iff_le_factorization hN0).2 h)
  omega

private theorem eight60FieldSmall_sylow {X : Type} [Group X] [Finite X] {N : ℕ}
    (hN : Nat.card X = N) (h3 : N.factorization 3 = 2) :
    ∀ Q : Sylow 3 X, ∀ x ∈ (Q : Subgroup X), ∀ y ∈ (Q : Subgroup X), x * y = y * x := by
  intro Q x hx y hy
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (Q : Subgroup X) = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hN, h3]
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

private theorem eight60FieldSmall_center {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hN : ¬ (Nat.card X).Prime) : ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hnonab : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    have h' : ∀ a b : X, a * b = b * a := fun a b => by
      by_contra hab
      exact h ⟨a, b, hab⟩
    let : CommGroup X := { ‹Group X› with mul_comm := h' }
    exact hN (CommGroup.is_simple_iff_prime_card.1 inferInstance)
  rw [CFSG.ComponentClassification.Helpers.center_eq_bot X hnonab]
  simp

private theorem eight60FieldSmall_conclude {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {N : ℕ} (hodd : ∀ α : MulAut X, Odd (orderOf α) → ∃ l : X, α = MulAut.conj l)
    (hN : Nat.card X = N) (h1 : 3 ^ 2 ∣ N) (h2 : ¬ 3 ^ 3 ∣ N) (hnp : ¬ N.Prime) :
    (∀ α : MulAut X, IsPGroup 3 (Subgroup.zpowers α) → α ∈ inner X) ∧
    (∀ Q : Sylow 3 X, ∀ x ∈ (Q : Subgroup X), ∀ y ∈ (Q : Subgroup X), x * y = y * x) ∧
    ¬ 3 ∣ Nat.card (Subgroup.center X) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact Nat.card_pos.ne' hN
  refine ⟨fun α hα => eight60FieldSmall_mem_inner (hodd α (eight60FieldSmall_odd α hα)),
    eight60FieldSmall_sylow hN (eight60FieldSmall_factorization hN0 h1 h2), ?_⟩
  exact eight60FieldSmall_center (hN ▸ hnp)

theorem eight60FieldSmallInput_holds :
    Eight60FieldSmallInput := by
  intro X _ _ hX
  rcases hX with hM | hM | hM | hM | hM | hM
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (NativeSporadic.Carrier .M11) :=
      CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    have : IsSimpleGroup X := e.isSimpleGroup
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315s_oddInner_M11 e)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11 : Nat.card X = 7920)
      (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    have : IsSimpleGroup X := e.isSimpleGroup
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315s_oddInner_M22 e)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22 : Nat.card X = 443520)
      (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (NativeSporadic.Carrier .M23) :=
      CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2
    have : IsSimpleGroup X := e.isSimpleGroup
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315s_oddInner_M23 e)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.m23_card : Nat.card X = 10200960)
      (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (NativeSporadic.Carrier .HS) :=
      CFSG.Sporadic.HS.fam_hs_simplicity.2.2
    have : IsSimpleGroup X := e.isSimpleGroup
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315s_oddInner_HS e)
      ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.HS.card_HS : Nat.card X = 44352000)
      (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup X := e.isSimpleGroup
    have hN : Nat.card X = 2520 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315x_out_alt (by norm_num)
      (by norm_num) e) hN (by norm_num) (by norm_num) (by norm_num)
  · obtain ⟨e⟩ := hM
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup X := e.isSimpleGroup
    have hN : Nat.card X = 360 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    exact eight60FieldSmall_conclude (CFSG.ASVolI.burnsideA315x_out_alt (by norm_num)
      (by norm_num) e) hN (by norm_num) (by norm_num) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
