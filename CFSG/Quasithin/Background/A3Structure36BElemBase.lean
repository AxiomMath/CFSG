
module

public import CFSG.Quasithin.Background.A3Structure36BNilpotent

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem exists_involution (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    ∃ t : X, t ∈ CFSG.solvableRadical X ∧ t ^ 2 = 1 ∧ t ∉ K := by
  have hfin : Finite X := h.finite
  have h2 : 2 ∣ Nat.card (CFSG.solvableRadical X) := by
    have := Subgroup.relIndex_dvd_card K (CFSG.solvableRadical X)
    rwa [hK.data.relIndex] at this
  have hf2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.solvableRadical X)) 2 h2
  refine ⟨(t : X), t.2, ?_, ?_⟩
  · have h3 := pow_orderOf_eq_one t
    rw [ht] at h3
    exact congrArg Subtype.val h3
  · intro htK
    have hKF : K = CFSG.fittingSubgroup X := kernel_eq_fitting h hK
    have hodd : Odd (Nat.card K) := hKF ▸ odd_card_fitting h
    have hdvd : orderOf (t : X) ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K htK
    rw [Subgroup.orderOf_coe, ht] at hdvd
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hdvd)

theorem IsElemAbelianOfRank.comm_pow {q n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank q n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ q = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

end CFSG.Quasithin.A36B
