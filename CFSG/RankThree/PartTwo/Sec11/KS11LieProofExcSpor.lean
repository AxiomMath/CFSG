module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofExc
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofField

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open Matrix

@[expose] def SporAutPowThree : Prop :=
  ∀ (Z : Type) [Group Z] [Finite Z],
    (∃ (X : Type) (_ : Group X), (Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
      Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.He)) ∧
        Nonempty (Z ≃* _root_.commutator X)) →
    ∀ β : MulAut Z, (∃ k : ℕ, β ^ 3 ^ k = 1) → β ^ 3 = 1

namespace KS11LieProof

theorem three_dvd_card_projImage {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) : 3 ∣ Nat.card (projImage (slPi π 3 (p ^ f) K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  set x := projOf (slPi π 3 (p ^ f) K) ⟨cycThree, cycThree_mem_slPi hπ⟩ with hx
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨cycThree, cycThree_mem_slPi hπ⟩ : slPi π 3 (p ^ f) K) ^ 3 = 1 :=
      Subtype.ext cycThree_pow_three
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := congrArg (fun y : projImage (slPi π 3 (p ^ f) K) =>
      (y : ProjGenLinGroup (Fin 3) K)) h
    change ProjGenLinGroup.mk cycThree = 1 at h1
    obtain ⟨z, hz⟩ := mk_eq_one_iff_mem_statedScalars.mp h1
    have := congrFun (congrFun (congrArg (fun A : GL (Fin 3) K =>
      (A : Matrix (Fin 3) (Fin 3) K)) hz) 0) 0
    simp [GeneralLinearGroup.coe_scalar, coe_cycThree] at this
  have h := orderOf_dvd_natCard x
  rwa [orderOf_eq_prime hx3 hx1] at h

theorem three_dvd_card_of_isType424 {X : Type} [Group X] (h : IsType424 X) :
    3 ∣ Nat.card X := by
  rcases h with ⟨n, -, ⟨e⟩⟩ | ⟨p, n, hp, -, -, ⟨e⟩⟩ | ⟨n, hn, h⟩
  · rw [Nat.card_congr (e.trans (Sec4.projSLEquivPSL _)).toEquiv]
    exact KFacts.three_dvd_card_psl2 _
  · rw [Nat.card_congr (e.trans (Sec4.projSLEquivPSL _)).toEquiv]
    exact KFacts.three_dvd_card_psl2 _
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rcases h with ⟨-, ⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩
    · rw [Nat.card_congr φ.toEquiv, Sec13.projSU_eq]
      exact three_dvd_card_projImage (Sec13.piField_galoisField_two 2 n hn)
    · rw [Nat.card_congr φ.toEquiv, Sec13.projSL_eq]
      exact three_dvd_card_projImage (Sec13.piField_galoisField 2 n hn)

end KS11LieProof

theorem centAut119Spor_of (h : SporAutPowThree) : CentAut119Spor := by
  intro Z _ _ hZ α β J _ hβ _ _ hJT _
  have hβ3 := h Z hZ β hβ
  have h3J : 3 ∣ Nat.card J :=
    (KS11LieProof.three_dvd_card_of_isType424 hJT).trans
      (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 J))
  have hv : 1 ≤ (Nat.card J).factorization 3 :=
    (Nat.prime_three.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h3J
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hv
  rw [hr, pow_add, pow_one, pow_mul, hβ3, one_pow]

theorem centBound119Spor_of_sporAutPowThree (h : SporAutPowThree) : CentBound119Spor :=
  centBound119Spor_of (centAut119Spor_of h)

end CFSG.RankThree.PartTwo.Sec11
