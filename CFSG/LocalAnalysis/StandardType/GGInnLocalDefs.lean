module

public import CFSG.LocalAnalysis.StandardType.GGStdSubExistDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Outdiag

variable {R : Type} [Group R]

@[expose] def GGOutdiagOdd (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∃ D : Subgroup (MulAut R), D.Normal ∧ (∀ φ ∈ I, φ ^ p = 1 → φ ∈ D) ∧
    Odd ((MulAut.conj : R →* MulAut R).range.relIndex D)

@[expose] def GGOutdiagPrime (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ φ ∈ I, φ ^ p = 1 → φ ∈ (MulAut.conj : R →* MulAut R).range

theorem ggOutdiagOdd_of_prime {p : ℕ} {I : Set (MulAut R)} (h : GGOutdiagPrime p R I) :
    GGOutdiagOdd p R I :=
  ⟨_, inferInstance, h, by rw [Subgroup.relIndex_self]; exact odd_one⟩

theorem mem_range_conj_of_pow_two_pow {D : Subgroup (MulAut R)}
    (hodd : Odd ((MulAut.conj : R →* MulAut R).range.relIndex D)) {φ : MulAut R} (hφ : φ ∈ D)
    {k : ℕ} (hk : φ ^ 2 ^ k = 1) : φ ∈ (MulAut.conj : R →* MulAut R).range := by
  set N := (MulAut.conj : R →* MulAut R).range with hN
  have h1 : (⟨φ, hφ⟩ : D) ^ (N.subgroupOf D).index ∈ N.subgroupOf D :=
    Subgroup.pow_index_mem _ _
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h1
  have hcop : Nat.Coprime (N.relIndex D) (orderOf φ) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hk)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ h1 m

end Outdiag

@[expose] def GGDeltaAdm (p : ℕ) (L' : Type) [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  (∀ e : L', e ^ p = 1 → (∀ a ∈ A, a e = e) → MulAut.conj e ∈ A) ∧
    (((∃ a ∈ A, a ∉ (MulAut.conj : L' →* MulAut L').range) ∧
        ∀ E : Subgroup L', IsElemAbelian p E → Nat.card E ≤ Nat.card A) ∨
      (p ∣ Nat.card (Subgroup.center L') ∧
        (∀ E : Subgroup L', IsElemAbelian p E → Nat.card E ≤ p * Nat.card A) ∧
        ∃ a ∈ A, a ∉ (MulAut.conj : L' →* MulAut L').range ∨
          ∀ l : L', MulAut.conj l = a → p ∣ orderOf (l ^ p)))

@[expose] def GGDeltaLocal (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGDeltaAdm p L' A →
      ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a u ∈ U

@[expose] def GGBstarBoundDelta (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A Ah : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGDeltaAdm p L' A →
      A ≤ Ah → IsElemAbelian p Ah → Nat.card Ah ≤ p * Nat.card A

@[expose] def GGCenterPrime (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → ¬ p ∣ Nat.card (Subgroup.center L')

end CFSG.StandardType
