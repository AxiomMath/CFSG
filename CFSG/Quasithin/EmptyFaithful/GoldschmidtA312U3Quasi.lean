module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Core
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3IrrRed
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Five
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Klein

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists

structure QCtx (p : ℕ) (K : Type) [Field K] (M : Subgroup ↥(StatedSU 3 (p ^ 1) K))
    (H : Subgroup (GL (Fin 3) K)) : Prop where
  odd : Odd M.index
  le : H ≤ M.map (StatedSU 3 (p ^ 1) K).subtype
  norm : ∀ g ∈ M.map (StatedSU 3 (p ^ 1) K).subtype, ∀ x ∈ H, g * x * g⁻¹ ∈ H
  quasi : CFSG.IsQuasisimple H
  irr : IsIrreducibleMatrixRep H.subtype
  scalar : ∀ A : Matrix (Fin 3) (Fin 3) K,
    (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * A = A * x) → ∃ c : K, A = Matrix.scalar (Fin 3) c
  det : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1
  center : Nat.card (Subgroup.center H) ∣ 3

@[expose] def SU3NoPSL3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ (M : Subgroup ↥(StatedSU 3 (p ^ 1) K)) (H : Subgroup (GL (Fin 3) K)), QCtx p K M H →
      ∀ r f : ℕ, r.Prime → r ≠ 2 → 1 ≤ f → ∀ (K' : Type) [Field K'] [Finite K'],
        Nat.card K' = r ^ f → (H ⧸ Subgroup.center H ≃* StatedProj (StatedSL 3 K')) → False

@[expose] def SU3PSU3Case : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ (M : Subgroup ↥(StatedSU 3 (p ^ 1) K)) (H : Subgroup (GL (Fin 3) K)), QCtx p K M H →
      ∀ r f : ℕ, r.Prime → r ≠ 2 → 1 ≤ f → ∀ (K' : Type) [Field K'] [Finite K'],
        Nat.card K' = (r ^ f) ^ 2 →
          (H ⧸ Subgroup.center H ≃* StatedProj (StatedSU 3 (r ^ f) K')) → M = ⊤

@[expose] def SU3NoPSL2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ (M : Subgroup ↥(StatedSU 3 (p ^ 1) K)) (H : Subgroup (GL (Fin 3) K)), QCtx p K M H →
      ∀ r f : ℕ, r.Prime → r ≠ 2 → 1 ≤ f → StatedLieAdmissible .PSL 2 r f →
        ∀ (K' : Type) [Field K'] [Finite K'], Nat.card K' = r ^ f →
          (H ⧸ Subgroup.center H ≃* StatedProj (StatedSL 2 K')) → False

@[expose] def SU3OddIrrGe7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 7 ≤ p → ∀ (K : Type) [Field K] [Finite K], Nat.card K = p ^ 2 →
    ∀ M : Subgroup ↥(StatedSU 3 (p ^ 1) K), Odd M.index → IsIrrIn (StatedSU 3 (p ^ 1) K) M →
      M = ⊤ ∨ Group.IsSolvable ↥M

@[expose] def SU3OddIrrSmall : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], (p = 3 ∨ p = 5) → ∀ (K : Type) [Field K] [Finite K],
    Nat.card K = p ^ 2 → ∀ M : Subgroup ↥(StatedSU 3 (p ^ 1) K), Odd M.index →
      IsIrrIn (StatedSU 3 (p ^ 1) K) M →
        M = ⊤ ∨ Group.IsSolvable ↥M ∨
          (p = 5 ∧ IsHat ↥(perfectCore M) (alternatingGroup (Fin 6)) ∧
            ∀ z ∈ Subgroup.center ↥(perfectCore M),
              (((z : ↥(perfectCore M)) : ↥(StatedSU 3 (p ^ 1) K)) : GL (Fin 3) K) ∈
                StatedScalars (Fin 3) K)

theorem natCast_ne_zero_of_card_sq {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) {n : ℕ} (hn : n.Prime) (hnp : n ≠ p) : (n : K) ≠ 0 := by
  have := charP_of_card_sq (p := p) hK
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact hnp ((Nat.prime_dvd_prime_iff_eq Fact.out hn).mp h).symm

theorem su3OddIrrGe7_of
    (h4 : SU3NoPSL3) (h5 : SU3PSU3Case) (h6 : SU3NoPSL2) : SU3OddIrrGe7 := by
  intro p hpf hp7 K _ _ hK M hodd hirr
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hoddK : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  rcases solvable_or_quasisimple_gl3 hirr with hsolv | ⟨H, hHG, hnorm, hq, hHirr, hscal, hdet, hZ⟩
  · right
    exact Group.isSolvable_of_isSolvable_injective
      (f := (M.equivMapOfInjective _ (StatedSU 3 (p ^ 1) K).subtype_injective).toMonoidHom)
      (MulEquiv.injective _)
  · have hctx : QCtx p K M H := ⟨hodd, hHG, hnorm, hq, hHirr, hscal, hdet, hZ⟩
    have hK2 : (2 : K) ≠ 0 := by exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_two hp2.symm
    have hK5 : (5 : K) ≠ 0 := by
      exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_five (by omega)
    have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
      pow_three_eq_one_of_mem_center hZ hz
    left
    rcases quotient_center_rank_two_cases hoddK hq hdet hZ with
      ⟨r, f, hr, hr2, hf, hadm, K', _, _, hK', ⟨e⟩⟩ | ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ |
      ⟨r, f, hr, hr2, hf, -, K', _, _, hK', ⟨e⟩⟩ | ⟨-, K', _, _, hK', ⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩
    · exact (h6 p hp7 K hK M H hctx r f hr hr2 hf hadm K' hK' e).elim
    · exact (h4 p hp7 K hK M H hctx r f hr hr2 hf K' hK' e).elim
    · exact h5 p hp7 K hK M H hctx r f hr hr2 hf K' hK' e
    · exact (false_of_psu34_K hK2 hdet hZ hK' e).elim
    · obtain ⟨e⟩ := e
      exact (not_mulEquiv_alternating_seven_K hK5 hdet hZ3 e).elim
    · obtain ⟨e⟩ := e
      exact (not_mulEquiv_m11_K hK5 hdet hZ3 e).elim

theorem su3OddIrr_of (h7 : SU3OddIrrGe7) (hs : SU3OddIrrSmall) : SU3OddIrr := by
  intro p hpf hp2 K _ _ hK M hodd hirr
  have hp : p.Prime := hpf.out
  by_cases hsm : p = 3 ∨ p = 5
  · exact hs p hsm K hK M hodd hirr
  · have hp7 : 7 ≤ p := by
      by_contra h
      push Not at h
      have h2 := hp.two_le
      interval_cases p
      · exact hp2 rfl
      · exact hsm (Or.inl rfl)
      · exact absurd hp (by norm_num)
      · exact hsm (Or.inr rfl)
      · exact absurd hp (by norm_num)
    rcases h7 p hp7 K hK M hodd hirr with htop | hsolv
    · exact Or.inl htop
    · exact Or.inr (Or.inl hsolv)

end CFSG.Quasithin.A312U3
