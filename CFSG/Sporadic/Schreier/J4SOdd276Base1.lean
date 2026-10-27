
module

public import CFSG.Sporadic.Schreier.J4SOdd276Base

public import CFSG.Sporadic.Schreier.J4SOddLocalBase1
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SFiveBase1
public import CFSG.Sporadic.Schreier.J4SPointwise
public meta import CFSG.Sporadic.J4.PrimSpec
public import Certificates.Certificate2177
public import CFSG.Sporadic.Schreier.J4SOddData
public meta import CFSG.Sporadic.Schreier.J4SOddData
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SPrimes
public meta import CFSG.Sporadic.Schreier.J4SPrimes
public import CFSG.Sporadic.Schreier.J4SThreeDataInputs
public meta import CFSG.Sporadic.Schreier.J4SKCent
public import CFSG.Sporadic.J4.Local

@[expose] public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2.Native

theorem a276_acts :
    ActsBy a276 (wordCols a276Word) := word_conj_η_cols a276Word

theorem a276_mem_centralizer :
    a276 ∈ Subgroup.centralizer {η 14} := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h : a276 * η 14 * a276⁻¹ = η 14 := by rw [a276_acts, a276_check.2.2.1]
  calc a276 * η 14 = a276 * η 14 * a276⁻¹ * a276 := by group
    _ = η 14 * a276 := by rw [h]

theorem a276_fix
    {b : J} (hb : b ∈ N) (h : a276 * b * a276⁻¹ = b) : b = 1 ∨ b = η 14 := by
  obtain ⟨n, hn, rfl⟩ := exists_η_eq hb
  rw [a276_acts] at h
  have hlt : app11 (wordCols a276Word) n < 2 ^ 11 :=
    vecMulN_lt (fun j hj => by rw [← getElem!_eq_getD']; exact a276_check.1.2 j hj) n
  rcases a276_check.2.2.2 n hn (η_injOn hlt hn h) with rfl | rfl
  · exact Or.inl η_zero
  · exact Or.inr rfl

theorem conj_inv_mem_N
    {k n : J} (hk : k ∈ K) (hn : n ∈ N) : k⁻¹ * n * k ∈ N := by
  have h := conj_mem_N_of_mem_H k⁻¹ (K_le_H (K.inv_mem hk)) n hn
  rwa [inv_inv] at h

theorem card_le_of_dvd_two_pow {B : Subgroup J} (hB : B ≤ N) :
    ∃ k ≤ 11, Nat.card B = 2 ^ k := by
  have h := Subgroup.card_dvd_of_le hB
  rw [card_N] at h
  exact (Nat.dvd_prime_pow Nat.prime_two).1 h

end CFSG.Sporadic.J4Schreier
