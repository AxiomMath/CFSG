module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8IotaBN1

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {Δ : Type*} [Group Δ]

@[expose] def altW (r r' : Δ) : ℕ → Δ
  | 0 => 1
  | k + 1 => r * altW r' r k

theorem altW_zero (r r' : Δ) : altW r r' 0 = 1 := rfl

@[expose] def InCellsGen (B : Subgroup Δ) (s t : Δ) (m : ℕ) (x : Δ) : Prop :=
  ∃ k ≤ m, InCell B (altW s t k) x ∨ InCell B (altW t s k) x

theorem InCellsGen.symm {B : Subgroup Δ} {s t x : Δ} {m : ℕ} (h : InCellsGen B s t m x) :
    InCellsGen B t s m x := by
  obtain ⟨k, hk, h | h⟩ := h
  · exact ⟨k, hk, Or.inr h⟩
  · exact ⟨k, hk, Or.inl h⟩

theorem InCellsGen.lmul {B : Subgroup Δ} {s t x b : Δ} {m : ℕ} (hb : b ∈ B)
    (h : InCellsGen B s t m x) : InCellsGen B s t m (b * x) := by
  obtain ⟨k, hk, h | h⟩ := h
  · exact ⟨k, hk, Or.inl (h.lmul hb)⟩
  · exact ⟨k, hk, Or.inr (h.lmul hb)⟩

theorem inCellsGen_one (B : Subgroup Δ) (s t : Δ) (m : ℕ) : InCellsGen B s t m 1 :=
  ⟨0, Nat.zero_le _, Or.inl (inCell_one_iff.2 B.one_mem)⟩

structure BNPairGen (B P₁ P₂ : Subgroup Δ) (s t : Δ) (us ut : List Δ) (m : ℕ) : Prop where
  r1 : RankOne B P₁ s us
  r2 : RankOne B P₂ t ut
  hm : 1 ≤ m
  braid : altW s t m = altW t s m
  us_chain : ∀ k < m, ∀ u ∈ us, (altW t s k)⁻¹ * u * altW t s k ∈ B
  ut_chain : ∀ k < m, ∀ u ∈ ut, (altW s t k)⁻¹ * u * altW s t k ∈ B

namespace BNPairGen

variable {B P₁ P₂ : Subgroup Δ} {s t : Δ} {us ut : List Δ} {m : ℕ}

theorem symm (H : BNPairGen B P₁ P₂ s t us ut m) : BNPairGen B P₂ P₁ t s ut us m :=
  ⟨H.r2, H.r1, H.hm, H.braid.symm, H.ut_chain, H.us_chain⟩

theorem mul_s (H : BNPairGen B P₁ P₂ s t us ut m) {x : Δ} (hx : InCellsGen B s t m x) :
    InCellsGen B s t m (s * x) := by
  obtain ⟨k, hk, h | h⟩ := hx
  ·
    rcases k with _ | j
    · exact ⟨1, H.hm, Or.inl ((H.r1.up (n := 1) (by simpa using H.r1.U_mem) h).congr
        (by simp [altW]))⟩
    · rcases H.r1.down (n' := altW t s j) (H.us_chain j (by omega)) h with h2 | h2
      · exact ⟨j, by omega, Or.inr h2⟩
      · exact ⟨j + 1, hk, Or.inl h2⟩
  ·
    rcases lt_or_eq_of_le hk with hlt | rfl
    · exact ⟨k + 1, hlt, Or.inl (H.r1.up (H.us_chain k hlt) h)⟩
    · rw [← H.braid] at h
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := H.hm; omega⟩
      rcases H.r1.down (n' := altW t s j) (H.us_chain j (by omega)) h with h2 | h2
      · exact ⟨j, by omega, Or.inr h2⟩
      · exact ⟨j + 1, le_rfl, Or.inl h2⟩

theorem mul_t (H : BNPairGen B P₁ P₂ s t us ut m) {x : Δ} (hx : InCellsGen B s t m x) :
    InCellsGen B s t m (t * x) :=
  (H.symm.mul_s hx.symm).symm

end BNPairGen

end CFSG.Quasithin.H13.F431.U42Aut
