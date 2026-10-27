module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base
public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.Fan86

namespace Sec8P3

variable {G : Type*} [Group G]

theorem fcomm_mem_of_gens (N : Subgroup G) (S : Set G)
    (hnorm : ∀ a ∈ Subgroup.closure S, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (hS : ∀ s ∈ S, ∀ t ∈ S, fcomm s t ∈ N) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, fcomm a b ∈ N := by
  have hnorm' : ∀ a ∈ Subgroup.closure S, ∀ n ∈ N, a⁻¹ * n * a ∈ N := fun a ha n hn => by
    simpa using hnorm a⁻¹ (inv_mem ha) n hn
  have h1 : ∀ s ∈ S, ∀ b ∈ Subgroup.closure S, fcomm s b ∈ N := by
    intro s hs b hb
    refine Subgroup.closure_induction (p := fun b _ => fcomm s b ∈ N) ?_ ?_ ?_ ?_ hb
    · intro t ht
      exact hS s hs t ht
    · simp [fcomm]
    · intro b b' hb hb' ih ih'
      have e : fcomm s (b * b') = fcomm s b' * (b'⁻¹ * fcomm s b * b') := by
        unfold fcomm
        group
      rw [e]
      exact mul_mem ih' (hnorm' b' hb' _ ih)
    · intro b hb ih
      have e : fcomm s b⁻¹ = b * (fcomm s b)⁻¹ * b⁻¹ := by
        unfold fcomm
        group
      rw [e]
      exact hnorm b hb _ (inv_mem ih)
  intro a ha b hb
  refine Subgroup.closure_induction (p := fun a _ => fcomm a b ∈ N) ?_ ?_ ?_ ?_ ha
  · intro s hs
    exact h1 s hs b hb
  · simp [fcomm]
  · intro a a' ha ha' ih ih'
    have e : fcomm (a * a') b = a'⁻¹ * fcomm a b * a' * fcomm a' b := by
      unfold fcomm
      group
    rw [e]
    exact mul_mem (hnorm' a' ha' _ ih) ih'
  · intro a ha ih
    have e : fcomm a⁻¹ b = a * (fcomm a b)⁻¹ * a⁻¹ := by
      unfold fcomm
      group
    rw [e]
    exact hnorm a ha _ (inv_mem ih)

theorem bot_normalized (S : Set G) :
    ∀ a ∈ Subgroup.closure S, ∀ n ∈ (⊥ : Subgroup G), a * n * a⁻¹ ∈ (⊥ : Subgroup G) := by
  intro a _ n hn
  rw [Subgroup.mem_bot.1 hn]
  simp

theorem mul_self_mem_of_gens (N : Subgroup G) (S : Set G)
    (hnorm : ∀ a ∈ Subgroup.closure S, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (hcomm : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, fcomm a b ∈ N)
    (hS : ∀ s ∈ S, s * s ∈ N) : ∀ a ∈ Subgroup.closure S, a * a ∈ N := by
  have hnorm' : ∀ a ∈ Subgroup.closure S, ∀ n ∈ N, a⁻¹ * n * a ∈ N := fun a ha n hn => by
    simpa using hnorm a⁻¹ (inv_mem ha) n hn
  intro a ha
  refine Subgroup.closure_induction (p := fun a _ => a * a ∈ N) ?_ ?_ ?_ ?_ ha
  · exact hS
  · simp
  · intro a b ha hb iha ihb
    have e : (a * b) * (a * b) = (a * a) * (b * b) * (b⁻¹ * fcomm b a * b) := by
      unfold fcomm
      group
    rw [e]
    exact mul_mem (mul_mem iha ihb) (hnorm' b hb _ (hcomm b hb a ha))
  · intro a ha iha
    have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
    rw [e]
    exact inv_mem iha

end Sec8P3

end CFSG.Quasithin.Fan86
