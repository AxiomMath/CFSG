module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.GroupTheory.GroupAction.Defs

public section

namespace CFSG.Sporadic.Co1.Module

open MulAction

section PermChar

variable {G Ω : Type*} [Group G] [MulAction G Ω]

theorem card_centralizer_mul_ncard_le [Finite G] {ω₀ : Ω} {s : G} {S : Set G}
    (hS₁ : ∀ t ∈ S, t ∈ stabilizer G ω₀) (hS₂ : ∀ t ∈ S, IsConj s t) :
    Nat.card (Subgroup.centralizer ({s} : Set G)) * S.ncard ≤
      Nat.card (stabilizer G ω₀) * {ω ∈ orbit G ω₀ | s • ω = ω}.ncard := by
  classical
  have hx : ∀ t : S, ∃ x : G, x⁻¹ * s * x = t.1 := by
    intro t
    obtain ⟨c, hc⟩ := isConj_iff.1 (hS₂ t.1 t.2)
    exact ⟨c⁻¹, by simpa using hc⟩
  choose x hx using hx
  have hy : ∀ ω : {ω ∈ orbit G ω₀ | s • ω = ω}, ∃ y : G, y • ω₀ = ω.1 := by
    intro ω
    exact (mem_orbit_iff.1 ω.2.1)
  choose y hy using hy
  have hfin : Finite {ω ∈ orbit G ω₀ | s • ω = ω} :=
    ((Set.finite_range (fun g : G => g • ω₀)).subset (fun ω hω => hω.1)).to_subtype
  let g : Subgroup.centralizer ({s} : Set G) × S → G := fun p => p.1.1 * x p.2
  have hg : ∀ p, (g p)⁻¹ * s * g p = p.2.1 := by
    intro p
    have hz : p.1.1⁻¹ * s * p.1.1 = s := by
      have := Subgroup.mem_centralizer_iff.1 p.1.2 s (Set.mem_singleton s)
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (g p)⁻¹ * s * g p = (x p.2)⁻¹ * (p.1.1⁻¹ * s * p.1.1) * x p.2 := by
          simp only [g, mul_inv_rev, mul_assoc]
      _ = p.2.1 := by rw [hz]; exact hx p.2
  have hfix : ∀ p, s • (g p • ω₀) = g p • ω₀ := by
    intro p
    have h1 : s * g p = g p * p.2.1 := by
      have h := hg p
      generalize g p = u at h ⊢
      rw [← h]
      simp [mul_assoc]
    rw [← mul_smul, h1, mul_smul, mem_stabilizer_iff.1 (hS₁ p.2.1 p.2.2)]
  let ω : Subgroup.centralizer ({s} : Set G) × S → {ω ∈ orbit G ω₀ | s • ω = ω} := fun p =>
    ⟨g p • ω₀, mem_orbit _ _, hfix p⟩
  have hstab : ∀ p, (y (ω p))⁻¹ * g p ∈ stabilizer G ω₀ := by
    intro p
    rw [mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
    exact (hy (ω p)).symm
  let F : Subgroup.centralizer ({s} : Set G) × S →
      {ω ∈ orbit G ω₀ | s • ω = ω} × stabilizer G ω₀ := fun p =>
    (ω p, ⟨(y (ω p))⁻¹ * g p, hstab p⟩)
  have hF : Function.Injective F := by
    intro p q h
    have h1 : ω p = ω q := congrArg Prod.fst h
    have h2 : (y (ω p))⁻¹ * g p = (y (ω q))⁻¹ * g q := congrArg (fun r => (r.2 : G)) h
    rw [h1] at h2
    have h3 : g p = g q := mul_left_cancel h2
    have h4 : p.2 = q.2 := by
      apply Subtype.ext
      rw [← hg p, ← hg q, h3]
    have h5 : x p.2 = x q.2 := by rw [h4]
    have h6 : p.1.1 = q.1.1 := by
      have : p.1.1 * x p.2 = q.1.1 * x q.2 := h3
      rw [h5] at this
      exact mul_right_cancel this
    exact Prod.ext (Subtype.ext h6) h4
  have := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this
  rw [mul_comm (Nat.card (stabilizer G ω₀))]
  exact this

end PermChar

end CFSG.Sporadic.Co1.Module
