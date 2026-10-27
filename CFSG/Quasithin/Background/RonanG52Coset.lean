module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin.RonanG52

lemma bijective_out_mul {G : Type} [Group G] (P : Subgroup G) :
    Function.Bijective (fun x : (G ⧸ P) × P => Quotient.out x.1 * (x.2 : G)) := by
  constructor
  · rintro ⟨q, p⟩ ⟨q', p'⟩ h
    have h' : Quotient.out q * (p : G) = Quotient.out q' * (p' : G) := h
    have hq : q = q' := by
      have h1 : (QuotientGroup.mk (Quotient.out q * (p : G)) : G ⧸ P) =
          QuotientGroup.mk (Quotient.out q' * (p' : G)) := congrArg QuotientGroup.mk h'
      rw [QuotientGroup.mk_mul_of_mem _ p.2, QuotientGroup.mk_mul_of_mem _ p'.2,
        QuotientGroup.out_eq', QuotientGroup.out_eq'] at h1
      exact h1
    subst hq
    rw [Subtype.ext (mul_left_cancel h')]
  · intro g
    exact ⟨((g : G ⧸ P), ⟨(Quotient.out (g : G ⧸ P))⁻¹ * g,
      QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : G ⧸ P))⟩), mul_inv_cancel_left _ _⟩

theorem sum_conj_eq_id_of_odd_index {k G V : Type} [Field k] [CharP k 2] [Group G] [Fintype G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (P : Subgroup G) (S : Finset G)
    (hS : ∀ x, x ∈ S ↔ x ∈ P) (hodd : ¬ 2 ∣ P.index) (φ : V →ₗ[k] V)
    (h : ∑ p ∈ S, ρ p ∘ₗ φ ∘ₗ ρ p⁻¹ = LinearMap.id) :
    ∑ g : G, ρ g ∘ₗ φ ∘ₗ ρ g⁻¹ = LinearMap.id := by
  classical
  have h2 : ∑ p ∈ S, ρ p * (φ * ρ p⁻¹) = 1 := h
  have hP : ∑ p : P, ρ (p : G) * (φ * ρ (p : G)⁻¹) = 1 :=
    (Finset.sum_subtype S hS (fun x : G => ρ x * (φ * ρ x⁻¹))).symm.trans h2
  have hconj : ∀ x p : G, ρ (x * p) * (φ * ρ (x * p)⁻¹) =
      ρ x * (ρ p * (φ * ρ p⁻¹)) * ρ x⁻¹ := by
    intro x p
    simp only [map_mul, mul_inv_rev, mul_assoc]
  have hq : ∀ q : G ⧸ P, ∑ p : P, ρ (Quotient.out q * (p : G)) *
      (φ * ρ (Quotient.out q * (p : G))⁻¹) = 1 := by
    intro q
    simp only [hconj]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hP, mul_one, ← map_mul, mul_inv_cancel, map_one]
  have hcard : ((P.index : ℕ) : k) = 1 := by
    obtain ⟨m, hm⟩ : Odd P.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    have h2' : (2 : k) = 0 := by exact_mod_cast CharP.cast_eq_zero k 2
    rw [hm]
    push_cast
    rw [h2']
    simp
  have hend : ((P.index : ℕ) : Module.End k V) = 1 := by
    have := map_natCast (algebraMap k (Module.End k V)) P.index
    rw [hcard, map_one] at this
    exact this.symm
  show ∑ g : G, ρ g * (φ * ρ g⁻¹) = 1
  calc ∑ g : G, ρ g * (φ * ρ g⁻¹)
      = ∑ x : (G ⧸ P) × P, ρ (Quotient.out x.1 * (x.2 : G)) *
          (φ * ρ (Quotient.out x.1 * (x.2 : G))⁻¹) :=
        (Equiv.sum_comp (Equiv.ofBijective _ (bijective_out_mul P))
          (fun g : G => ρ g * (φ * ρ g⁻¹))).symm
    _ = ∑ q : G ⧸ P, ∑ p : P, ρ (Quotient.out q * (p : G)) *
          (φ * ρ (Quotient.out q * (p : G))⁻¹) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ _q : G ⧸ P, (1 : Module.End k V) := Finset.sum_congr rfl fun q _ => hq q
    _ = (Fintype.card (G ⧸ P) : Module.End k V) := by simp
    _ = (P.index : Module.End k V) := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    _ = 1 := hend

end CFSG.Quasithin.RonanG52
