module

public import CFSG.Walter.ReeOrder.Ward.Columns4
public import CFSG.Walter.ReeOrder.Ward.Values

public section

open scoped BigOperators Classical

namespace CFSG.Walter.Ward

open CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct

namespace WardSetup

variable {G : Type} [Group G] [Fintype G] {L : Type} [Group L] [Fintype L] {q : ℕ} {e : ℤ}
  {IV : Bool} (S : WardSetup G L q e IV)

theorem deg_sub_J {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) :
    ∃ k : ℤ, χ 1 - χ S.J = 2 * k := by
  refine ⟨∑ θ ∈ (irreducibles_finite L).toFinset, (S.mb χ θ : ℤ) * deg θ, ?_⟩
  have h1 := S.τ_expand hχ 1
  have h2 := S.σ_expand hχ 1
  simp only [τ, σ, map_one, mul_one] at h1 h2
  rw [h1, h2, ← Finset.sum_sub_distrib]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun θ hθ => ?_
  rw [Set.Finite.mem_toFinset] at hθ
  rw [deg_eq hθ]
  have := S.two_mb χ θ
  have h' : ((2 * (S.mb χ θ : ℤ) : ℤ) : ℂ) = ((S.Ar χ θ - S.M χ θ : ℤ) : ℂ) := by rw [this]
  push_cast at h'
  linear_combination -(θ 1) * h'

theorem deg_parity {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) {t : ℤ} (ht : χ S.J = t) :
    ∃ k : ℤ, deg χ = t + 2 * k := by
  obtain ⟨k, hk⟩ := S.deg_sub_J hχ
  refine ⟨k, ?_⟩
  have h : ((deg χ : ℤ) : ℂ) = ((t + 2 * k : ℤ) : ℂ) := by
    rw [deg_eq hχ]
    push_cast
    linear_combination hk + ht
  exact_mod_cast h

namespace EtaData

variable {S} (D : S.EtaData)

theorem restrict_Ro {χ : G → ℂ} (h : χ ∈ D.NE) :
    (Nat.card S.W.Ro : ℤ) ∣ deg χ - z (S := S) χ := by
  have hχ := (D.mem_NE.mp h).1
  obtain ⟨n, hn⟩ := exists_natCast_restrict (S.κ.comp S.W.Ro.subtype) hχ
    (one_mem_blocksIrr S.W.Ro)
  have hsum : ∑ r : S.W.Ro, χ (S.κ r) =
      (deg χ : ℂ) + ((Nat.card S.W.Ro : ℂ) - 1) * z (S := S) χ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
    have hrest : ∀ r ∈ (Finset.univ : Finset S.W.Ro).erase 1, χ (S.κ r) = z (S := S) χ := by
      intro r hr
      have hr1 : (r : L) ≠ 1 := fun h' => (Finset.mem_erase.mp hr).1 (Subtype.ext h')
      exact D.τ_NE h r.2 hr1
    rw [Finset.sum_congr rfl hrest, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, nsmul_eq_mul, OneMemClass.coe_one, map_one, deg_eq hχ]
    rw [Nat.cast_sub (Fintype.card_pos), Fintype.card_eq_nat_card]
    push_cast
    ring
  have hinner : BlocksInnerProduct (χ ∘ (S.κ.comp S.W.Ro.subtype)) (1 : S.W.Ro → ℂ) =
      (Nat.card S.W.Ro : ℂ)⁻¹ * ∑ r : S.W.Ro, χ (S.κ r) := by
    unfold BlocksInnerProduct
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    simp
  rw [hinner, hsum] at hn
  have hR0 : (Nat.card S.W.Ro : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have key : ((deg χ - z (S := S) χ : ℤ) : ℂ) =
      (((Nat.card S.W.Ro : ℤ) * (n - z (S := S) χ) : ℤ) : ℂ) := by
    have := hn
    field_simp at this
    push_cast
    linear_combination this
  exact ⟨n - z (S := S) χ, by exact_mod_cast key⟩

end EtaData

end WardSetup

end CFSG.Walter.Ward
