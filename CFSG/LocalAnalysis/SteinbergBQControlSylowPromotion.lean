module

public import CFSG.Foundations.MaxOrderThompsonDefs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.LocalAnalysis.SteinbergBQ

open CFSG
open scoped Pointwise

variable {G : Type*} [Group G]

theorem not_dvd_relIndex_of_not_dvd_relIndex_normalizer [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {S H : Subgroup G} (hSH : S ≤ H) (hS : IsPGroup p S)
    (h : ¬ p ∣ S.relIndex (H ⊓ Subgroup.normalizer (S : Set G))) : ¬ p ∣ S.relIndex H := by
  intro hdvd
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hS
  have hH := Subgroup.relIndex_mul_card (H := S) (K := H)
  rw [inf_eq_left.2 hSH, hn] at hH
  have hdvdH : p ^ (n + 1) ∣ Nat.card H := by
    rw [← hH, pow_succ, mul_comm (p ^ n)]
    exact Nat.mul_dvd_mul_right hdvd _
  have hS' : Nat.card (S.subgroupOf H) = p ^ n := by
    rw [← hn]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv
  have h1 := Sylow.prime_pow_dvd_card_normalizer hdvdH hS'
  rw [← Subgroup.subgroupOf_normalizer_eq hSH] at h1
  have h2 : Nat.card ((Subgroup.normalizer (S : Set G)).subgroupOf H) =
      Nat.card (H ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2] at h1
  have h3 := Subgroup.relIndex_mul_card (H := S) (K := H ⊓ Subgroup.normalizer (S : Set G))
  rw [inf_eq_left.2 (le_inf hSH Subgroup.le_normalizer), hn] at h3
  rw [← h3, pow_succ, mul_comm (S.relIndex (H ⊓ Subgroup.normalizer (S : Set G))) (p ^ n)] at h1
  exact h (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.out.pos n) h1)

theorem normalizer_le_normalizer_of_le_isCyclic [Finite G] {U S : Subgroup G} (hUS : U ≤ S)
    (hS : IsCyclic S) : Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (U : Set G) := by
  classical
  have key : ∀ x ∈ S, x ^ Nat.card U = 1 → x ∈ U := by
    intro x hxS hxU
    have := Fintype.ofFinite S
    have := Fintype.ofFinite U
    let T : Finset S := Finset.univ.filter fun a => a ^ Nat.card U = 1
    have hT : T.card ≤ Nat.card U := IsCyclic.card_pow_eq_one_le Nat.card_pos
    let T' : Finset S := Finset.univ.filter fun a => (a : G) ∈ U
    have hT'T : T' ⊆ T := fun a ha => by
      simp only [T', Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      have h1 : (⟨a, ha⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
      apply Subtype.ext
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h2
    have hT' : T'.card = Nat.card U := by
      rw [Nat.card_eq_fintype_card (α := U)]
      refine Finset.card_bij (fun a ha => ⟨a, by simpa [T'] using ha⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ h => Subtype.ext (congrArg (fun x : U => (x : G)) h)) fun u _ => ?_
      exact ⟨⟨u, hUS u.2⟩, by simp [T'], rfl⟩
    have heq : T' = T := Finset.eq_of_subset_of_card_le hT'T (by rw [hT']; exact hT)
    have hxT : (⟨x, hxS⟩ : S) ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hxU)
    rw [← heq] at hxT
    simpa [T'] using hxT
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    refine key _ ((Subgroup.mem_normalizer_iff.1 hg u).1 (hUS hu)) ?_
    rw [conj_pow]
    have h1 : (⟨u, hu⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [h2, mul_one, mul_inv_cancel]
  · intro hu
    have hg' := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (g * u * g⁻¹)).1
      (hUS hu)
    have hu' : u = g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ := by group
    rw [hu']
    refine key _ hg' ?_
    rw [conj_pow]
    have h1 : (⟨g * u * g⁻¹, hu⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [h2, mul_one, mul_inv_cancel]

end CFSG.LocalAnalysis.SteinbergBQ
