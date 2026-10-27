module

public import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
public import CFSG.RankThree.PartOne.S11d.Facts5
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG

section Central

variable {G : Type*} [Group G]

theorem conj_aux {B a b u : G} (hu : ∀ x : G, u * x = x * u) (ha : a * B = u * B * a)
    (hb : b * B = u * B * b) : (a * b⁻¹) * B = B * (a * b⁻¹) := by
  have h1 : b⁻¹ * B = u⁻¹ * B * b⁻¹ := by
    have hu' : ∀ x : G, u⁻¹ * x = x * u⁻¹ := fun x => by
      have := hu x⁻¹
      calc u⁻¹ * x = u⁻¹ * (x * u) * u⁻¹ := by group
        _ = u⁻¹ * (u * x) * u⁻¹ := by rw [← hu x]
        _ = x * u⁻¹ := by group
    calc b⁻¹ * B = b⁻¹ * B * (b * b⁻¹) := by group
      _ = b⁻¹ * (B * b) * b⁻¹ := by group
      _ = b⁻¹ * (u⁻¹ * (u * B * b)) * b⁻¹ := by group
      _ = b⁻¹ * (u⁻¹ * (b * B)) * b⁻¹ := by rw [← hb]
      _ = u⁻¹ * (b⁻¹ * b) * B * b⁻¹ := by
        rw [show b⁻¹ * (u⁻¹ * (b * B)) * b⁻¹ = (b⁻¹ * u⁻¹) * (b * B) * b⁻¹ by group,
          show b⁻¹ * u⁻¹ = u⁻¹ * b⁻¹ from (hu' b⁻¹).symm]
        group
      _ = u⁻¹ * B * b⁻¹ := by group
  calc a * b⁻¹ * B = a * (b⁻¹ * B) := by group
    _ = a * (u⁻¹ * B * b⁻¹) := by rw [h1]
    _ = u⁻¹ * (a * B) * b⁻¹ := by
      have hu' : ∀ x : G, u⁻¹ * x = x * u⁻¹ := fun x => by
        calc u⁻¹ * x = u⁻¹ * (x * u) * u⁻¹ := by group
          _ = u⁻¹ * (u * x) * u⁻¹ := by rw [← hu x]
          _ = x * u⁻¹ := by group
      rw [show a * (u⁻¹ * B * b⁻¹) = (a * u⁻¹) * B * b⁻¹ by group,
        show a * u⁻¹ = u⁻¹ * a from (hu' a).symm]
      group
    _ = u⁻¹ * (u * B * a) * b⁻¹ := by rw [ha]
    _ = B * (a * b⁻¹) := by group

theorem commutator_mem_of_central_conj {B g₁ g₂ u₁ u₂ : G} (hu₁ : ∀ x : G, u₁ * x = x * u₁)
    (hu₂ : ∀ x : G, u₂ * x = x * u₂) (h₁ : g₁ * B * g₁⁻¹ = u₁ * B) (h₂ : g₂ * B * g₂⁻¹ = u₂ * B) :
    (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * B = B * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) := by
  have e₁ : g₁ * B = u₁ * B * g₁ := by
    have := congrArg (· * g₁) h₁
    simpa [mul_assoc] using this
  have e₂ : g₂ * B = u₂ * B * g₂ := by
    have := congrArg (· * g₂) h₂
    simpa [mul_assoc] using this
  have hu : ∀ x : G, (u₁ * u₂) * x = x * (u₁ * u₂) := fun x => by
    rw [mul_assoc, hu₂ x, ← mul_assoc, hu₁ x, mul_assoc]
  have hu21 : u₂ * u₁ = u₁ * u₂ := hu₂ u₁
  have ha : (g₁ * g₂) * B = (u₁ * u₂) * B * (g₁ * g₂) := by
    calc (g₁ * g₂) * B = g₁ * (g₂ * B) := by group
      _ = g₁ * (u₂ * B * g₂) := by rw [e₂]
      _ = u₂ * (g₁ * B) * g₂ := by
        rw [show g₁ * (u₂ * B * g₂) = (g₁ * u₂) * B * g₂ by group,
          show g₁ * u₂ = u₂ * g₁ from (hu₂ g₁).symm]
        group
      _ = u₂ * (u₁ * B * g₁) * g₂ := by rw [e₁]
      _ = (u₂ * u₁) * B * (g₁ * g₂) := by group
      _ = (u₁ * u₂) * B * (g₁ * g₂) := by rw [hu21]
  have hb : (g₂ * g₁) * B = (u₁ * u₂) * B * (g₂ * g₁) := by
    calc (g₂ * g₁) * B = g₂ * (g₁ * B) := by group
      _ = g₂ * (u₁ * B * g₁) := by rw [e₁]
      _ = u₁ * (g₂ * B) * g₁ := by
        rw [show g₂ * (u₁ * B * g₁) = (g₂ * u₁) * B * g₁ by group,
          show g₂ * u₁ = u₁ * g₂ from (hu₁ g₂).symm]
        group
      _ = u₁ * (u₂ * B * g₂) * g₁ := by rw [e₂]
      _ = (u₁ * u₂) * B * (g₂ * g₁) := by group
  have := conj_aux hu ha hb
  have h3 : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = (g₁ * g₂) * (g₂ * g₁)⁻¹ := by group
  rw [h3]
  exact this

end Central

section Comm

theorem exists_involution_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) : ∃ t : Q, orderOf t = 2 := by
  obtain ⟨-, hs, hnab⟩ := hQ
  have := hs
  have heven := (CFSG.ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (Subgroup.center Q)
  have h2 : 2 ∣ Nat.card Q := by
    rw [hk]
    exact Dvd.dvd.mul_right (even_iff_two_dvd.mp heven) k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact exists_prime_orderOf_dvd_card' 2 h2

variable {T : Type} [Group T]

theorem exists_two_subgroup_of_isComponentOf [Finite T] {N E : Subgroup T} (hE : IsComponentOf N E) :
    ∃ U : Subgroup T, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ U ≤ E := by
  obtain ⟨t, ht⟩ := exists_involution_of_isQuasisimple hE.2.1
  have hord : orderOf (t : T) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hcard : Nat.card (Subgroup.zpowers (t : T)) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨Subgroup.zpowers (t : T), ?_, IsPGroup.of_card (n := 1) (by rw [hcard]; norm_num), ?_⟩
  · intro hbot
    have := Subgroup.card_bot (G := T)
    rw [← hbot, hcard] at this
    omega
  · rw [Subgroup.zpowers_le]
    exact t.2

theorem commutator_eq_self_of_isQuasisimple {E : Subgroup T} (hq : CFSG.IsQuasisimple ↥E) :
    ⁅E, E⁆ = E := by
  have h1 : (commutator ↥E).map E.subtype = ⁅E, E⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have h2 : commutator ↥E = ⊤ := hq.1.commutator_eq_top
  rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

theorem not_commutative_of_isQuasisimple {E : Subgroup T} (hq : CFSG.IsQuasisimple ↥E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hcomm a' a'.2 b' b'.2)

theorem false_of_isComponentOf_of_comm {C E A : Subgroup T}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hC : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ A)
    (hE : IsComponentOf C E) : False := by
  have hq := hE.2.1
  have hEA : E ≤ A := by
    rw [← commutator_eq_self_of_isQuasisimple hq]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    exact hC x (hE.1 hx) y (hE.1 hy)
  exact not_commutative_of_isQuasisimple hq fun a ha b hb => hA a (hEA ha) b (hEA hb)

end Comm

end CFSG.RankThree.PartOne.FOC
