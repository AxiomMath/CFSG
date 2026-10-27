module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassTransport

public section

namespace CFSG.ShultStronglyClosedTI.AmbientDegree

open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.MixedClass
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem card_pairs_const_fiber {α β : Type*} [Finite α] [Finite β] (A : Set α)
    (R : α → β → Prop) (c : ℕ) (hfib : ∀ a ∈ A, Nat.card {b // R a b} = c) :
    Nat.card {p : α × β // p.1 ∈ A ∧ R p.1 p.2} = Nat.card A * c := by
  classical
  have := Fintype.ofFinite A
  calc Nat.card {p : α × β // p.1 ∈ A ∧ R p.1 p.2} = Nat.card (Σ a : A, {b // R a b}) :=
        Nat.card_congr
          { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
            invFun := fun x => ⟨(x.1.1, x.2.1), x.1.2, x.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
    _ = ∑ a : A, Nat.card {b // R a b} := Nat.card_sigma
    _ = ∑ _a : A, c := Finset.sum_congr rfl fun a _ => hfib a a.2
    _ = Nat.card A * c := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

variable {G : Type*} [Group G]

theorem card_inf_centralizer_conj {H Q : Subgroup G} {z : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (u : G) {k : G} (hk : k ∈ H) :
    Nat.card (Q ⊓ Subgroup.centralizer ({k⁻¹ * u * k} : Set G) : Subgroup G) =
      Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
  have hQnorm := point_subgroup_normalized hQclass
  have hQk : ∀ a ∈ Q, k * a * k⁻¹ ∈ Q := fun a ha => by
    simpa only [inv_inv] using hQnorm k⁻¹ (H.inv_mem hk) a ha
  symm
  apply Nat.card_congr
  refine
    { toFun := fun e => ⟨k⁻¹ * e * k, hQnorm k hk e e.2.1, ?_⟩
      invFun := fun f => ⟨k * f * k⁻¹, hQk f f.2.1, ?_⟩
      left_inv := fun e => Subtype.ext (by simp only; group)
      right_inv := fun f => Subtype.ext (by simp only; group) }
  · have he : Commute (e : G) u := Subgroup.mem_centralizer_singleton_iff.mp e.2.2
    have hc := he.conj k⁻¹
    rw [inv_inv] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc.eq
  · have hf : Commute (f : G) (k⁻¹ * u * k) := Subgroup.mem_centralizer_singleton_iff.mp f.2.2
    have hc := hf.conj k
    rw [show k * (k⁻¹ * u * k) * k⁻¹ = u by group] at hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr hc.eq

variable [Finite G]

theorem card_square_fiber {Q : Subgroup G} (hQ : CFSG.Open.IsElemAbelian 2 Q) {v : G}
    (hv2 : v * v = 1) (hvQ : ∀ q ∈ Q, v⁻¹ * q * v ∈ Q)
    (hsq : Nat.card Q = Nat.card (Q ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) ^ 2)
    {z : G} (hz : z ∈ Q ⊓ Subgroup.centralizer ({v} : Set G)) :
    Nat.card {s : G // s ∈ Q ∧ (v * s) ^ 2 = z} =
      Nat.card (Q ⊓ Subgroup.centralizer ({v} : Set G) : Subgroup G) := by
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hinvQ : ∀ a ∈ Q, a⁻¹ = a := fun a ha =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hQ.2 a ha)
  have hiff : ∀ s ∈ Q, (v * s) ^ 2 = z ↔ s⁻¹ * v * s = v * z := by
    intro s hs
    have hexp : (v * s) ^ 2 = v * (s⁻¹ * v * s) := by
      rw [sq, hinvQ s hs]
      group
    rw [hexp]
    constructor
    · intro h'
      rw [← h', ← mul_assoc, hv2, one_mul]
    · intro h'
      rw [h', ← mul_assoc, hv2, one_mul]
  have hvz : v * z ∈ conjugacyWithin Q v := by
    rw [← coset_eq_conjugacyWithin hQ hv2 hvQ hsq]
    exact ⟨z, hz, rfl⟩
  obtain ⟨s₀, hs₀⟩ := hvz
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun c => ⟨(c : G) * s₀, Q.mul_mem c.2.1 s₀.2, ?_⟩) ⟨?_, ?_⟩
  · rw [hiff _ (Q.mul_mem c.2.1 s₀.2), ← hs₀]
    have hc := conj_eq_self_of_mem_centralizer c.2.2
    calc ((c : G) * s₀)⁻¹ * v * (c * s₀) = (s₀ : G)⁻¹ * ((c : G)⁻¹ * v * c) * s₀ := by group
      _ = (s₀ : G)⁻¹ * v * s₀ := by rw [hc]
  · intro c₁ c₂ h'
    have h'' : (c₁ : G) * s₀ = c₂ * s₀ := congrArg Subtype.val h'
    exact Subtype.ext (mul_right_cancel h'')
  · rintro ⟨s, hsQ, hs⟩
    have hs' := (hiff s hsQ).mp hs
    refine ⟨⟨s * (s₀ : G)⁻¹, Q.mul_mem hsQ (Q.inv_mem s₀.2), ?_⟩, ?_⟩
    · apply mem_centralizer_of_conj_eq_self
      calc (s * (s₀ : G)⁻¹)⁻¹ * v * (s * (s₀ : G)⁻¹) = s₀ * (s⁻¹ * v * s) * (s₀ : G)⁻¹ := by
            group
        _ = v := by rw [hs', ← hs₀]; group
    · apply Subtype.ext
      change s * (s₀ : G)⁻¹ * s₀ = s
      group

theorem card_class_inter_centralizer_mul {H Q : Subgroup G} {z u : G}
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) :
    Nat.card {v : G // v ∈ conjugacyWithin H u ∧ v ∈ Subgroup.centralizer ({z} : Set G)} *
        (Nat.card Q - 1) =
      Nat.card (conjugacyWithin H u) *
        (Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) - 1) := by
  let R : G → G → Prop := fun v r => r ∈ (Q : Set G) \ {1} ∧ Commute v r
  have hrow := card_pairs_const_fiber (conjugacyWithin H u) R
    (Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) - 1) (by
      rintro v ⟨k, rfl⟩
      rw [← card_inf_centralizer_conj hQclass u k.2, ← card_diff_one]
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun r => ?_
      simp only [R, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨⟨hr, hr1⟩, hc⟩
        exact ⟨⟨hr, hc.eq.symm⟩, hr1⟩
      · rintro ⟨⟨hr, hc⟩, hr1⟩
        exact ⟨⟨hr, hr1⟩, hc.symm⟩)
  have hcol := card_pairs_const_fiber ((Q : Set G) \ {1}) (fun r v => v ∈ conjugacyWithin H u ∧
      Commute v r)
    (Nat.card {v : G // v ∈ conjugacyWithin H u ∧ v ∈ Subgroup.centralizer ({z} : Set G)}) (by
      intro r hr
      rw [hQclass] at hr
      obtain ⟨k, rfl⟩ := hr
      symm
      apply Nat.card_congr
      have hconjH : ∀ x : G, x ∈ conjugacyWithin H u → ∀ g ∈ H,
          g⁻¹ * x * g ∈ conjugacyWithin H u := by
        rintro x ⟨a, rfl⟩ g hg
        exact ⟨a * ⟨g, hg⟩, by simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc]⟩
      refine
        { toFun := fun v => ⟨(k : G)⁻¹ * v * k, hconjH v v.2.1 k k.2, ?_⟩
          invFun := fun v => ⟨(k : G) * v * (k : G)⁻¹, by
            simpa only [inv_inv] using hconjH v v.2.1 (k : G)⁻¹ (H.inv_mem k.2), ?_⟩
          left_inv := fun v => Subtype.ext (by simp only; group)
          right_inv := fun v => Subtype.ext (by simp only; group) }
      · have hc : Commute (v : G) z := Subgroup.mem_centralizer_singleton_iff.mp v.2.2
        simpa only [inv_inv] using hc.conj (k : G)⁻¹
      · have hc := (v.2.2).conj (k : G)
        rw [show (k : G) * ((k : G)⁻¹ * z * k) * (k : G)⁻¹ = z by group] at hc
        exact Subgroup.mem_centralizer_singleton_iff.mpr hc.eq)
  have hswap : Nat.card {p : G × G // p.1 ∈ conjugacyWithin H u ∧ R p.1 p.2} =
      Nat.card {p : G × G // p.1 ∈ (Q : Set G) \ {1} ∧
        (p.2 ∈ conjugacyWithin H u ∧ Commute p.2 p.1)} := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv (Equiv.prodComm G G) fun p => ?_
    simp only [R, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    tauto
  rw [hswap, hcol, card_diff_one] at hrow
  rw [← hrow, mul_comm]

end CFSG.ShultStronglyClosedTI.AmbientDegree
