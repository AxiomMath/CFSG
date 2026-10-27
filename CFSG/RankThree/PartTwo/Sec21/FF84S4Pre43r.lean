module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Pre43f

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem comm_mul_central_derived {k k' z z' : G} (hk : k ∈ K) (hk' : k' ∈ K) (hz' : z' ∈ K)
    (hzc : ∀ g ∈ K, g * z = z * g) (hzc' : ∀ g ∈ K, g * z' = z' * g) :
    (k * z) * (k' * z') * (k * z)⁻¹ * (k' * z')⁻¹ = k * k' * k⁻¹ * k'⁻¹ := by
  have h1 : z * (k' * z') * z⁻¹ = k' * z' := by
    rw [← hzc (k' * z') (mul_mem hk' hz'), mul_inv_cancel_right]
  have h2 : z' * k⁻¹ * z'⁻¹ = k⁻¹ := by
    rw [← hzc' k⁻¹ (inv_mem hk), mul_inv_cancel_right]
  calc (k * z) * (k' * z') * (k * z)⁻¹ * (k' * z')⁻¹
      = k * (z * (k' * z') * z⁻¹) * k⁻¹ * (z'⁻¹ * k'⁻¹) := by group
    _ = k * (k' * z') * k⁻¹ * (z'⁻¹ * k'⁻¹) := by rw [h1]
    _ = k * k' * (z' * k⁻¹ * z'⁻¹) * k'⁻¹ := by group
    _ = k * k' * k⁻¹ * k'⁻¹ := by rw [h2]

theorem commutator_le_self : (⁅K, K⁆ : Subgroup G) ≤ K :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ =>
    mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

theorem derived_perfect (hK : IsTypeLnq 2 2 2 K) :
    commutator ↥(⁅K, K⁆ : Subgroup G) = ⊤ := by
  have hsub : (⁅K, K⁆ : Subgroup G) ≤ ⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ := by
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    obtain ⟨k₁, hk₁, z₁, hz₁K, hz₁c, hx₁⟩ := K_decomp hK g₁ h₁
    obtain ⟨k₂, hk₂, z₂, hz₂K, hz₂c, hx₂⟩ := K_decomp hK g₂ h₂
    have e : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = k₁ * k₂ * k₁⁻¹ * k₂⁻¹ := by
      rw [hx₁, hx₂]
      exact comm_mul_central_derived (commutator_le_self hk₁) (commutator_le_self hk₂) hz₂K hz₁c hz₂c
    show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ _
    rw [e]
    exact Subgroup.commutator_mem_commutator hk₁ hk₂
  rw [eq_top_iff]
  rintro ⟨m, hm⟩ -
  have h1 : m ∈ ⁅(⁅K, K⁆ : Subgroup G), (⁅K, K⁆ : Subgroup G)⁆ := hsub hm
  rw [← Subgroup.map_subtype_commutator] at h1
  obtain ⟨c, hc, hcm⟩ := Subgroup.mem_map.1 h1
  have h2 : c = ⟨m, hm⟩ := Subtype.ext hcm
  rw [← h2]
  exact hc

theorem range_card_ge' {Γ : Type*} [Group Γ] [Finite Γ] (hperf : commutator Γ = ⊤)
    (ψ : Γ →* alternatingGroup (Fin 5)) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center Γ) {M : Type*} [Group M] [Finite M]
    (φ : Γ →* M) (x₀ : Γ) (hx₀ : φ x₀ ≠ 1) : 60 ≤ Nat.card φ.range := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hN : φ.ker ≤ ψ.ker := by
    have hnorm : (φ.ker.map ψ).Normal := Subgroup.Normal.map φ.normal_ker ψ hψ
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map ψ) with hb | ht
    · intro n hn
      have : ψ n ∈ φ.ker.map ψ := Subgroup.mem_map_of_mem _ hn
      rw [hb] at this
      exact Subgroup.mem_bot.1 this
    · exfalso
      have hcomm : ∀ x y : Γ, x * y * x⁻¹ * y⁻¹ ∈ φ.ker := by
        intro x y
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 (ht ▸ Subgroup.mem_top (ψ x))
        obtain ⟨n', hn', hny⟩ := Subgroup.mem_map.1 (ht ▸ Subgroup.mem_top (ψ y))
        have hz : n⁻¹ * x ∈ Subgroup.center Γ := hker (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel])
        have hz' : n'⁻¹ * y ∈ Subgroup.center Γ := hker (by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hny, inv_mul_cancel])
        have hφx : φ x = φ (n⁻¹ * x) := by
          have : φ x = φ n * φ (n⁻¹ * x) := by rw [← map_mul]; congr 1; group
          rw [this, MonoidHom.mem_ker.1 hn, one_mul]
        have hφy : φ y = φ (n'⁻¹ * y) := by
          have : φ y = φ n' * φ (n'⁻¹ * y) := by rw [← map_mul]; congr 1; group
          rw [this, MonoidHom.mem_ker.1 hn', one_mul]
        have hcz : φ (n⁻¹ * x) * φ (n'⁻¹ * y) = φ (n'⁻¹ * y) * φ (n⁻¹ * x) := by
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz' (n⁻¹ * x))]
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hφx, hφy]
        have := (show Commute (φ (n⁻¹ * x)) (φ (n'⁻¹ * y)) from hcz)
        exact (commutatorElement_eq_one_iff_mul_comm.2 this) ▸ rfl
      have hle : (⊤ : Subgroup Γ) ≤ φ.ker := by
        rw [← hperf]
        exact Subgroup.commutator_le.2 fun g₁ _ g₂ _ => hcomm g₁ g₂
      exact hx₀ (MonoidHom.mem_ker.1 (hle (Subgroup.mem_top x₀)))
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  have h2 : Nat.card (Γ ⧸ ψ.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv, card_alt5]
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have h4 : Nat.card (Γ ⧸ φ.ker) = Nat.card φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h5 : Nat.card φ.ker ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hN
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  rw [h2] at h1
  rw [h4] at h3
  have h6 : 60 * Nat.card ψ.ker ≤ Nat.card φ.range * Nat.card ψ.ker := by
    calc 60 * Nat.card ψ.ker = Nat.card Γ := h1.symm
      _ = Nat.card φ.range * Nat.card φ.ker := h3
      _ ≤ Nat.card φ.range * Nat.card ψ.ker := Nat.mul_le_mul_left _ h5
  exact Nat.le_of_mul_le_mul_right h6 hpos

theorem derived_card (hK : IsTypeLnq 2 2 2 K) {M : Type*} [Group M]
    [Finite M] (φ : ↥(⁅K, K⁆ : Subgroup G) →* M) (x₀ : ↥(⁅K, K⁆ : Subgroup G)) (hx₀ : φ x₀ ≠ 1) :
    60 ≤ Nat.card φ.range := by
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hK
  have hle : (⁅K, K⁆ : Subgroup G) ≤ K := commutator_le_self
  let ψ : ↥(⁅K, K⁆ : Subgroup G) →* alternatingGroup (Fin 5) :=
    e5.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥K)).comp (Subgroup.inclusion hle))
  have hψs : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := e5.surjective a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, z, hzK, hzc, hx⟩ := K_decomp hK (x : G) x.2
    refine ⟨⟨k, hk⟩, ?_⟩
    have hz : (⟨k, hle hk⟩ : ↥K)⁻¹ * x ∈ Subgroup.center ↥K := by
      have : (⟨k, hle hk⟩ : ↥K)⁻¹ * x = ⟨z, hzK⟩ := by
        apply Subtype.ext
        show k⁻¹ * (x : G) = z
        rw [hx]; group
      rw [this]
      exact Subgroup.mem_center_iff.2 fun g => Subtype.ext (hzc g g.2)
    show e5 (QuotientGroup.mk (⟨k, hle hk⟩ : ↥K)) = e5 (QuotientGroup.mk x)
    rw [QuotientGroup.eq.2 hz]
  have hker : ψ.ker ≤ Subgroup.center ↥(⁅K, K⁆ : Subgroup G) := by
    intro m hm
    have h1 : QuotientGroup.mk' (Subgroup.center ↥K) (Subgroup.inclusion hle m) = 1 := by
      apply e5.injective
      rw [map_one]
      exact MonoidHom.mem_ker.1 hm
    have h2 : Subgroup.inclusion hle m ∈ Subgroup.center ↥K := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.1 h2 (Subgroup.inclusion hle g)
    apply Subtype.ext
    exact congrArg (fun t : ↥K => (t : G)) this
  exact range_card_ge' (derived_perfect hK) ψ hψs hker φ x₀ hx₀

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
