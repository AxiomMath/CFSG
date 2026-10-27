module

public import CFSG.RankThree.GF2n.Smith81.S81KNormGrp

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.D6Normalizer

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.RankThree.GF2n.Smith81.E7Model CFSG.RankThree.GF2n.Smith81.E7X
  CFSG.RankThree.GF2n.Smith81.D6X CFSG.RankThree.GF2n.Smith81.D6Spin


attribute [local instance] finite_W finite_WAut

@[expose] def SylowW : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
    ∀ A : Subgroup (W K ≃ₗ[K] W K), A ≤ EAut0 K → IsPGroup 2 A →
      ∃ g ∈ EAut0 K, ∀ a ∈ A, g * a * g⁻¹ ∈ UW K

theorem normalizerE4_of_sylow (hS : SylowW) :
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ∀ T : W K ≃ₗ[K] W K, (∀ g ∈ EAut0 K, ∃ g' ∈ EAut0 K, T * g = g' * T) →
        (∃ k : ℕ, T ^ (2 ^ k) = 1) → T ∈ EAut0 K := by
  intro K _ _ _ hK T hT hk
  obtain ⟨k, hk⟩ := hk
  have hK3 : 3 ≤ Nat.card K := by omega
  have hT1 : ∀ g ∈ EAut0 K, T * g * T⁻¹ ∈ EAut0 K := by
    intro g hg
    obtain ⟨g', hg', h⟩ := hT g hg
    rw [h, mul_inv_cancel_right]
    exact hg'
  have hT2 := conj_inv_mem_of_finite hT1
  let A : Subgroup (W K ≃ₗ[K] W K) := (UW K).map (MulAut.conj T).toMonoidHom
  have hAΓ : A ≤ EAut0 K := by
    rintro _ ⟨u, hu, rfl⟩
    exact hT1 u (UW_le_EAut0 hu)
  have hA2 : IsPGroup 2 A := by
    rintro ⟨_, u, hu, rfl⟩
    obtain ⟨j, hj⟩ := isPGroup_UW ⟨u, hu⟩
    refine ⟨j, Subtype.ext ?_⟩
    have h1 : u ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    show ((MulAut.conj T).toMonoidHom u) ^ (2 ^ j) = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨g, hgΓ, hgA⟩ := hS K hK A hAΓ hA2
  have hT₁U : ∀ u ∈ UW K, g * T * u * (g * T)⁻¹ ∈ UW K := by
    intro u hu
    have h1 := hgA (T * u * T⁻¹) ⟨u, hu, by simp [MulAut.conj_apply]⟩
    have e : g * T * u * (g * T)⁻¹ = g * (T * u * T⁻¹) * g⁻¹ := by group
    rw [e]
    exact h1
  have hT₁U' := conj_inv_mem_of_finite hT₁U
  have hT₁Γ : ∀ x ∈ EAut0 K, g * T * x * (g * T)⁻¹ ∈ EAut0 K := by
    intro x hx
    have e : g * T * x * (g * T)⁻¹ = g * (T * x * T⁻¹) * g⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hgΓ (hT1 x hx)) (inv_mem hgΓ)
  have hnormU : ∀ x ∈ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K)), ∀ u ∈ UW K,
      x * u * x⁻¹ ∈ UW K := fun x hx u hu => (Subgroup.mem_normalizer_iff.1 hx u).1 hu
  have hTB : ∀ b ∈ EAut0 K ⊓ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K)),
      g * T * b * (g * T)⁻¹ ∈ EAut0 K ⊓ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K)) := by
    intro b hb
    refine ⟨hT₁Γ b hb.1, Subgroup.mem_normalizer_iff.2 fun x => ?_⟩
    have e : g * T * b * (g * T)⁻¹ * x * (g * T * b * (g * T)⁻¹)⁻¹ =
        (g * T) * (b * ((g * T)⁻¹ * x * (g * T)) * b⁻¹) * (g * T)⁻¹ := by group
    rw [e]
    constructor
    · intro hx
      exact hT₁U _ (hnormU b hb.2 _ (hT₁U' x hx))
    · intro hx
      have h3 := hT₁U' _ hx
      have e2 : (g * T)⁻¹ * ((g * T) * (b * ((g * T)⁻¹ * x * (g * T)) * b⁻¹) * (g * T)⁻¹) *
          (g * T) = b * ((g * T)⁻¹ * x * (g * T)) * b⁻¹ := by group
      rw [e2] at h3
      have h4 := (Subgroup.mem_normalizer_iff.1 hb.2 ((g * T)⁻¹ * x * (g * T))).2 h3
      have h5 := hT₁U _ h4
      have e3 : (g * T) * ((g * T)⁻¹ * x * (g * T)) * (g * T)⁻¹ = x := by group
      rwa [e3] at h5
  obtain ⟨n, hn, hnT⟩ := exists_mul_normalizes (U := UW K) (H := HdW K)
    (B := EAut0 K ⊓ Subgroup.normalizer (UW K : Set (W K ≃ₗ[K] W K))) isPGroup_UW
    (fun h hh => odd_orderOf_of_mem_HdW hh)
    (fun u hu => ⟨UW_le_EAut0 hu, Subgroup.le_normalizer hu⟩) (fun h hh => hh.1)
    (fun b hb u hu => hnormU b hb.2 u hu) (fun b hb => normalizer_mul hb.1 hb.2) (g * T) hTB
  obtain ⟨σ, hσ⟩ := monomial_of_normalizes hK3 hnT
  have hT₂U : ∀ u ∈ UW K, n * (g * T) * u * (n * (g * T))⁻¹ ∈ UW K := by
    intro u hu
    have e : n * (g * T) * u * (n * (g * T))⁻¹ = n * (g * T * u * (g * T)⁻¹) * n⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hn (hT₁U u hu)) (inv_mem hn)
  have hdiag : n * (g * T) ∈ DiagW K := fun b => by
    obtain ⟨d, -, hd⟩ := hσ b
    exact ⟨d, by rw [hd, eq_self_of_normalizes hσ hT₂U b]⟩
  have hc : n * g ∈ EAut0 K := mul_mem (UW_le_EAut0 hn) hgΓ
  have hTD : T = (n * g)⁻¹ * (n * (g * T)) := by group
  have hDnorm : n * (g * T) ∈ Subgroup.normalizer (EAut0 K : Set (W K ≃ₗ[K] W K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have e : n * (g * T) * x * (n * (g * T))⁻¹ = (n * g) * (T * x * T⁻¹) * (n * g)⁻¹ := by group
    rw [e]
    constructor
    · intro hx
      exact mul_mem (mul_mem hc (hT1 x hx)) (inv_mem hc)
    · intro hx
      have h1 : T * x * T⁻¹ ∈ EAut0 K := by
        have := mul_mem (mul_mem (inv_mem hc) hx) hc
        have e2 : (n * g)⁻¹ * ((n * g) * (T * x * T⁻¹) * (n * g)⁻¹) * (n * g) =
            T * x * T⁻¹ := by group
        rwa [e2] at this
      simpa [mul_assoc] using hT2 _ h1
  exact mem_of_pow_mem_of_coprime hc hTD hDnorm odd_card_sub_one
    (pow_card_sub_one_of_diag hdiag) hk

end CFSG.RankThree.GF2n.Smith81.D6Normalizer
