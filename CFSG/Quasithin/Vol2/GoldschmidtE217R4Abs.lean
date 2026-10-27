module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Cent
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Pair
public import CFSG.Quasithin.Vol2.GoldschmidtE217R4Swap

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Layer

namespace E217R4

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem exists_pair_of_swap {S K₁ K₂ : Subgroup Γ} {t v : Γ} (hS : IsSylowTwoOf S ⊤)
    (hKn : (K₁ ⊔ K₂).Normal) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
    (hL₁ : L27 ↥K₁) (hL₂ : L27 ↥K₂) (hK₂ : K₂ = K₁.map (MulAut.conj t).toMonoidHom)
    (htS : t ∈ S) (hvS : ∀ s ∈ S, s * v = v * s) (hv2 : v * v = 1) (hv1 : v ≠ 1)
    (hvN : v ∈ K₁ ⊔ K₂) :
    ∃ Ā T₀ : Subgroup Γ, Nat.card Ā = 9 ∧ T₀ ≤ S ∧ T₀ ≤ Subgroup.normalizer (Ā : Set Γ) ∧
      (∀ C : Subgroup Γ, C ≤ Ā → T₀ ≤ Subgroup.normalizer (C : Set Γ) → C = ⊥ ∨ C = Ā) ∧
      (∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, v = k₁ * k₂ ∧ k₁ ∈ T₀ ∧ k₂ ∈ T₀) ∧
      v ∈ T₀ ∧ ∀ a ∈ Ā, v * a * v⁻¹ * a = 1 := by
  have hK₁N : K₁ ≤ Subgroup.normalizer (K₂ : Set Γ) :=
    (show K₁ ≤ Subgroup.centralizer (K₂ : Set Γ) from fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun b hb => (hc a ha b hb).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hK₂N : K₂ ≤ Subgroup.normalizer (K₁ : Set Γ) :=
    (show K₂ ≤ Subgroup.centralizer (K₁ : Set Γ) from fun b hb =>
      Subgroup.mem_centralizer_iff.2 fun a ha => hc a ha b hb).trans
      (Subgroup.centralizer_le_normalizer _)
  have hKt := map_conj_eq_of_swap hKn hc hd hL₁ hL₂ hK₂
  have m1 : ∀ x ∈ K₁, t * x * t⁻¹ ∈ K₂ := fun x hx => by
    rw [hK₂]
    exact ⟨x, hx, rfl⟩
  have m2 : ∀ x ∈ K₂, t * x * t⁻¹ ∈ K₁ := fun x hx => by
    rw [← hKt]
    exact ⟨x, hx, rfl⟩
  have m3 : ∀ x ∈ K₁, t⁻¹ * x * t ∈ K₂ := fun x hx => by
    rw [← hKt] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
    show t⁻¹ * (t * y * t⁻¹) * t ∈ K₂
    rwa [e]
  have m4 : ∀ x ∈ K₂, t⁻¹ * x * t ∈ K₁ := fun x hx => by
    rw [hK₂] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
    show t⁻¹ * (t * y * t⁻¹) * t ∈ K₁
    rwa [e]
  obtain ⟨k1, hk1, k2, hk2, hk12⟩ := exists_mul_of_mem_sup hc hvN
  have hsq : k1 * k1 = 1 ∧ k2 * k2 = 1 := by
    have h12 : (k1 * k1) * (k2 * k2) = 1 := by
      calc (k1 * k1) * (k2 * k2) = (k1 * k2) * (k1 * k2) := by
            calc (k1 * k1) * (k2 * k2) = k1 * (k1 * k2) * k2 := by group
              _ = k1 * (k2 * k1) * k2 := by rw [hc k1 hk1 k2 hk2]
              _ = (k1 * k2) * (k1 * k2) := by group
        _ = 1 := by rw [hk12]; exact hv2
    have hc1 : k1 * k1 ∈ K₁ := K₁.mul_mem hk1 hk1
    have hc2 : k1 * k1 ∈ K₂ := by
      have : k1 * k1 = (k2 * k2)⁻¹ := eq_inv_of_mul_eq_one_left h12
      rw [this]
      exact K₂.inv_mem (K₂.mul_mem hk2 hk2)
    have : k1 * k1 = 1 := by
      have := hd ▸ (Subgroup.mem_inf.2 ⟨hc1, hc2⟩ : k1 * k1 ∈ K₁ ⊓ K₂)
      simpa using this
    refine ⟨this, ?_⟩
    rw [this, one_mul] at h12
    exact h12
  have htv : t * v * t⁻¹ = v := by
    calc t * v * t⁻¹ = v * t * t⁻¹ := by rw [hvS t htS]
      _ = v := by group
  have hab : (t * k2 * t⁻¹) * (t * k1 * t⁻¹) = k1 * k2 := by
    calc (t * k2 * t⁻¹) * (t * k1 * t⁻¹) = (t * k1 * t⁻¹) * (t * k2 * t⁻¹) :=
          hc _ (m2 k2 hk2) _ (m1 k1 hk1)
      _ = t * (k1 * k2) * t⁻¹ := by group
      _ = k1 * k2 := by rw [hk12, htv]
  obtain ⟨hk21, hk12'⟩ := eq_of_mul_eq_of_inf_eq_bot hd (m2 k2 hk2) hk1 (m1 k1 hk1) hk2 hab
  have hk1one : k1 ≠ 1 := fun h => hv1 (by
    have : k2 = 1 := by rw [← hk12', h]; group
    rw [← hk12, h, this, one_mul])
  have hD₁ : IsSylowTwoOf (S ⊓ K₁) K₁ := isSylowTwoOf_inf_of_normal hS hKn le_sup_left
    (sup_le Subgroup.le_normalizer hK₂N)
  have hD₂ : IsSylowTwoOf (S ⊓ K₂) K₂ := isSylowTwoOf_inf_of_normal hS hKn le_sup_right
    (sup_le hK₁N Subgroup.le_normalizer)
  have hz₁c : ∀ d ∈ S ⊓ K₁, d * k1 = k1 * d := fun d hd' => by
    have h3 : (d * k1) * k2 = (k1 * d) * k2 := by
      calc (d * k1) * k2 = d * (k1 * k2) := by rw [mul_assoc]
        _ = d * v := by rw [hk12]
        _ = v * d := hvS d hd'.1
        _ = (k1 * k2) * d := by rw [hk12]
        _ = k1 * (k2 * d) := by rw [mul_assoc]
        _ = k1 * (d * k2) := by rw [hc d hd'.2 k2 hk2]
        _ = (k1 * d) * k2 := by rw [mul_assoc]
    exact mul_right_cancel h3
  have hz₁S : k1 ∈ S := (mem_of_commutes_sylow hL₁ hD₁ hk1 hz₁c).1
  have ht₂ : t * (t * k1 * t⁻¹) * t⁻¹ = k1 := by rw [hk12', hk21]
  obtain ⟨Ā, T₀, hcard, hT₀S, hT₀N, hirr, hz₁T₀, hz₂T₀, hinv⟩ := exists_irreducible_pair hL₁ hL₂ hc
    hd hD₂ htS m1 m3 m4 hk1 hz₁S hsq.1 hk1one hz₁c ht₂
  have hvz : k1 * (t * k1 * t⁻¹) = v := by rw [hk12', hk12]
  refine ⟨Ā, T₀, hcard, hT₀S, hT₀N, hirr, ⟨k1, hk1, k2, hk2, hk12.symm, hz₁T₀, hk12' ▸ hz₂T₀⟩,
    ?_, ?_⟩
  · rw [← hvz]
    exact T₀.mul_mem hz₁T₀ hz₂T₀
  · rw [← hvz]
    exact hinv

end E217R4

end CFSG.Quasithin
