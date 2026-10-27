module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AW3Cycle

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

variable {T : Type} [CommGroup T] [Finite T] {ι : Type} [Fintype ι] {Y : ι → Subgroup T}
  {X : Subgroup (MulAut T)}

theorem s16t_w3_no_single (h : S16tW3Hyp Y X) {S : Subgroup (MulAut T)}
    (hS : ∀ g, g ∈ S ↔ g ∈ X ∧ (∀ i, (Y i).map g.toMonoidHom = Y i) ∧ g ^ 3 = 1)
    (hSc : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) {f : MulAut T} (hfX : f ∈ X) (hf3 : f ^ 3 = 1)
    (hfm : ∃ i, (Y i).map f.toMonoidHom ≠ Y i) {u : MulAut T} (hu : u ∈ S) {i : ι}
    (hj : ∀ j, j ≠ i → ∀ y ∈ Y j, u y = y) : ∀ y ∈ Y i, u y = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀, hmove⟩ := hcon
  obtain ⟨i₁, i₂, h1, h2, -, hi₁, hi₂, -, -⟩ := s16t_w3_cycle h hfX hf3 hfm i
  have hu₁S : f * u * f⁻¹ ∈ S := s16t_w3_conj_mem h hS hfX hu
  have hu₂S : f * (f * u * f⁻¹) * f⁻¹ ∈ S := s16t_w3_conj_mem h hS hfX hu₁S
  have hfix₁ : ∀ y ∈ Y i₁, u y = y := hj i₁ (Ne.symm hi₁)
  have hfix₂ : ∀ y ∈ Y i₂, u y = y := hj i₂ (Ne.symm hi₂)
  have hfix₁₂ : ∀ y ∈ Y i₂, (f * u * f⁻¹) y = y := by
    rw [← h2]
    exact s16t_w3_conj_fix hfix₁
  have hy₁ : f y₀ ∈ Y i₁ := h1 ▸ Subgroup.mem_map_of_mem f.toMonoidHom hy₀
  have hy₂ : f (f y₀) ∈ Y i₂ := h2 ▸ Subgroup.mem_map_of_mem f.toMonoidHom hy₁
  have hmove₁ : (f * u * f⁻¹) (f y₀) ≠ f y₀ := by
    rw [s16t_w3_conj_apply]
    exact fun h' => hmove (f.injective h')
  have hmove₂ : (f * (f * u * f⁻¹) * f⁻¹) (f (f y₀)) ≠ f (f y₀) := by
    rw [s16t_w3_conj_apply]
    exact fun h' => hmove₁ (f.injective h')
  have hu1 : u ≠ 1 := fun h' => hmove (by rw [h']; rfl)
  have hou : orderOf u = 3 := orderOf_eq_prime ((hS u).1 hu).2.2 hu1
  have hZC : Subgroup.zpowers u ≤ S ⊓ centSub (Y i₂) :=
    Subgroup.zpowers_le.2 ⟨hu, mem_centSub.2 hfix₂⟩
  have hS9 := s16t_w3_card_S h hS hSc
  have hC9 : Nat.card ↥(S ⊓ centSub (Y i₂)) ∣ 3 ^ 2 := by
    have h3 := Subgroup.card_dvd_of_le (inf_le_left : S ⊓ centSub (Y i₂) ≤ S)
    rwa [hS9] at h3
  have hC3 : 3 ∣ Nat.card ↥(S ⊓ centSub (Y i₂)) := by
    have h3 := Subgroup.card_dvd_of_le hZC
    rwa [Nat.card_zpowers, hou] at h3
  have hCne : Nat.card ↥(S ⊓ centSub (Y i₂)) ≠ 9 := by
    intro hc
    have hCS : S ⊓ centSub (Y i₂) = S :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hS9])
    have h3 : f * (f * u * f⁻¹) * f⁻¹ ∈ S ⊓ centSub (Y i₂) := by
      rw [hCS]
      exact hu₂S
    exact hmove₂ (mem_centSub.1 h3.2 _ hy₂)
  obtain ⟨k, hk, hck⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hC9
  have hC : Nat.card ↥(S ⊓ centSub (Y i₂)) = 3 := by
    interval_cases k
    · rw [hck] at hC3
      norm_num at hC3
    · rw [hck, pow_one]
    · exact absurd (hck.trans (by norm_num)) hCne
  have hZeq : Subgroup.zpowers u = S ⊓ centSub (Y i₂) :=
    Subgroup.eq_of_le_of_card_ge hZC (by rw [hC, Nat.card_zpowers, hou])
  have hu₁Z : f * u * f⁻¹ ∈ Subgroup.zpowers u := by
    rw [hZeq]
    exact ⟨hu₁S, mem_centSub.2 hfix₁₂⟩
  have hZfix : Subgroup.zpowers u ≤ centSub (Y i₁) :=
    Subgroup.zpowers_le.2 (mem_centSub.2 hfix₁)
  exact hmove₁ (mem_centSub.1 (hZfix hu₁Z) _ hy₁)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
