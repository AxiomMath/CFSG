module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLBLevel

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.GoldMLB
open CFSG.QuasithinUnique.Setup.X6

variable {G : Type} [Group G] [Finite G]

theorem GoldMLB.normalizer_le_of_isParabolic2 {K P S₀ : Subgroup G} (hP : IsParabolic2 K P)
    (hS₀ : IsSylowTwoOf S₀ K) (hS₀P : S₀ ≤ P) : K ⊓ Subgroup.normalizer (S₀ : Set G) ≤ P := by
  obtain ⟨hPK, S₁, hS₁, hN⟩ := hP
  have hS₁P : S₁ ≤ P := fun x hx => hN ⟨hS₁.1 hx, Subgroup.le_normalizer hx⟩
  have h₀ := isSylowTwoOf_of_le_of_le hS₀ hS₀P hPK
  have h₁ := isSylowTwoOf_of_le_of_le hS₁ hS₁P hPK
  obtain ⟨k, hkP, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 h₁) (isSylowTwoOf_iff_isSylowOf.1 h₀)
  rintro g ⟨hgK, hgN⟩
  have hkK : k ∈ K := hPK hkP
  have hmem : ∀ y, y ∈ S₁ ↔ k * y * k⁻¹ ∈ S₀ := fun y => by
    have := hk (k * y * k⁻¹)
    rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group] at this
    exact this.symm
  have hgN' : k⁻¹ * g * k ∈ Subgroup.normalizer (S₁ : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
    rw [hmem y, hmem (k⁻¹ * g * k * y * (k⁻¹ * g * k)⁻¹),
      show k * (k⁻¹ * g * k * y * (k⁻¹ * g * k)⁻¹) * k⁻¹ = g * (k * y * k⁻¹) * g⁻¹ by group]
    exact Subgroup.mem_normalizer_iff.mp hgN _
  have hgP : k⁻¹ * g * k ∈ P :=
    hN ⟨K.mul_mem (K.mul_mem (K.inv_mem hkK) hgK) hkK, hgN'⟩
  have := P.mul_mem (P.mul_mem hkP hgP) (P.inv_mem hkP)
  simpa [mul_assoc] using this

end CFSG.Quasithin
