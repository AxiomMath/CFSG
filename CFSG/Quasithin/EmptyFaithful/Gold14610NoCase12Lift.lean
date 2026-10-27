module

public import CFSG.Quasithin.EmptyFaithful.Gold14610NoCase12Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace NC12

variable {J : Type} [Group J] [Finite J]

theorem lift_le (X : Subgroup J) [X.Normal] {J₁ J₂ L T' W : Subgroup J} (hJ₁ : J₁ = L ⊔ T')
    (hT' : IsPGroup 2 ↥T')
    (hT : IsGoldschmidtTriple (J₁.map (QuotientGroup.mk' X)) (J₂.map (QuotientGroup.mk' X)))
    (hinf : J₁.map (QuotientGroup.mk' X) ⊓ J₂.map (QuotientGroup.mk' X) =
      (J₁ ⊓ J₂).map (QuotientGroup.mk' X))
    {Pb : Subgroup (J ⧸ X)} [Pb.Normal]
    (hP₂ : twoResidual (J₂.map (QuotientGroup.mk' X)) ≤ Pb)
    (hP₁ : ¬ twoResidual (J₁.map (QuotientGroup.mk' X)) ≤ Pb) (hJ₁W : J₁ ≤ W)
    (hc3 : L ≤ Pb.comap (QuotientGroup.mk' X) ∨ Pb.comap (QuotientGroup.mk' X) ≤ W) :
    J₂ ≤ W := by
  classical
  set π := QuotientGroup.mk' X with hπ
  have hPbn : ∀ g : J ⧸ X, g ∈ Subgroup.normalizer (Pb : Set (J ⧸ X)) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  rcases hc3 with hL | hW
  · exfalso
    apply hP₁
    have hD₁ : J₁.map π ≤ T'.map π ⊔ Pb := by
      rw [hJ₁, Subgroup.map_sup]
      exact sup_le (le_sup_of_le_right (Subgroup.map_le_iff_le_comap.mpr hL)) le_sup_left
    have hq := B6.isTwoQuotient_of_sup_eq (hT'.map π) (fun g _ => hPbn g)
      (rfl : T'.map π ⊔ Pb = T'.map π ⊔ Pb)
    exact twoResidual_le_of_pow_mem fun x hx => hq x (hD₁ hx)
  · intro x hx
    have hS : IsSylowTwoOf (J₁.map π ⊓ J₂.map π) (J₂.map π) :=
      F7.isSylowTwoOf_mono_right (isSylowTwoOf_top hT) inf_le_right le_top
    have hD₂ := sup_twoResidual_eq hS
    have hmem : π x ∈ (J₁.map π ⊓ J₂.map π) ⊔ twoResidual (J₂.map π) := by
      rw [hD₂]
      exact Subgroup.mem_map_of_mem π hx
    have hπx : π x ∈ (J₁.map π ⊓ J₂.map π) ⊔ Pb := (sup_le_sup_left hP₂ _) hmem
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hπx
    obtain ⟨t, ht, p, hp, htp⟩ := hπx
    rw [hinf] at ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    obtain ⟨p₀, rfl⟩ := QuotientGroup.mk'_surjective X p
    have hp₀ : p₀ ∈ Pb.comap π := hp
    have htp' : π t₀ * π p₀ = π x := htp
    have hk : (t₀ * p₀)⁻¹ * x ∈ Pb.comap π := by
      have h1 : π ((t₀ * p₀)⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, map_mul, htp', inv_mul_cancel]
      rw [Subgroup.mem_comap, h1]
      exact Pb.one_mem
    have hx' : x = t₀ * (p₀ * ((t₀ * p₀)⁻¹ * x)) := by group
    rw [hx']
    exact W.mul_mem (hJ₁W ht₀.1) (W.mul_mem (hW hp₀) (hW hk))

end NC12

end Gold14610

end CFSG.Quasithin
