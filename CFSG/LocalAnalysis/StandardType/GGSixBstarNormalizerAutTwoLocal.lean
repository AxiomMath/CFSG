module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNormalizerAut
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

namespace CFSG.StandardType

namespace NormalizerAut

open CFSG.Assembly

variable {C G : Type*} [Group C] [Group G] [Finite G]

theorem card_le_pow_twoLocalRank {p : ℕ} (hp : p.Prime) (χ : C →* G)
    (hχ : Function.Injective χ) {M : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (χ.range : Set G))
    (hC : Subgroup.centralizer (χ.range : Set G) = ⊥)
    {X : Subgroup (MulAut C)} (hX : X ≤ (normAutOn χ hχ hM).range) (hXel : IsElemAbelian p X)
    {U : Subgroup C} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hXU : ∀ φ ∈ X, ∀ u ∈ U, φ u ∈ U) :
    Nat.card X ≤ p ^ LargeEvenTwoLocalRank p G := by
  set Φ := normAutOn χ hχ hM with hΦ
  have hΦinj : Function.Injective Φ := normAutOn_injective χ hχ hM hC
  set Y : Subgroup M := X.comap Φ with hY
  set X' : Subgroup G := Y.map M.subtype with hX'
  have hcardY : Nat.card Y = Nat.card X := by
    have h := Subgroup.card_map_of_injective (K := Y) hΦinj
    rw [hY, Subgroup.map_comap_eq_self hX] at h
    exact h.symm
  have hcardX' : Nat.card X' = Nat.card X := by
    rw [hX', Subgroup.card_map_of_injective (K := Y) M.subtype_injective, hcardY]
  have hYel : IsElemAbelian p Y := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hΦinj ?_)⟩⟩, fun a ha => hΦinj ?_⟩
    · have h := congrArg Subtype.val (hXel.1.1.1 ⟨Φ a, a.2⟩ ⟨Φ b, b.2⟩)
      simpa only [map_mul, Subgroup.coe_mul] using h
    · rw [map_pow, hXel.2 _ ha, map_one]
  have hX'el : IsElemAbelian p X' := TableB.isElemAbelian_map hYel M.subtype
  have hUne : U.map χ ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ hχ]
    exact hU
  have hTL : IsTwoLocal (Subgroup.normalizer ((U.map χ : Subgroup G) : Set G)) :=
    ⟨_, hUne, hU2.map _, rfl⟩
  have hfwd : ∀ g ∈ X', ∀ y ∈ U.map χ, g * y * g⁻¹ ∈ U.map χ := by
    rintro _ ⟨m, hm, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨Φ m u, hXU _ hm u hu, ?_⟩
    rw [chi_normAutOn_apply χ hχ hM m u]
    rfl
  have hXN : X' ≤ Subgroup.normalizer ((U.map χ : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd g hg y, fun hy => ?_⟩
    have h := hfwd g⁻¹ (inv_mem hg) _ hy
    simpa [mul_assoc] using h
  have h1 := TableB.card_le_of_twoLocal hp hTL hXN hX'el
  rwa [hcardX'] at h1

end NormalizerAut

end CFSG.StandardType
