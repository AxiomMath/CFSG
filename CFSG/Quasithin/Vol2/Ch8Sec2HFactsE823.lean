module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsL3
public import CFSG.Quasithin.Background.HFL3Par

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
open scoped commutatorElement

theorem hL3Nine823_holds :
    ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
      ∀ n : ℕ, 1 ≤ n → BinaryNineTensor L ⊤ ⊥ n →
        (∀ x ∈ M, ∀ A : Subgroup (MulAut V), A ≤ M → IsPGroup 2 ↥A →
          x ∈ Subgroup.normalizer (A : Set (MulAut V)) → ⁅A, Subgroup.zpowers x⁆ ≤ L) ∧
        (∀ x ∈ M, Odd (orderOf x) → ∀ R : Subgroup (MulAut V), R ≤ L → IsPGroup 2 ↥R →
          R ≠ ⊥ → x ∈ Subgroup.normalizer (R : Set (MulAut V)) →
            orderOf x ∣ (2 ^ (4 * n) - 1) * n) := by
  intro V _ _ L M hLM n hn hL
  obtain ⟨K, _, _, _, hK, e, hLe, hMN⟩ := exists_model_l3nine hLM hL
  have hmemL : ∀ w : MulAut V, congrHom e w ∈ L3Nine.img hK → w ∈ L := by
    intro w hw
    rw [← hLe] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    rwa [← congrHom_injective e hww']
  refine ⟨?_, ?_⟩
  ·
    intro x hxM A hAM hA2 hxA
    rw [Subgroup.commutator_le]
    intro a ha z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzM : x ^ k ∈ M := zpow_mem hxM k
    have hzA : x ^ k ∈ Subgroup.normalizer (A : Set (MulAut V)) := zpow_mem hxA k
    have hwA : ⁅a, x ^ k⁆ ∈ A := by
      rw [commutatorElement_def]
      have h1 : x ^ k * a⁻¹ * (x ^ k)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hzA _).mp (inv_mem ha)
      have h2 := mul_mem ha h1
      simpa [mul_assoc] using h2
    refine hmemL _ (L3Nine.mem_img_of_isPGroup_zpowers hK ?_ ?_)
    · rw [map_commutatorElement, commutatorElement_def]
      exact L3Nine.commutator_mem_linImg hn hK (hMN ⟨a, hAM ha, rfl⟩) (hMN ⟨x ^ k, hzM, rfl⟩)
    · rw [← MonoidHom.map_zpowers]
      exact (hA2.to_le ((Subgroup.zpowers_le).2 hwA)).map _
  ·
    intro x hxM hodd R hRL hR2 hR1 hxR
    have hR'L : R.map (congrHom e) ≤ L3Nine.img hK := by
      rw [← hLe]
      exact Subgroup.map_mono hRL
    have hR'1 : R.map (congrHom e) ≠ ⊥ := fun h =>
      hR1 ((Subgroup.map_eq_bot_iff_of_injective _ (congrHom_injective e)).mp h)
    have hx'R : congrHom e x ∈ Subgroup.normalizer
        ((R.map (congrHom e) : Subgroup (MulAut (L3Nine.HMod n K))) :
          Set (MulAut (L3Nine.HMod n K))) := by
      rw [← Subgroup.map_equiv_normalizer_eq R (MulAut.congr e)]
      exact ⟨x, hxR, rfl⟩
    have h := L3Nine.orderOf_dvd_of_normalizes hn hK (hMN ⟨x, hxM, rfl⟩)
      (by rwa [orderOf_injective _ (congrHom_injective e)]) hR'L (hR2.map _) hR'1 hx'R
    rwa [orderOf_injective _ (congrHom_injective e)] at h

end CFSG.Quasithin.H13
