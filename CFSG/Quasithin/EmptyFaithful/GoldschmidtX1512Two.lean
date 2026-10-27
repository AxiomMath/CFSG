module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Bar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G]

theorem bar_mem_pCoreOf {H : Subgroup G} {Y : Subgroup (OTwoQuot H)} {g : G}
    (hg : g ∈ pCoreOf 2 (preimBar H Y)) : bar H g ∈ pCoreOf 2 Y := by
  set X := preimBar H Y with hX
  have hXH : X ≤ H := preimBar_le H Y
  have hgX : g ∈ X := pCoreOf_le 2 X hg
  have hgH : g ∈ H := hXH hgX
  set W := imBar H (pCoreOf 2 X) with hW
  have hWp : IsPGroup 2 W := by
    rintro ⟨z, hz⟩
    obtain ⟨w, hwH, hwP, rfl⟩ := mem_imBar.mp hz
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨w, hwP⟩
    refine ⟨k, Subtype.ext ?_⟩
    have : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    show bar H w ^ 2 ^ k = 1
    rw [← bar_pow hwH, this, bar_one]
  have hWY : W ≤ Y := by
    intro z hz
    obtain ⟨w, hwH, hwP, rfl⟩ := mem_imBar.mp hz
    exact (mem_preimBar.mp (pCoreOf_le 2 X hwP)).2
  have hnormX := le_normalizer_pCoreOf 2 X
  have hconj : ∀ h ∈ X, ∀ w ∈ pCoreOf 2 X, h * w * h⁻¹ ∈ pCoreOf 2 X := fun h hh w hw =>
    (Subgroup.mem_normalizer_iff.mp (hnormX hh) w).mp hw
  have hWn : Y ≤ Subgroup.normalizer (W : Set (OTwoQuot H)) := by
    intro ŷ hŷ
    obtain ⟨h, hhH, rfl⟩ := bar_surjective H ŷ
    have hhX : h ∈ X := mem_preimBar.mpr ⟨hhH, hŷ⟩
    have hhX' : h⁻¹ ∈ X := X.inv_mem hhX
    refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨w, hwH, hwP, rfl⟩ := mem_imBar.mp hx
      refine mem_imBar.mpr ⟨h * w * h⁻¹, ?_, hconj h hhX w hwP, ?_⟩
      · exact H.mul_mem (H.mul_mem hhH hwH) (H.inv_mem hhH)
      · rw [bar_mul (H.mul_mem hhH hwH) (H.inv_mem hhH), bar_mul hhH hwH, bar_inv hhH]
    · obtain ⟨w, hwH, hwP, rfl⟩ := mem_imBar.mp hx
      refine mem_imBar.mpr ⟨h⁻¹ * w * h, ?_, ?_, ?_⟩
      · exact H.mul_mem (H.mul_mem (H.inv_mem hhH) hwH) hhH
      · have := hconj h⁻¹ hhX' w hwP
        simpa using this
      · rw [bar_mul (H.mul_mem (H.inv_mem hhH) hwH) hhH, bar_mul (H.inv_mem hhH) hwH,
          bar_inv hhH]
  have hle : W ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer 2 hWY hWn hWp
  exact hle (mem_imBar.mpr ⟨g, hgH, hg, rfl⟩)

theorem mem_pCoreOf_of_bar_mem {H : Subgroup G} {Y : Subgroup (OTwoQuot H)} {g : G}
    (hg : g ∈ preimBar H Y) (hb : bar H g ∈ pCoreOf 2 Y) : g ∈ pCoreOf 2 (preimBar H Y) := by
  set X := preimBar H Y with hX
  have hXH : X ≤ H := preimBar_le H Y
  have hgH : g ∈ H := hXH hg
  set W := preimBar H (pCoreOf 2 Y) with hW
  have hWX : W ≤ X := by
    intro w hw
    obtain ⟨hwH, hwb⟩ := mem_preimBar.mp hw
    exact mem_preimBar.mpr ⟨hwH, pCoreOf_le 2 Y hwb⟩
  have hWp : IsPGroup 2 W := by
    rintro ⟨w, hw⟩
    obtain ⟨hwH, hwb⟩ := mem_preimBar.mp hw
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 Y) ⟨bar H w, hwb⟩
    have h1 : bar H w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : w ^ 2 ^ k ∈ pCoreOf 2 H := by
      rw [← bar_eq_one_iff (H.pow_mem hwH _), bar_pow hwH]
      exact h1
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H) ⟨w ^ 2 ^ k, h2⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have : (w ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    show w ^ 2 ^ (k + j) = 1
    rw [pow_add, pow_mul, this]
  have hnormY := le_normalizer_pCoreOf 2 Y
  have hWn : X ≤ Subgroup.normalizer (W : Set G) := by
    intro h hh
    have hhH : h ∈ H := hXH hh
    have hhY : bar H h ∈ Y := (mem_preimBar.mp hh).2
    have key : ∀ k ∈ X, ∀ w ∈ W, k * w * k⁻¹ ∈ W := by
      intro k hk w hw
      obtain ⟨hkH, hkY⟩ := mem_preimBar.mp hk
      obtain ⟨hwH, hwb⟩ := mem_preimBar.mp hw
      refine mem_preimBar.mpr ⟨H.mul_mem (H.mul_mem hkH hwH) (H.inv_mem hkH), ?_⟩
      rw [bar_mul (H.mul_mem hkH hwH) (H.inv_mem hkH), bar_mul hkH hwH, bar_inv hkH]
      exact (Subgroup.mem_normalizer_iff.mp (hnormY hkY) _).mp hwb
    refine B6.mem_normalizer_of_forall_mem (key h hh) (fun x hx => ?_)
    simpa using key h⁻¹ (X.inv_mem hh) x hx
  have hle : W ≤ pCoreOf 2 X := le_pCoreOf_of_le_normalizer 2 hWX hWn hWp
  exact hle (mem_preimBar.mpr ⟨hgH, hb⟩)

theorem mem_pCoreOf_preimBar_iff {H : Subgroup G} {Y : Subgroup (OTwoQuot H)} {g : G}
    (hg : g ∈ preimBar H Y) : g ∈ pCoreOf 2 (preimBar H Y) ↔ bar H g ∈ pCoreOf 2 Y :=
  ⟨bar_mem_pCoreOf, mem_pCoreOf_of_bar_mem hg⟩

end X1512

end CFSG.Quasithin
