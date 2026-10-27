module

public import CFSG.Quasithin.EmptyFaithful.SBc15F3Cls
public import CFSG.Quasithin.EmptyFaithful.S146zRL3

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace SBc15

namespace L3

theorem inner_of_conj_transfer {G : Type*} [Group G] {Y : Subgroup G} (g : G) {φ : MulAut G}
    (hφ : ∀ y ∈ Y, φ y ∈ Y)
    (H : ∀ ψ : MulAut G, (∀ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom,
      ψ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom) → ψ ∈ (MulAut.conj : G →* MulAut G).range) :
    φ ∈ (MulAut.conj : G →* MulAut G).range := by
  have hψY : ∀ y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom,
      (MulAut.conj g⁻¹ * φ * MulAut.conj g) y ∈ Y.map (MulAut.conj g⁻¹).toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨φ y, hφ y hy, ?_⟩
    simp [MulAut.mul_apply, MulAut.conj_apply, mul_assoc]
  obtain ⟨t, ht⟩ := H _ hψY
  refine ⟨g * t * g⁻¹, ?_⟩
  rw [map_mul, map_mul, ht, map_inv]
  group

theorem aut_SL32_inner_of_normalizes {R Y : Subgroup SL32} (hR : IsSylowTwoOf R ⊤)
    (hRY : R ≤ Subgroup.normalizer (Y : Set SL32)) (hO : oTwoUpper Y = Y) (hY : Y ≠ ⊥)
    (h7 : ¬ 7 ∣ Nat.card Y) {φ : MulAut SL32} (hφ : ∀ y ∈ Y, φ y ∈ Y) :
    φ ∈ (MulAut.conj : SL32 →* MulAut SL32).range := by
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf isSylowTwoOf_R0 hR
  have hRmap : R.map (MulAut.conj g⁻¹).toMonoidHom = R0 := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨r, hr, rfl⟩
      have := (hg r).mp hr
      simpa [MulAut.conj_apply] using this
    · intro hx
      refine ⟨g * x * g⁻¹, (hg _).mpr (by simpa [mul_assoc] using hx), ?_⟩
      simp [mul_assoc]
  have hN' : R0 ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup SL32) : Set SL32) := by
    rw [← hRmap]
    exact map_le_normalizer_map _ hRY
  have hO' : oTwoUpper (Y.map (MulAut.conj g⁻¹).toMonoidHom) =
      Y.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [oTwoUpper_map, hO]
  have hY0' : Y.map (MulAut.conj g⁻¹).toMonoidHom ≠ ⊥ := fun h =>
    hY ((Subgroup.map_eq_bot_iff_of_injective Y (MulAut.conj g⁻¹).injective).mp h)
  have h7' : ¬ 7 ∣ Nat.card (Y.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  refine inner_of_conj_transfer g hφ fun ψ hψ => ?_
  rcases classify hN' hO' hY0' h7' with h | h
  · rw [h] at hψ
    exact inner_of_stab_A4a hψ
  · rw [h] at hψ
    exact inner_of_stab_A4b hψ

end L3

end SBc15

open SBc15.L3 in
theorem l3_aut_inner_of_normalizes {L : Type*} [Group L] [Finite L]
    (hL : Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {R Y : Subgroup L} (hR : IsPGroup 2 R) (hRi : ¬ 2 ∣ R.index)
    (hRY : R ≤ Subgroup.normalizer (Y : Set L)) (hO : oTwoUpper Y = Y) (hY : Y ≠ ⊥)
    (h7 : ¬ 7 ∣ Nat.card Y) (φ : MulAut L) (hφ : Y.map φ.toMonoidHom = Y) :
    φ ∈ (MulAut.conj : L →* MulAut L).range := by
  obtain ⟨e⟩ := hL
  have hsyl : IsSylowTwoOf (R.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hR.map e.toMonoidHom, ?_⟩
    rw [show ((R.map e.toMonoidHom).subgroupOf ⊤).index = (R.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right (H := R.map e.toMonoidHom)]
    rwa [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective R]
  have hRY' : R.map e.toMonoidHom ≤ Subgroup.normalizer
      ((Y.map e.toMonoidHom : Subgroup _) : Set _) := SBc15.map_le_normalizer_map _ hRY
  have hO' : oTwoUpper (Y.map e.toMonoidHom) = Y.map e.toMonoidHom := by
    rw [oTwoUpper_map, hO]
  have hY0' : Y.map e.toMonoidHom ≠ ⊥ := fun h =>
    hY ((Subgroup.map_eq_bot_iff_of_injective Y e.injective).mp h)
  have h7' : ¬ 7 ∣ Nat.card (Y.map e.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective e.injective]
  have hφ' : ∀ y ∈ Y.map e.toMonoidHom, (MulAut.congr e φ) y ∈ Y.map e.toMonoidHom := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨φ y, ?_, ?_⟩
    · exact hφ ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hy
    · simp [MulAut.congr_apply]
  obtain ⟨t, ht⟩ := aut_SL32_inner_of_normalizes hsyl hRY' hO' hY0' h7' hφ'
  refine ⟨e.symm t, MulEquiv.ext fun x => ?_⟩
  have h1 : (MulAut.congr e φ) (e x) = t * e x * t⁻¹ := by
    rw [← MulAut.conj_apply, ht]
  have h2 : φ x = e.symm (t * e x * t⁻¹) := by
    rw [← h1]
    simp [MulAut.congr_apply]
  rw [MulAut.conj_apply, h2]
  simp

end CFSG.Quasithin
