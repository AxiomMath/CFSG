module

public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem pCoreOf_le_pCore_of_subnormal {Γ : Type*} [Group Γ] {K X : Subgroup Γ} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hX : X.Normal) :
    CFSG.Open.pCoreOf 2 K ≤ CFSG.pCore 2 Γ := by
  have h1 := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hKX hXK
  have hTop : (⊤ : Subgroup Γ) ≤ Subgroup.normalizer (X : Set Γ) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hX]
  have h2 := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 (le_top : X ≤ ⊤) hTop
  have h3 : CFSG.Open.pCoreOf 2 (⊤ : Subgroup Γ) = CFSG.pCore 2 Γ :=
    CFSG.pCore_map_iso 2 (Subgroup.topEquiv : (⊤ : Subgroup Γ) ≃* Γ)
  exact (h1.trans h2).trans h3.le

theorem eq_bot_of_normal_isPGroup_of_subnormal {Γ : Type*} [Group Γ] {K X : Subgroup Γ}
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hX : X.Normal)
    (hΓ : CFSG.pCore 2 Γ = ⊥) (S : Subgroup ↥K) (hS : S.Normal) (hS2 : IsPGroup 2 ↥S) :
    S = ⊥ := by
  have h1 : S ≤ CFSG.pCore 2 ↥K := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le hS2 le_rfl))
  have h2 : CFSG.Open.pCoreOf 2 K ≤ CFSG.pCore 2 Γ := pCoreOf_le_pCore_of_subnormal hKX hXK hX
  rw [hΓ] at h2
  have h3 : S.map K.subtype ≤ ⊥ := (Subgroup.map_mono h1).trans h2
  refine (Subgroup.eq_bot_iff_forall S).mpr fun x hx => ?_
  have h4 : K.subtype x ∈ S.map K.subtype := Subgroup.mem_map_of_mem _ hx
  have h5 := h3 h4
  rw [Subgroup.mem_bot] at h5
  exact Subtype.ext h5

theorem eq_bot_of_isPGroup_of_subnormal {Γ : Type*} [Group Γ] {K X : Subgroup Γ}
    (hKX : K ≤ X) (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hX : X.Normal)
    (hΓ : CFSG.pCore 2 Γ = ⊥) (hK : IsPGroup 2 ↥K) : K = ⊥ := by
  have h1 : (⊤ : Subgroup ↥K) = ⊥ :=
    eq_bot_of_normal_isPGroup_of_subnormal hKX hXK hX hΓ ⊤ inferInstance
      (hK.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup ↥K) ≃* ↥K).symm)
  refine (Subgroup.eq_bot_iff_forall K).mpr fun x hx => ?_
  have h2 : (⟨x, hx⟩ : ↥K) ∈ (⊤ : Subgroup ↥K) := Subgroup.mem_top _
  rw [h1, Subgroup.mem_bot] at h2
  exact congrArg Subtype.val h2

theorem commute_of_pCore_trivial {Γ : Type*} [Group Γ] {K X L : Subgroup Γ} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set Γ)) (hX : X.Normal) (hΓ : CFSG.pCore 2 Γ = ⊥)
    (hL : IsPGroup 2 ↥L) (hLK : L ≤ Subgroup.normalizer (K : Set Γ))
    (hKL : K ≤ Subgroup.normalizer (L : Set Γ)) : ∀ k ∈ K, ∀ l ∈ L, k * l = l * k := by
  have hnorm : K ≤ Subgroup.normalizer ((L ⊓ K : Subgroup Γ) : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hKL hk) x
    have h2 : x ∈ K ↔ k * x * k⁻¹ ∈ K := by
      constructor
      · intro hx
        exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
      · intro hx
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
        simpa [mul_assoc] using this
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hS : ((L ⊓ K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnorm
  have hS2 : IsPGroup 2 ↥((L ⊓ K).subgroupOf K) :=
    ((hL.to_le (inf_le_left : L ⊓ K ≤ L)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : L ⊓ K ≤ K)).symm)
  have hbot := eq_bot_of_normal_isPGroup_of_subnormal hKX hXK hX hΓ _ hS hS2
  intro k hk l hl
  have hc1 : k * l * k⁻¹ * l⁻¹ ∈ L := by
    have h1 : k * l * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hKL hk) l).mp hl
    exact L.mul_mem h1 (L.inv_mem hl)
  have hc2 : k * l * k⁻¹ * l⁻¹ ∈ K := by
    have h1 : l * k⁻¹ * l⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hLK hl) k⁻¹).mp (K.inv_mem hk)
    have := K.mul_mem hk h1
    simpa [mul_assoc] using this
  have h3 : (⟨k * l * k⁻¹ * l⁻¹, hc2⟩ : ↥K) ∈ (L ⊓ K).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr ⟨hc1, hc2⟩
  rw [hbot, Subgroup.mem_bot] at h3
  have h4 : k * l * k⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h3
  calc k * l = (k * l * k⁻¹ * l⁻¹) * l * k := by group
    _ = l * k := by rw [h4, one_mul]

theorem exists_hom_GL_two_of_stable {Γ : Type*} [Group Γ] {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] (ρ : Γ →* (E ≃ₗ[K] E)) (W : Submodule K E) (hW : Module.finrank K W = 2)
    (hstab : ∀ g, ∀ w ∈ W, ρ g w ∈ W) :
    ∃ f : Γ →* Matrix.GeneralLinearGroup (Fin 2) K, ∀ g, f g = 1 ↔ ∀ w ∈ W, ρ g w = w := by
  classical
  haveI : Module.Finite K W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) K W := Module.finBasisOfFinrankEq K W hW
  let R : Γ →* Module.End K W :=
    { toFun := fun g => (ρ g : E →ₗ[K] E).restrict (hstab g)
      map_one' := by
        ext w
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext w
        simp [LinearMap.restrict_apply] }
  let e : Module.End K W ≃ₐ[K] Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrixAlgEquiv b
  refine ⟨(Units.map (e : Module.End K W →* Matrix (Fin 2) (Fin 2) K)).comp R.toHomUnits,
    fun g => ?_⟩
  have h1 : (Units.map (e : Module.End K W →* Matrix (Fin 2) (Fin 2) K)).comp R.toHomUnits g = 1
      ↔ R.toHomUnits g = 1 := by
    rw [MonoidHom.comp_apply]
    exact map_eq_one_iff _ (Units.map_injective e.injective)
  rw [h1, Units.ext_iff]
  simp only [MonoidHom.coe_toHomUnits, Units.val_one]
  constructor
  · intro h w hw
    have := congrArg (fun f : Module.End K W => (f ⟨w, hw⟩ : E)) h
    simpa [R, LinearMap.restrict_apply] using this
  · intro h
    ext w
    simp [R, LinearMap.restrict_apply, h w w.2]

end CFSG.RankThree.GF2n.Stroth80
