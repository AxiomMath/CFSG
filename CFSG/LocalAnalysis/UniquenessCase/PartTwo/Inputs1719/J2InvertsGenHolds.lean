module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsElevenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2InvertsGenSpec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2ModelHom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.J2KFact

theorem k_J2InvertsGen_of_model
    (hM : InvertsGenModel) : K_J2InvertsGen := by
  classical
  intro Y _ _ K hKn hK a ha2 ⟨k, hk, hak⟩
  have := hKn
  obtain ⟨e0⟩ := hK
  let θ : ↥K ≃* ↥P := e0.trans nativeEquivP
  let ρ : Y →* Equiv.Perm (Fin 315) := j2Cover_autModel.embed K θ
  have hρK : ∀ s : ↥K, ρ s = θ s := fun s => j2Cover_autModel.embed_coe K θ s
  have hρa2 : ρ a * ρ a = 1 := by rw [← map_mul, ha2, map_one]
  have hρa1 : ρ a ≠ 1 := by
    intro h
    have hmem : a ∈ ρ.ker := h
    rw [embed_ker_eq_centralizer] at hmem
    exact hak ((Subgroup.mem_centralizer_iff.1 hmem k hk).symm)
  have hρord : orderOf (ρ a) = 2 := orderOf_eq_prime (by rw [pow_two, hρa2]) hρa1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcls, -⟩ :=
    CFSG.ComponentClassification.J2Cover.ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, c, hc, e⟩ := hcls (ρ a) (j2Cover_autModel.embed_mem K θ a) hρord
  obtain ⟨x₀, hx₀, g₀, hg₀, hord, hgen⟩ := hM r hr
  let x₁ : ↥P := ⟨c * x₀ * c⁻¹, P.mul_mem (P.mul_mem hc hx₀) (P.inv_mem hc)⟩
  let g₁ : ↥P := ⟨c * g₀ * c⁻¹, P.mul_mem (P.mul_mem hc hg₀) (P.inv_mem hc)⟩
  have hxK : ((θ.symm x₁ : ↥K) : Y) ∈ K := (θ.symm x₁).2
  have hgK : ((θ.symm g₁ : ↥K) : Y) ∈ K := (θ.symm g₁).2
  have hρx : ρ (θ.symm x₁ : ↥K) = c * x₀ * c⁻¹ := by rw [hρK, MulEquiv.apply_symm_apply]
  have hρg : ρ (θ.symm g₁ : ↥K) = c * g₀ * c⁻¹ := by rw [hρK, MulEquiv.apply_symm_apply]
  set x : Y := ((θ.symm x₁ : ↥K) : Y) with hxdef
  set g : Y := ((θ.symm g₁ : ↥K) : Y) with hgdef
  have hyK : x⁻¹ * (a * x * a⁻¹) ∈ K := K.mul_mem (K.inv_mem hxK) (hKn.conj_mem x hxK a)
  have hy'K : g * (x⁻¹ * (a * x * a⁻¹)) * g⁻¹ ∈ K :=
    K.mul_mem (K.mul_mem hgK hyK) (K.inv_mem hgK)
  have hρy : ρ (x⁻¹ * (a * x * a⁻¹)) = c * (x₀⁻¹ * (r * x₀ * r⁻¹)) * c⁻¹ := by
    simp only [map_mul, map_inv, e, hρx]
    group
  have hinj : ∀ u ∈ K, ∀ v ∈ K, ρ u = ρ v → u = v := by
    intro u hu v hv huv
    have h1 : θ ⟨u, hu⟩ = θ ⟨v, hv⟩ := by
      apply Subtype.ext
      rw [← hρK, ← hρK]
      exact huv
    exact congrArg Subtype.val (θ.injective h1)
  have hle : Subgroup.closure ({x⁻¹ * (a * x * a⁻¹), g * (x⁻¹ * (a * x * a⁻¹)) * g⁻¹} :
      Set Y) ≤ K := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hyK
    · exact hy'K
  refine ⟨x, hxK, g, hgK, ?_, le_antisymm hle ?_⟩
  · have h1 : orderOf (x⁻¹ * (a * x * a⁻¹)) = orderOf (ρ (x⁻¹ * (a * x * a⁻¹))) := by
      have h2 : ρ (x⁻¹ * (a * x * a⁻¹)) = ((θ ⟨_, hyK⟩ : ↥P) : Equiv.Perm (Fin 315)) :=
        hρK ⟨_, hyK⟩
      rw [h2, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    rw [h1, hρy]
    have h3 := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
      (x₀⁻¹ * (r * x₀ * r⁻¹))
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
    rw [h3]
    exact hord
  · intro u hu
    have hlift : ∀ q ∈ Subgroup.closure ({x₀⁻¹ * (r * x₀ * r⁻¹),
        g₀ * (x₀⁻¹ * (r * x₀ * r⁻¹)) * g₀⁻¹} : Set (Equiv.Perm (Fin 315))),
        ∃ h ∈ Subgroup.closure ({x⁻¹ * (a * x * a⁻¹), g * (x⁻¹ * (a * x * a⁻¹)) * g⁻¹} :
          Set Y), ρ h = c * q * c⁻¹ := by
      intro q hq
      induction hq using Subgroup.closure_induction with
      | mem z hz =>
        rcases hz with rfl | rfl
        · exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), hρy⟩
        · refine ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), ?_⟩
          simp only [map_mul, map_inv, hρy, hρg]
          group
      | one => exact ⟨1, Subgroup.one_mem _, by simp⟩
      | mul z w _ _ hz hw =>
        obtain ⟨h1, hh1, e1⟩ := hz
        obtain ⟨h2, hh2, e2⟩ := hw
        exact ⟨h1 * h2, Subgroup.mul_mem _ hh1 hh2, by rw [map_mul, e1, e2]; group⟩
      | inv z _ hz =>
        obtain ⟨h1, hh1, e1⟩ := hz
        exact ⟨h1⁻¹, Subgroup.inv_mem _ hh1, by rw [map_inv, e1]; group⟩
    have hρu : ρ u ∈ P := by
      have := hρK ⟨u, hu⟩
      rw [this]
      exact (θ ⟨u, hu⟩).2
    have hq : c⁻¹ * ρ u * c ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hc) hρu) hc
    rw [← hgen] at hq
    obtain ⟨h, hh, eh⟩ := hlift _ hq
    have hhu : h = u := hinj h (hle hh) u hu (by rw [eh]; group)
    rw [← hhu]
    exact hh

theorem k_J2InvertsGen_holds :
    K_J2InvertsGen :=
  k_J2InvertsGen_of_model invertsGenModel_holds

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
