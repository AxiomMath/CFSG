module

public import CFSG.LocalAnalysis.StandardType.StarFour.FrameModel
public import CFSG.LocalAnalysis.StandardType.StarFour.FrameNesting
public import CFSG.LocalAnalysis.StandardType.StarFour.ItemFour
public import CFSG.LinearAlgebra.RootGroupSL.EmbItemFour

public section

namespace CFSG.StandardType.StarFour

open CFSG.LinearAlgebra.RootGroupSL CFSG.Open CFSG.StandardType

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

theorem exists_mem_range_mul_inv_mem_centralizer {P : Type} [CommGroup P]
    (η : P →* SpecialLinearGroup F V) (fr : SemiFrame F (groupRep η)) (i : Fin fr.r)
    (hm : 3 ≤ fr.m i) (hc : 2 ≤ Module.finrank F (fr.E i))
    (hcop : Nat.Coprime (Module.finrank F V) (Nat.card F - 1))
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (U : Subgroup X)
    (hU₁ : ggCenterOf (pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X))) ≤ U)
    (hU₂ : U ≤ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X)))
    (hU₃ : U ≠ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X)))
    (hU₄ : ¬ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer
      (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X)) ≤
        Subgroup.centralizer (U : Set X))
    (hU₅ : ψ.range ⊓ Subgroup.normalizer
      (((fr.blockRoot i (by omega)).map ψ : Subgroup X) : Set X) ≤
        Subgroup.normalizer (U : Set X))
    (g : X) (hgJ : g ∈ Subgroup.centralizer (((fr.slOnBlock i).map ψ : Subgroup X) : Set X))
    (hgU : g ∈ Subgroup.normalizer (U : Set X)) :
    ∃ h ∈ ψ.range,
      g * h⁻¹ ∈ Subgroup.centralizer ((((fr.slOnBlock i).map ψ ⊔ U : Subgroup X)) : Set X) := by
  classical
  have hm0 : 2 ≤ fr.m i := by omega
  let ι : fr.E i →ₗ[F] V := fr.blockIota i (fr.idx0 i hm0)
  let π : V →ₗ[F] fr.E i := fr.blockPi i (fr.idx1 i hm0)
  let hzero : ∀ t, π (ι t) = 0 := fun t => fr.blockPi_blockIota_ne i (fr.idx0_ne_idx1 i hm0) t
  have hι : Function.Injective ι := fr.blockIota_injective i (fr.idx0 i hm0)
  have hπ : Function.Surjective π := fun t =>
    ⟨fr.blockIota i (fr.idx1 i hm0) t, fr.blockPi_blockIota_self i (fr.idx1 i hm0) t⟩
  have hfinrankVJ : Module.finrank F (Fin (fr.m i) → fr.E i) =
      fr.m i * Module.finrank F (fr.E i) := by
    rw [Module.finrank_pi_fintype]
    simp [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hVprod : Module.finrank F V =
      Module.finrank F (Fin (fr.m i) → fr.E i) + Module.finrank F (fr.blockCompl i) := by
    rw [LinearEquiv.finrank_eq (fr.modelEquiv i), Module.finrank_prod]
  have hlt : 2 * Module.finrank F (fr.E i) <
      Module.finrank F (Fin (fr.m i) → fr.E i) := by
    rw [hfinrankVJ]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hV : 2 * Module.finrank F (fr.E i) < Module.finrank F V := by
    rw [hVprod]
    exact lt_of_lt_of_le hlt (Nat.le_add_right _ _)
  have hUcases : U = (datumU1 ι).map ψ ∨ U = (datumU2 π).map ψ :=
    eq_map_datumU_of_pCore ψ hψ hc ι π hzero hι hπ hV U hU₁ hU₂ hU₃ hU₄ hU₅
  let L : V ≃ₗ[F] ((Fin (fr.m i) → fr.E i) × fr.blockCompl i) := fr.modelEquiv i
  let T : SpecialLinearGroup F V ≃*
      SpecialLinearGroup F ((Fin (fr.m i) → fr.E i) × fr.blockCompl i) :=
    SpecialLinearGroup.congr_linearEquiv L
  let Θ : SpecialLinearGroup F ((Fin (fr.m i) → fr.E i) × fr.blockCompl i) →* X :=
    ψ.comp T.symm.toMonoidHom
  have hΘ : Function.Injective Θ := hψ.comp T.symm.injective
  have hcomp : Θ.comp T.toMonoidHom = ψ := by
    ext x
    simp only [MonoidHom.comp_apply]
    show ψ (T.symm (T x)) = ψ x
    rw [MulEquiv.symm_apply_apply]
  have hJΘ : (modelJ F (fr.E i) (Fin (fr.m i) → fr.E i) (fr.blockCompl i)).map Θ =
      (fr.slOnBlock i).map ψ := by
    rw [← SemiFrame.map_slOnBlock_modelEquiv fr i, Subgroup.map_map, hcomp]
  have hgJ' : g ∈ Subgroup.centralizer
      (((modelJ F (fr.E i) (Fin (fr.m i) → fr.E i) (fr.blockCompl i)).map Θ :
        Subgroup X) : Set X) := by
    rw [hJΘ]
    exact hgJ
  have hm' : 3 ≤ Module.finrank (fr.E i) (Fin (fr.m i) → fr.E i) := by
    simpa using hm
  have hcop' : Nat.Coprime
      (Module.finrank F ((Fin (fr.m i) → fr.E i) × fr.blockCompl i)) (Nat.card F - 1) := by
    rw [← LinearEquiv.finrank_eq (fr.modelEquiv i)]
    exact hcop
  rcases hUcases with hU1 | hU2
  ·
    let e₀ : Fin (fr.m i) → fr.E i := Pi.single (fr.idx0 i hm0) 1
    let U₀ : Subgroup (SpecialLinearGroup F ((Fin (fr.m i) → fr.E i) × fr.blockCompl i)) :=
      datumU1 (modelIota (E := fr.E i) F (fr.blockCompl i) e₀)
    have he₀ : e₀ ≠ 0 := by
      intro h
      have h1 := congrFun h (fr.idx0 i hm0)
      simp [e₀] at h1
    have hiota : L.toLinearMap ∘ₗ ι =
        modelIota (E := fr.E i) F (fr.blockCompl i) e₀ :=
      SemiFrame.modelEquiv_comp_blockIota fr i (fr.idx0 i hm0)
    have hUeq : U = U₀.map Θ := by
      rw [hU1, ← hcomp, ← Subgroup.map_map, map_datumU1_congr L ι, hiota]
    have hgU' : g ∈ Subgroup.normalizer ((U₀.map Θ : Subgroup X) : Set X) := by
      rw [← hUeq]
      exact hgU
    obtain ⟨h', hh'⟩ := exists_mem_centralizer_of_centralizer_normalizer (l₀ := 0)
      hm' hc hcop' U₀ (Or.inl ⟨he₀, rfl⟩) Θ hΘ g hgJ' hgU'
    refine ⟨Θ h', ⟨T.symm h', rfl⟩, ?_⟩
    have hmap : (modelJ F (fr.E i) (Fin (fr.m i) → fr.E i) (fr.blockCompl i) ⊔ U₀).map Θ =
        (fr.slOnBlock i).map ψ ⊔ U := by
      rw [Subgroup.map_sup, hJΘ, ← hUeq]
    rw [hmap, map_inv Θ h'] at hh'
    exact hh'
  ·
    let l₀ : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i] fr.E i := LinearMap.proj (fr.idx1 i hm0)
    let U₀ : Subgroup (SpecialLinearGroup F ((Fin (fr.m i) → fr.E i) × fr.blockCompl i)) :=
      datumU2 (modelPi (E := fr.E i) F (fr.blockCompl i) l₀)
    have hl₀ : l₀ ≠ 0 := by
      intro h
      have h1 : l₀ (Pi.single (fr.idx1 i hm0) 1) = 1 := by
        simp [l₀]
      rw [h] at h1
      simp at h1
    have hpi : π ∘ₗ L.symm.toLinearMap =
        modelPi (E := fr.E i) F (fr.blockCompl i) l₀ :=
      SemiFrame.blockPi_comp_modelEquiv_symm fr i (fr.idx1 i hm0)
    have hUeq : U = U₀.map Θ := by
      rw [hU2, ← hcomp, ← Subgroup.map_map, map_datumU2_congr L π, hpi]
    have hgU' : g ∈ Subgroup.normalizer ((U₀.map Θ : Subgroup X) : Set X) := by
      rw [← hUeq]
      exact hgU
    obtain ⟨h', hh'⟩ := exists_mem_centralizer_of_centralizer_normalizer (e₀ := 0)
      hm' hc hcop' U₀ (Or.inr ⟨hl₀, rfl⟩) Θ hΘ g hgJ' hgU'
    refine ⟨Θ h', ⟨T.symm h', rfl⟩, ?_⟩
    have hmap : (modelJ F (fr.E i) (Fin (fr.m i) → fr.E i) (fr.blockCompl i) ⊔ U₀).map Θ =
        (fr.slOnBlock i).map ψ ⊔ U := by
      rw [Subgroup.map_sup, hJΘ, ← hUeq]
    rw [hmap, map_inv Θ h'] at hh'
    exact hh'

end CFSG.StandardType.StarFour
