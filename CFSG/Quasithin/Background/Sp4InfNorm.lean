module

public import CFSG.Quasithin.Background.Sp4InfDer
public import CFSG.Quasithin.Background.HSp4Pair
public import Certificates.Certificate8068
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof

public section

namespace CFSG.Quasithin

namespace Sp4Inf

open Equiv
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H CFSG.Quasithin.H.PairG Matrix
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauEquiv)

theorem exists_matAut_zmod_two (a : MulAut (StdMod I4 (ZMod 2))) :
    ∃ A : GL I4 (ZMod 2), a = matAut A := by
  have h0 : toAddMap a 0 = 0 := by
    have := map_one a
    simp [toAddMap]
  refine exists_matAut_of_mem_linSub (mem_linSub.2 fun c v => ?_)
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp [h0]
  · simp

theorem matAut_inv' (g : GL I4 (ZMod 2)) : matAut g⁻¹ = (matAut g)⁻¹ := map_inv matHom g

@[expose] def toGL (D : Subgroup (StatedSp 2 (ZMod 2))) : ↥D →* GL I4 (ZMod 2) :=
  (StatedSp 2 (ZMod 2)).subtype.comp D.subtype

theorem toGL_injective (D : Subgroup (StatedSp 2 (ZMod 2))) : Function.Injective (toGL D) :=
  (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)

theorem toGL_apply (D : Subgroup (StatedSp 2 (ZMod 2))) (γ : ↥D) :
    toGL D γ = ((γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) := rfl

theorem tau_mem_of_mem {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    {x : StatedSp 2 (ZMod 2)} (hx : x ∈ D) : tauSp x ∈ D :=
  map_le_of_isAlt6Sub hD tauSp (Subgroup.mem_map_of_mem tauSp hx)

theorem tauInv_mem_of_mem {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    {x : StatedSp 2 (ZMod 2)} (hx : x ∈ D) : tauEquiv.symm x ∈ D :=
  map_le_of_isAlt6Sub hD tauEquiv.symm.toMonoidHom (Subgroup.mem_map_of_mem tauEquiv.symm.toMonoidHom hx)

theorem mem_statedSp_of_normalizes
    {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    (A : GL I4 (ZMod 2))
    (h₁ : ∀ γ ∈ D, ∃ δ ∈ D, A * (γ : GL I4 (ZMod 2)) * A⁻¹ = (δ : GL I4 (ZMod 2)))
    (h₂ : ∀ δ ∈ D, ∃ γ ∈ D, A⁻¹ * (δ : GL I4 (ZMod 2)) * A = (γ : GL I4 (ZMod 2))) :
    ∃ α : StatedSp 2 (ZMod 2), (α : GL I4 (ZMod 2)) = A := by
  classical
  choose f hfD hf using h₁
  let ψ₀ : ↥D → ↥D := fun γ => ⟨f γ.1 γ.2, hfD γ.1 γ.2⟩
  have hψ₀ : ∀ γ : ↥D, toGL D (ψ₀ γ) = A * toGL D γ * A⁻¹ := fun γ => (hf γ.1 γ.2).symm
  let ψ : ↥D →* ↥D :=
    { toFun := ψ₀
      map_one' := toGL_injective D (by simp [hψ₀])
      map_mul' := fun γ γ' => toGL_injective D (by
        rw [hψ₀, map_mul, map_mul, hψ₀, hψ₀]
        group) }
  have hinj : Function.Injective ψ := by
    intro γ γ' h
    apply toGL_injective D
    have h1 : toGL D (ψ₀ γ) = toGL D (ψ₀ γ') := congrArg (toGL D) h
    rw [hψ₀, hψ₀] at h1
    simpa using h1
  have hsurj : Function.Surjective ψ := by
    intro δ
    obtain ⟨γ, hγ, hγδ⟩ := h₂ δ.1 δ.2
    refine ⟨⟨γ, hγ⟩, toGL_injective D ?_⟩
    show toGL D (ψ₀ ⟨γ, hγ⟩) = toGL D δ
    rw [hψ₀, toGL_apply, toGL_apply, ← hγδ]
    group
  let ψe : ↥D ≃* ↥D := MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  let ιD : ↥D ≃* ↥(alternatingGroup (Fin 6)) :=
    (iotaSp.subgroupMap D).trans (MulEquiv.subgroupCongr hD)
  let c : MulAut ↥(alternatingGroup (Fin 6)) := ιD.symm.trans (ψe.trans ιD)
  have hc : ∀ γ : ↥D, c (ιD γ) = ιD (ψe γ) := fun γ => by simp [c]
  have hιD : ∀ γ : ↥D, ((ιD γ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      iotaSp (γ : StatedSp 2 (ZMod 2)) := fun γ => rfl
  have hψe : ∀ γ : ↥D, toGL D (ψe γ) = A * toGL D γ * A⁻¹ := hψ₀
  rcases ext_alt6 c with ⟨g, hg⟩ | ⟨γ₁, hγ₁⟩
  ·
    have hconj : ∀ γ : ↥D, toGL D (ψe γ) = ((iotaSp.symm g : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) *
        toGL D γ * ((iotaSp.symm g : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ := by
      intro γ
      have h1 := hg (ιD γ)
      rw [hc, hιD, hιD] at h1
      have h2 : ((ψe γ : ↥D) : StatedSp 2 (ZMod 2)) =
          iotaSp.symm g * (γ : StatedSp 2 (ZMod 2)) * (iotaSp.symm g)⁻¹ := by
        apply iotaSp.injective
        rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [toGL_apply, h2]
      rfl
    set α : StatedSp 2 (ZMod 2) := iotaSp.symm g with hα
    have hcomm : ∀ γ ∈ D, ∀ x, matAut ((α : GL I4 (ZMod 2))⁻¹ * A) (matAut ((γ : StatedSp 2 (ZMod 2)) :
          GL I4 (ZMod 2)) x) = matAut ((γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))
          (matAut ((α : GL I4 (ZMod 2))⁻¹ * A) x) := by
      intro γ hγ x
      have h3 := (hψe ⟨γ, hγ⟩).symm.trans (hconj ⟨γ, hγ⟩)
      simp only [toGL_apply] at h3
      have h4 : (α : GL I4 (ZMod 2))⁻¹ * A * (γ : GL I4 (ZMod 2)) =
          (γ : GL I4 (ZMod 2)) * ((α : GL I4 (ZMod 2))⁻¹ * A) := by
        have h5 : A * (γ : GL I4 (ZMod 2)) = (α : GL I4 (ZMod 2)) * (γ : GL I4 (ZMod 2)) *
            (α : GL I4 (ZMod 2))⁻¹ * A := by
          calc A * (γ : GL I4 (ZMod 2)) = (A * (γ : GL I4 (ZMod 2)) * A⁻¹) * A := by group
            _ = _ := by rw [h3]
        calc (α : GL I4 (ZMod 2))⁻¹ * A * (γ : GL I4 (ZMod 2))
            = (α : GL I4 (ZMod 2))⁻¹ * (A * (γ : GL I4 (ZMod 2))) := by group
          _ = _ := by rw [h5]; group
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← matAut_mul', ← matAut_mul', h4]
    have h1 : matAut ((α : GL I4 (ZMod 2))⁻¹ * A) = 1 := eq_one_of_commute hD _ hcomm
    have h2 : (α : GL I4 (ZMod 2))⁻¹ * A = 1 := by
      apply matHom_injective
      rw [map_one]
      exact h1
    exact ⟨α, inv_mul_eq_one.1 h2⟩
  ·
    exfalso
    have hrel : ∀ γ : ↥D, toGL D (ψe γ) = ((γ₁ * tauSp (γ : StatedSp 2 (ZMod 2)) * γ₁⁻¹ :
        StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) := by
      intro γ
      have h1 := hγ₁ (ιD γ)
      rw [hc, hιD, hιD, MulEquiv.symm_apply_apply] at h1
      have h2 : ((ψe γ : ↥D) : StatedSp 2 (ZMod 2)) =
          γ₁ * tauSp (γ : StatedSp 2 (ZMod 2)) * γ₁⁻¹ := iotaSp.injective h1
      rw [toGL_apply, h2]
    refine no_tau_iso hD (matAut ((γ₁ : GL I4 (ZMod 2))⁻¹ * A)) (fun γ hγ x => ?_)
    have h3 := (hψe ⟨γ, hγ⟩).symm.trans (hrel ⟨γ, hγ⟩)
    simp only [toGL_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h3
    have h4 : (γ₁ : GL I4 (ZMod 2))⁻¹ * A * (γ : GL I4 (ZMod 2)) =
        ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) * ((γ₁ : GL I4 (ZMod 2))⁻¹ * A) := by
      have h5 : A * (γ : GL I4 (ZMod 2)) = (γ₁ : GL I4 (ZMod 2)) *
          ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) * (γ₁ : GL I4 (ZMod 2))⁻¹ * A := by
        calc A * (γ : GL I4 (ZMod 2)) = (A * (γ : GL I4 (ZMod 2)) * A⁻¹) * A := by group
          _ = _ := by rw [h3]
      calc (γ₁ : GL I4 (ZMod 2))⁻¹ * A * (γ : GL I4 (ZMod 2))
          = (γ₁ : GL I4 (ZMod 2))⁻¹ * (A * (γ : GL I4 (ZMod 2))) := by group
        _ = _ := by rw [h5]; group
    show matAut ((γ₁ : GL I4 (ZMod 2))⁻¹ * A) (matAut (γ : GL I4 (ZMod 2)) x) =
      matAut ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) (matAut ((γ₁ : GL I4 (ZMod 2))⁻¹ * A) x)
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← matAut_mul', ← matAut_mul', h4]

theorem mem_pairNormSp_of_normalizes
    {D : Subgroup (StatedSp 2 (ZMod 2))} (hD : IsAlt6Sub D)
    {x : MulAut (PairMod I4 (ZMod 2))} (hx : x ∈ pairSub I4 (ZMod 2))
    (h₁ : ∀ γ ∈ D, ∃ δ ∈ D,
      x * pairHom (StatedSp 2 (ZMod 2)) tauSp γ * x⁻¹ = pairHom (StatedSp 2 (ZMod 2)) tauSp δ)
    (h₂ : ∀ γ ∈ D, ∃ δ ∈ D,
      x⁻¹ * pairHom (StatedSp 2 (ZMod 2)) tauSp γ * x = pairHom (StatedSp 2 (ZMod 2)) tauSp δ) :
    x ∈ Sp4.pairNormSp (ZMod 2) := by
  obtain ⟨a, b, rfl⟩ := mem_pairSub_iff.mp hx
  obtain ⟨A, rfl⟩ := exists_matAut_zmod_two a
  obtain ⟨B, rfl⟩ := exists_matAut_zmod_two b
  have conj_eq : ∀ (P M N : GL I4 (ZMod 2)), matAut P * matAut M * (matAut P)⁻¹ = matAut N →
      P * M * P⁻¹ = N := by
    intro P M N h
    apply matHom_injective
    rw [map_mul, map_mul, map_inv]
    exact h
  have key₁ : ∀ γ ∈ D, ∃ δ ∈ D, A * (γ : GL I4 (ZMod 2)) * A⁻¹ = (δ : GL I4 (ZMod 2)) ∧
      B * ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) * B⁻¹ =
        ((tauSp δ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) := by
    intro γ hγ
    obtain ⟨δ, hδ, h⟩ := h₁ γ hγ
    rw [pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul] at h
    obtain ⟨h1, h2⟩ := pairAut_injective h
    exact ⟨δ, hδ, conj_eq _ _ _ h1, conj_eq _ _ _ h2⟩
  have key₂ : ∀ γ ∈ D, ∃ δ ∈ D, A⁻¹ * (γ : GL I4 (ZMod 2)) * A = (δ : GL I4 (ZMod 2)) ∧
      B⁻¹ * ((tauSp γ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) * B =
        ((tauSp δ : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) := by
    intro γ hγ
    obtain ⟨δ, hδ, h⟩ := h₂ γ hγ
    rw [pairHom_apply, pairHom_apply, pairAut_inv, pairAut_mul, pairAut_mul] at h
    obtain ⟨h1, h2⟩ := pairAut_injective h
    refine ⟨δ, hδ, conj_eq A⁻¹ _ _ ?_, conj_eq B⁻¹ _ _ ?_⟩
    · rw [matAut_inv', inv_inv]
      exact h1
    · rw [matAut_inv', inv_inv]
      exact h2
  obtain ⟨α, hα⟩ := mem_statedSp_of_normalizes hD A
    (fun γ hγ => (key₁ γ hγ).imp fun δ ⟨hδ, h, _⟩ => ⟨hδ, h⟩)
    (fun δ hδ => (key₂ δ hδ).imp fun γ ⟨hγ, h, _⟩ => ⟨hγ, h⟩)
  obtain ⟨β, hβ⟩ := mem_statedSp_of_normalizes hD B
    (fun γ' hγ' => by
      obtain ⟨δ, hδ, -, h⟩ := key₁ _ (tauInv_mem_of_mem hD hγ')
      rw [tauSp_tauEquiv_symm] at h
      exact ⟨tauSp δ, tau_mem_of_mem hD hδ, h⟩)
    (fun δ' hδ' => by
      obtain ⟨γ, hγ, -, h⟩ := key₂ _ (tauInv_mem_of_mem hD hδ')
      rw [tauSp_tauEquiv_symm] at h
      exact ⟨tauSp γ, tau_mem_of_mem hD hγ, h⟩)
  subst hα
  subst hβ
  have hBτ : β = tauSp α := by
    have hcomm : ∀ γ' ∈ D, ∀ y, matAut (((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ *
        (β : GL I4 (ZMod 2))) (matAut ((γ' : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) y) =
        matAut ((γ' : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) (matAut
          (((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2))) y) := by
      intro γ' hγ' y
      obtain ⟨δ, hδ, h3, h4⟩ := key₁ _ (tauInv_mem_of_mem hD hγ')
      rw [tauSp_tauEquiv_symm] at h4
      have h5 : δ = α * tauEquiv.symm γ' * α⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← h3]
      rw [h5, map_mul, map_mul, map_inv, tauSp_tauEquiv_symm] at h4
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      have h6 : ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2)) *
          (γ' : GL I4 (ZMod 2)) = (γ' : GL I4 (ZMod 2)) *
          (((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2))) := by
        have h7 : (β : GL I4 (ZMod 2)) * (γ' : GL I4 (ZMod 2)) =
            ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2)) * (γ' : GL I4 (ZMod 2)) *
              ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2)) := by
          calc (β : GL I4 (ZMod 2)) * (γ' : GL I4 (ZMod 2))
              = ((β : GL I4 (ZMod 2)) * (γ' : GL I4 (ZMod 2)) * (β : GL I4 (ZMod 2))⁻¹) *
                  (β : GL I4 (ZMod 2)) := by group
            _ = _ := by rw [h4]
        calc ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2)) *
              (γ' : GL I4 (ZMod 2))
            = ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ *
                ((β : GL I4 (ZMod 2)) * (γ' : GL I4 (ZMod 2))) := by group
          _ = _ := by rw [h7]; group
      rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← matAut_mul', ← matAut_mul', h6]
    have h1 : matAut (((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2))) = 1 :=
      eq_one_of_commute hD _ hcomm
    have h2 : ((tauSp α : StatedSp 2 (ZMod 2)) : GL I4 (ZMod 2))⁻¹ * (β : GL I4 (ZMod 2)) = 1 := by
      apply matHom_injective
      rw [map_one]
      exact h1
    exact Subtype.ext (inv_mul_eq_one.1 h2).symm
  subst hBτ
  exact pairImg_le_pairNorm (StatedSp 2 (ZMod 2)) tauSp ⟨α, rfl⟩

end Sp4Inf

end CFSG.Quasithin
