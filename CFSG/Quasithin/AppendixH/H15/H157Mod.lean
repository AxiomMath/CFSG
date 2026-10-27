module

public import CFSG.Quasithin.AppendixH.H15.H157Inv
public import CFSG.Quasithin.AppendixH.H15.H157Frame

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24
  CFSG.ASVolI.ChH CFSG.Monster.Code


theorem mem_fixV_rImg_iff {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) (A : Subgroup S24) (x : V) :
    x ∈ fixV (rImg ρ A) ↔ e x ∈ fixV (img11 A) := by
  rw [mem_fixV, rImg, mem_fixV_img11_iff]
  constructor
  · intro h γ hγ
    have h1 : ρ γ x = x := h (ρ γ) (Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hγ))
    rw [← he γ x, h1]
  · intro h g hg
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
    have h2 : rhoM24 γ (e x) = e x := h γ (Subgroup.mem_subgroupOf.1 hγ)
    apply e.injective
    rw [he γ x, h2]

theorem twist_compat {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) (c : ↥M24g) (γ : ↥M24g) (v : V) :
    twistEquiv e rhoM24 c⁻¹ ((ρ.comp (MulAut.conj c).toMonoidHom) γ v) =
      rhoM24 γ (twistEquiv e rhoM24 c⁻¹ v) := by
  have hrho : ∀ (g : ↥M24g) (X : W11), e.symm (rhoM24 g X) = ρ g (e.symm X) := by
    intro g X
    have h := congrArg e.symm (he g (e.symm X))
    simpa using h.symm
  have hsymm : ∀ (g : ↥M24g) (w : V), e.symm (twistEquiv e rhoM24 g w) = ρ g w := by
    intro g w
    exact (hrho g (e w)).trans (by rw [e.symm_apply_apply])
  have hkey : ρ (c⁻¹) (ρ (c * γ * c⁻¹) v) = ρ γ (ρ (c⁻¹) v) := by
    rw [← MulAut.mul_apply V (ρ (c⁻¹)) (ρ (c * γ * c⁻¹)) v,
      ← map_mul ρ (c⁻¹) (c * γ * c⁻¹)]
    rw [show c⁻¹ * (c * γ * c⁻¹) = γ * c⁻¹ by group]
    rw [map_mul ρ γ (c⁻¹), MulAut.mul_apply V (ρ γ) (ρ (c⁻¹)) v]
  rw [rho_comp_conj_apply]
  apply e.symm.injective
  calc e.symm (twistEquiv e rhoM24 c⁻¹ (ρ (c * γ * c⁻¹) v))
      = ρ (c⁻¹) (ρ (c * γ * c⁻¹) v) := hsymm (c⁻¹) (ρ (c * γ * c⁻¹) v)
    _ = ρ γ (ρ (c⁻¹) v) := hkey
    _ = e.symm (rhoM24 γ (twistEquiv e rhoM24 c⁻¹ v)) :=
        ((hrho γ (twistEquiv e rhoM24 c⁻¹ v)).trans
          (congrArg (ρ γ) (hsymm (c⁻¹) v))).symm

theorem fixV_KY_eq_fixV_N {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {h y c : S24} (hh : h ∈ M24g)
    (hcy : c * y * c⁻¹ = tP) :
    fixV (rImg ρ (KY M24g (h • S0))) =
      fixV (rImg ρ (M24g ⊓ Subgroup.normalizer
        ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24))) := by
  let c₀ : ↥M24g := ⟨h, hh⟩
  let ρ' : ↥M24g →* MulAut V := ρ.comp (MulAut.conj c₀).toMonoidHom
  let eg : V ≃* W11 := twistEquiv e rhoM24 c₀⁻¹
  have hc₀ : (c₀ : S24) = h := rfl
  have htwist : ∀ (γ : ↥M24g) (v : V), eg (ρ' γ v) = rhoM24 γ (eg v) :=
    fun γ v => twist_compat ρ e he c₀ γ v
  have hK : rImg ρ (KY M24g (h • S0)) = rImg ρ' KSp := by
    rw [KY_smul_S0 hh, ← hc₀]
    exact (rImg_comp_conj ρ c₀ KSp).symm
  have hN : rImg ρ (M24g ⊓ Subgroup.normalizer
        ((conjSubg (h * c) (Subgroup.zpowers y) : Subgroup S24) : Set S24)) = rImg ρ' Nt := by
    rw [normN_conj_eq hh hcy, ← hc₀]
    exact (rImg_comp_conj ρ c₀ Nt).symm
  rw [hK, hN]
  have hfix : ∀ A : Subgroup S24, fixV (rImg ρ' A) = (fixV (img11 A)).comap eg.toMonoidHom := by
    intro A
    ext x
    exact (mem_fixV_rImg_iff ρ' eg htwist A x).trans
      (Subgroup.mem_comap (f := eg.toMonoidHom) (K := fixV (img11 A)) (x := x)).symm
  rw [hfix KSp, hfix Nt, fixV_img11_KSp_eq_Nt]

theorem mem_fixV_zpowers_iff_fixW {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V)
    (e : V ≃* W11) (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24}
    (hy : y ∈ M24g) (x : V) :
    x ∈ fixV (rImg ρ (Subgroup.zpowers y)) ↔ e x ∈ fixW ⟨y, hy⟩ := by
  rw [mem_fixV_rImg_iff ρ e he (Subgroup.zpowers y) x, mem_fixV_img11_iff, mem_fixW]
  constructor
  · intro h
    exact h ⟨y, hy⟩ (by simpa using Subgroup.mem_zpowers y)
  · intro h γ hγ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hγ
    have hγ' : γ = (⟨y, hy⟩ : ↥AutPerm) ^ k := by
      apply Subtype.ext
      simpa using hk.symm
    rw [hγ', map_zpow rhoM24 (⟨y, hy⟩ : ↥AutPerm) k]
    exact (mem_fixV (X := Subgroup.zpowers (rhoM24 ⟨y, hy⟩))).1
      (CFSG.Quasithin.mem_fixV_zpowers_iff.2 h) ((rhoM24 ⟨y, hy⟩) ^ k)
      (Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩)

theorem card_fixV_zpowers {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24} (hy : y ∈ M24g) :
    Nat.card ↥(fixV (rImg ρ (Subgroup.zpowers y))) = Nat.card ↥(fixW ⟨y, hy⟩) := by
  have hmap : (fixV (rImg ρ (Subgroup.zpowers y))).map e.toMonoidHom = fixW ⟨y, hy⟩ := by
    ext w
    constructor
    · intro hw
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
      exact (mem_fixV_zpowers_iff_fixW ρ e he hy z).1 hz
    · intro hw
      exact Subgroup.mem_map.2 ⟨e.symm w,
        (mem_fixV_zpowers_iff_fixW ρ e he hy (e.symm w)).2 (by rwa [e.apply_symm_apply]),
        e.apply_symm_apply w⟩
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (K := fixV (rImg ρ (Subgroup.zpowers y)))
    (f := e.toMonoidHom) e.injective).symm

theorem rk_fixV_zpowers {V : Type} [CommGroup V] (ρ : ↥M24g →* MulAut V) (e : V ≃* W11)
    (he : ∀ (γ : ↥M24g) (v : V), e (ρ γ v) = rhoM24 γ (e v)) {y : S24} (hy : y ∈ M24g) :
    rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) = rk ↥(fixW ⟨y, hy⟩) := by
  unfold rk
  rw [card_fixV_zpowers ρ e he hy]

end CFSG.ASVolI.AppH.H157
