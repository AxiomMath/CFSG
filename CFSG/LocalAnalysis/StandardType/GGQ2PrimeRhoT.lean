module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutModel

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT autEquiv autEquiv_apply)

structure RhoTSpec {G : Type} [Group G] {L : Subgroup G}
    (e : (L ⧸ center L) ≃* T46) (ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)) : Prop where
  conj : ∀ (y : normalizer (L : Set G)) (l : L) (hl : (y : G) * l * (y : G)⁻¹ ∈ L),
    ρ y * (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) * (ρ y)⁻¹ =
      e (QuotientGroup.mk (⟨_, hl⟩ : L))
  mem_autT : ∀ y, ρ y ∈ autT

private noncomputable def rhoTQuotEquiv {G : Type} [Group G] {L : Subgroup G}
    (y : normalizer (L : Set G)) : (L ⧸ center L) ≃* (L ⧸ center L) :=
  QuotientGroup.congr (center L) (center L) (L.normalizerMonoidHom y)
    (Subgroup.characteristic_iff_map_eq.mp Subgroup.centerCharacteristic
      (L.normalizerMonoidHom y))

private theorem rhoTQuotEquiv_mk {G : Type} [Group G] {L : Subgroup G}
    (y : normalizer (L : Set G)) (l : L) :
    rhoTQuotEquiv y (QuotientGroup.mk l) = QuotientGroup.mk (L.normalizerMonoidHom y l) :=
  QuotientGroup.congr_mk _ _ _ _ _

private noncomputable def rhoTQuotHom {G : Type} [Group G] {L : Subgroup G} :
    normalizer (L : Set G) →* MulAut (L ⧸ center L) where
  toFun y := rhoTQuotEquiv y
  map_one' := MulEquiv.ext fun q => by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [rhoTQuotEquiv_mk, map_one, MulAut.one_apply]
  map_mul' a b := MulEquiv.ext fun q => by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [rhoTQuotEquiv_mk, map_mul, MulAut.mul_apply]

private noncomputable def rhoTAut
    {G : Type} [Group G]
    {L : Subgroup G} (e : (L ⧸ center L) ≃* T46) :
    normalizer (L : Set G) →* Equiv.Perm (Fin 693) :=
  autT.subtype.comp
    (autEquiv.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp rhoTQuotHom))

private theorem rhoTAut_apply
    {G : Type} [Group G]
    {L : Subgroup G} (e : (L ⧸ center L) ≃* T46) (y : normalizer (L : Set G)) :
    rhoTAut e y = (autEquiv.symm (MulAut.congr e (rhoTQuotEquiv y)) : Equiv.Perm (Fin 693)) :=
  rfl

private theorem rhoTAut_conj
    {G : Type} [Group G]
    {L : Subgroup G} (e : (L ⧸ center L) ≃* T46) (y : normalizer (L : Set G)) (l : L)
    (hl : (y : G) * l * (y : G)⁻¹ ∈ L) :
    rhoTAut e y * (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) * (rhoTAut e y)⁻¹ =
      e (QuotientGroup.mk (⟨_, hl⟩ : L)) := by
  have h2 : rhoTQuotEquiv y (QuotientGroup.mk l) = QuotientGroup.mk (⟨_, hl⟩ : L) := by
    rw [rhoTQuotEquiv_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (L.normalizerMonoidHom_apply_apply_coe y l))
  have h3 : MulAut.congr e (rhoTQuotEquiv y) (e (QuotientGroup.mk l)) =
      e (QuotientGroup.mk (⟨_, hl⟩ : L)) := by
    change e (rhoTQuotEquiv y (e.symm (e (QuotientGroup.mk l)))) = _
    rw [MulEquiv.symm_apply_apply, h2]
  have h1 := autEquiv_apply (autEquiv.symm (MulAut.congr e (rhoTQuotEquiv y)))
    (e (QuotientGroup.mk l))
  rw [MulEquiv.apply_symm_apply, h3] at h1
  rw [rhoTAut_apply]
  exact h1.symm

theorem exists_rhoTSpec
    {G : Type} [Group G] {L : Subgroup G}
    (e : (L ⧸ center L) ≃* T46) : ∃ ρ, RhoTSpec e ρ :=
  ⟨rhoTAut e, fun y l hl => rhoTAut_conj e y l hl, fun y => by
    rw [rhoTAut_apply]
    exact (autEquiv.symm _).2⟩

end CFSG.GGQ2Prime
