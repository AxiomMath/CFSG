module

public import CFSG.Sporadic.Recognition.McLCentralizerMoore

public noncomputable section

namespace CFSG.Sporadic.Recognition.McLCentralizer

open Subgroup CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier (mclP mclPermEquiv)

theorem self_mem_centralizer {G : Type*} [Group G] (t : G) : t ∈ centralizer ({t} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

instance normal_zpowers_centralizer_self {G : Type*} [Group G] (t : G) :
    (zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set G))).Normal :=
  normal_of_le_center <| zpowers_le.2 <| Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

@[expose] def Cover8 (E : Type*) [Group E] (z : E) : Prop :=
  Group.IsPerfect E ∧ center E = zpowers z ∧ Nonempty (E ⧸ center E ≃* alternatingGroup (Fin 8))

theorem Cover8.of_mulEquiv {E F : Type*} [Group E] [Group F] {z : E} (h : Cover8 E z)
    (e : E ≃* F) : Cover8 F (e z) := by
  obtain ⟨hp, hc, ⟨q⟩⟩ := h
  have hcF : (center E).map e.toMonoidHom = center F := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ?_⟩
  · have : Group.IsPerfect E := hp
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · rw [← hcF, hc, MonoidHom.map_zpowers]
    rfl
  · exact ⟨(QuotientGroup.congr (center E) (center F) e hcF).symm.trans q⟩

theorem cover8_mclCt
    (hM : mooreCheck = true)
    (hL : liftCheck = true) : Cover8 mclCt (⟨mclT0, mclT0_mem_Ct⟩ : mclCt) := by
  obtain ⟨e⟩ := nonempty_range_mulEquiv_alt8 hM hL
  exact ⟨isPerfect_mclCt hL, center_mclCt.trans mclRho_ker_eq,
    ⟨(QuotientGroup.quotientMulEquivOfEq center_mclCt).trans
      ((QuotientGroup.quotientKerEquivRange mclRho).trans e)⟩⟩

@[expose] def centralizerEquivOfInjective {T M : Type*} [Group T] [Group M] (ι : T →* M)
    (hι : Function.Injective ι) (t : T) :
    centralizer ({t} : Set T) ≃* ↥(ι.range ⊓ centralizer ({ι t} : Set M)) :=
  ((centralizer ({t} : Set T)).equivMapOfInjective ι hι).trans
    (MulEquiv.subgroupCongr (by
      rw [map_centralizer_eq_inf hι, Set.image_singleton]))

theorem cover8_centralizer_of_embedding {T M : Type*} [Group T] [Group M] (ι : T →* M)
    (hι : Function.Injective ι) {P : Subgroup M} (hP : ι.range = P) {t : T} {τ : M}
    (hτ : ι t = τ) (hmem : τ ∈ P ⊓ centralizer ({τ} : Set M))
    (h : Cover8 ↥(P ⊓ centralizer ({τ} : Set M)) ⟨τ, hmem⟩) :
    Cover8 ↥(centralizer ({t} : Set T)) ⟨t, self_mem_centralizer t⟩ := by
  subst hτ hP
  have h' := h.of_mulEquiv (centralizerEquivOfInjective ι hι t).symm
  have e : (centralizerEquivOfInjective ι hι t).symm ⟨ι t, hmem⟩ = ⟨t, self_mem_centralizer t⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rwa [e] at h'

theorem cover8_centralizer_of_equiv_mclP
    (hM : mooreCheck = true) (hL : liftCheck = true) {T : Type*} [Group T]
    (e : T ≃* mclP) {t : T} (ht : orderOf t = 2) :
    Cover8 ↥(centralizer ({t} : Set T)) ⟨t, self_mem_centralizer t⟩ := by
  have hτP : ((e t : mclP) : Equiv.Perm (Fin 275)) ∈
      mclP := (e t).2
  have hτ : orderOf ((e t : mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  obtain ⟨g, hg, hgτ⟩ := mclT0_facts.2.2.2.2 _ hτP hτ
  let ι : T →* Equiv.Perm (Fin 275) :=
    (MulAut.conj g⁻¹).toMonoidHom.comp
      ((mclP).subtype.comp e.toMonoidHom)
  have hι : Function.Injective ι :=
    (MulAut.conj g⁻¹).injective.comp (Subtype.val_injective.comp e.injective)
  have hrange : ι.range = mclP := by
    have h1 : ((mclP).subtype.comp e.toMonoidHom).range =
        mclP := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
        ← MonoidHom.range_eq_map, range_subtype]
    rw [show ι.range = ((mclP).subtype.comp e.toMonoidHom).range.map
      (MulAut.conj g⁻¹).toMonoidHom from MonoidHom.range_comp _ _, h1]
    exact map_conj_self ((mclP).inv_mem hg)
  have hιt : ι t = mclT0 := by
    have : ι t = g⁻¹ * ((e t : mclP) : Equiv.Perm (Fin 275)) * g⁻¹⁻¹ := rfl
    rw [this, hgτ]
    group
  exact cover8_centralizer_of_embedding ι hι hrange hιt mclT0_mem_Ct (cover8_mclCt hM hL)

theorem centralizer_alt8_of_cover8 {G : Type*} [Group G] {t : G}
    (h : Cover8 ↥(centralizer ({t} : Set G)) ⟨t, self_mem_centralizer t⟩) :
    Group.IsPerfect (centralizer ({t} : Set G)) ∧
    center (centralizer ({t} : Set G)) =
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set G)) ∧
    Nonempty (centralizer ({t} : Set G) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set G)) ≃*
        alternatingGroup (Fin 8)) := by
  obtain ⟨hp, hc, ⟨q⟩⟩ := h
  exact ⟨hp, hc, ⟨(QuotientGroup.quotientMulEquivOfEq hc.symm).trans q⟩⟩

theorem mcl_involution_centralizer_alt8
    (hM : mooreCheck = true)
    (hL : liftCheck = true) {T : Type*} [Group T]
    (hT : Nonempty (T ≃* CFSG.Blueprint.NativeSporadic.McL)) {t : T} (ht : orderOf t = 2) :
    Group.IsPerfect (centralizer ({t} : Set T)) ∧
    center (centralizer ({t} : Set T)) =
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ∧
    Nonempty (centralizer ({t} : Set T) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ≃*
        alternatingGroup (Fin 8)) := by
  obtain ⟨e⟩ := hT
  exact centralizer_alt8_of_cover8
    (cover8_centralizer_of_equiv_mclP hM hL (e.trans mclPermEquiv) ht)

theorem mcl_involution_centralizer_alt8_of_isSporadic
    (hM : mooreCheck = true)
    (hL : liftCheck = true) {T : Type} [Group T]
    (hT : CFSG.Blueprint.NativeSporadic.IsSporadic T .McL) {t : T} (ht : orderOf t = 2) :
    Group.IsPerfect (centralizer ({t} : Set T)) ∧
    center (centralizer ({t} : Set T)) =
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ∧
    Nonempty (centralizer ({t} : Set T) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ : centralizer ({t} : Set T)) ≃*
        alternatingGroup (Fin 8)) :=
  mcl_involution_centralizer_alt8 hM hL hT ht

theorem mcl_involution_centralizer_alt8_pinned
    (hM : mooreCheck = true)
    (hL : liftCheck = true) {t : CFSG.Blueprint.NativeSporadic.McL} (ht : orderOf t = 2) :
    Group.IsPerfect (centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.McL)) ∧
    center (centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.McL)) =
      zpowers (⟨t, self_mem_centralizer t⟩ :
        centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.McL)) ∧
    Nonempty (centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.McL) ⧸
      zpowers (⟨t, self_mem_centralizer t⟩ :
        centralizer ({t} : Set CFSG.Blueprint.NativeSporadic.McL)) ≃* alternatingGroup (Fin 8)) :=
  @centralizer_alt8_of_cover8 CFSG.Blueprint.NativeSporadic.McL inferInstance t
    (@cover8_centralizer_of_equiv_mclP hM hL CFSG.Blueprint.NativeSporadic.McL inferInstance
      mclPermEquiv t ht)

end CFSG.Sporadic.Recognition.McLCentralizer
