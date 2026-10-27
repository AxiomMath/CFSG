module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (OInf)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G] {H T : Subgroup G} {P : ∀ (X : Type) [Group X], Prop}

omit [Finite G] in
theorem map_subtype_lt_iff {Y : Subgroup ↥H} : Y.map H.subtype < H ↔ Y < ⊤ := by
  have h := Subgroup.map_subtype_lt_map_subtype (G' := H) (H := Y) (K := ⊤)
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

omit [Finite G] in
theorem subgroupOf_lt_top_iff_of_le {X : Subgroup G} (hXH : X ≤ H) :
    X.subgroupOf H < ⊤ ↔ X < H := by
  have h := map_subtype_lt_iff (H := H) (Y := X.subgroupOf H)
  rw [Subgroup.map_subgroupOf_eq_of_le hXH] at h
  exact h.symm

omit [Finite G] in
theorem hasCompFactor_map_subtype_iff (X : Subgroup ↥H) :
    HasCompFactor (X.map H.subtype) P ↔ HasCompFactor X P := by
  have e : ↥(X.map H.subtype) ≃* ↥X :=
    (Subgroup.equivMapOfInjective X H.subtype H.subtype_injective).symm
  constructor
  · rintro ⟨L, hL, hcf, hPL⟩
    exact ⟨L, hL, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).1 hcf, hPL⟩
  · rintro ⟨L, hL, hcf, hPL⟩
    exact ⟨L, hL, (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr e).2 hcf, hPL⟩

omit [Finite G] in
theorem map_subtype_mem_calLT_iff (hTH : T ≤ H) {Y : Subgroup ↥H} :
    Y.map H.subtype ∈ calLT P H T ↔ Y ∈ calLT P ⊤ (T.subgroupOf H) := by
  have hT : T ≤ Y.map H.subtype ↔ T.subgroupOf H ≤ Y :=
    ⟨fun h x hx => (Subgroup.mem_map_iff_mem (x := x) H.subtype_injective).1
        (h (Subgroup.mem_subgroupOf.1 hx)),
      fun h t ht => ⟨⟨t, hTH ht⟩, h (Subgroup.mem_subgroupOf.2 ht), rfl⟩⟩
  exact and_congr hT (and_congr map_subtype_lt_iff (not_congr (hasCompFactor_map_subtype_iff Y)))

omit [Finite G] in
theorem lGen_eq_map_lGen_subgroupOf (hTH : T ≤ H) :
    lGen P H T = (lGen P ⊤ (T.subgroupOf H)).map H.subtype := by
  refine le_antisymm (iSup₂_le fun X hX => ?_) ?_
  · have hXH : X ≤ H := hX.2.1.le
    have hmem : X.subgroupOf H ∈ calLT P ⊤ (T.subgroupOf H) :=
      (map_subtype_mem_calLT_iff hTH (Y := X.subgroupOf H)).1
        (by rwa [Subgroup.map_subgroupOf_eq_of_le hXH])
    calc X = (X.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hXH).symm
      _ ≤ (lGen P ⊤ (T.subgroupOf H)).map H.subtype :=
        Subgroup.map_mono (le_iSup₂_of_le (X.subgroupOf H) hmem le_rfl)
  · refine Subgroup.map_le_iff_le_comap.2 (iSup₂_le fun Y hY => ?_)
    exact Subgroup.map_le_iff_le_comap.1
      (le_iSup₂_of_le (Y.map H.subtype) ((map_subtype_mem_calLT_iff hTH).2 hY) le_rfl)

omit [Finite G] in
theorem isSylowIn_subgroupOf_top (hT : IsSylowIn 2 T H) : IsSylowIn 2 (T.subgroupOf H) ⊤ := by
  refine ⟨le_top, hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hT.le).symm, ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact hT.not_dvd_relIndex

theorem calNIn_eq_lGen_of_top (hTH : T < H) (hne : H ≠ lGen P H T) {M : Subgroup ↥H}
    (hM : M < ⊤) (hMax : ∀ X : Subgroup ↥H, T.subgroupOf H ≤ X → X < ⊤ → X ≤ M)
    (hM0 : ¬ HasCompFactor M P) : calNIn H T = {lGen P H T} := by
  refine calNIn_eq_lGen_of_forall hTH hne fun M' hM' => ?_
  obtain ⟨hTM', hM'H, hmax⟩ := hM'
  have hsub : M'.subgroupOf H ≤ M :=
    hMax _ (fun x hx => Subgroup.mem_subgroupOf.2 (hTM' (Subgroup.mem_subgroupOf.1 hx)))
      ((subgroupOf_lt_top_iff_of_le hM'H.le).2 hM'H)
  have hle : M' ≤ M.map H.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hM'H.le).symm.le.trans (Subgroup.map_mono hsub)
  have hMH : M.map H.subtype < H := map_subtype_lt_iff.2 hM
  have heq : M' = M.map H.subtype := by
    by_contra hne'
    exact hMH.ne (hmax _ (lt_of_le_of_ne hle hne') hMH.le)
  rw [heq, hasCompFactor_map_subtype_iff]
  exact hM0

theorem calNIn_eq_lGen_of_isSolvable'
    (hP : ∀ (L : Type) [Group L] [Finite L], P L → ∃ a b : L, a * b ≠ b * a)
    (hTH : T < H) [Group.IsSolvable ↥H] (hne : H ≠ lGen P H T) :
    calNIn H T = {lGen P H T} := by
  refine calNIn_eq_lGen_of_forall hTH hne fun M hM => ?_
  have : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM.2.1.le)
  rintro ⟨L, hL, hcf, hPL⟩
  have : Finite L := isCompositionFactor_finite hcf
  obtain ⟨a, b, hab⟩ := hP L hPL
  exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
    inferInstance hcf a b)

omit [Finite G] in
theorem oInf_subgroupOf_self (H : Subgroup G) :
    (OInf H).subgroupOf H = CFSG.solvableRadical ↥H :=
  Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite G] in
theorem hasQuotShape_map_subtype_comap {Y : Type} [Group Y] {π : ↥H →* Y}
    (hπ : Function.Surjective π) {N : Set G} (hN : ∀ h : ↥H, π h = 1 ↔ (h : G) ∈ N)
    (F : Subgroup Y) (hP : P ↥F) : HasQuotShape ((F.comap π).map H.subtype) N P := by
  let ψ : ↥(F.comap π) →* ↥F := π.subgroupComap F
  have hψ : Function.Surjective ψ := MonoidHom.subgroupComap_surjective π F hπ
  let α : ↥(F.comap π) ≃* ↥((F.comap π).map H.subtype) :=
    Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective
  refine ⟨↥F, inferInstance, ψ.comp α.symm.toMonoidHom, hψ.comp α.symm.surjective, fun k => ?_,
    hP⟩
  obtain ⟨k', rfl⟩ := α.surjective k
  have hcoe : ((α k' : ↥((F.comap π).map H.subtype)) : G) = ((k' : ↥H) : G) :=
    Subgroup.coe_equivMapOfInjective_apply _ H.subtype H.subtype_injective k'
  change ψ (α.symm (α k')) = 1 ↔ _
  rw [MulEquiv.symm_apply_apply, hcoe, ← hN, Subtype.ext_iff]
  rfl

omit [Finite G] in
theorem isComponentModN_of_isComponent
    {E : Subgroup (↥H ⧸ CFSG.solvableRadical ↥H)} (hE : CFSG.IsComponent E) :
    IsComponentModN (OInf H) H
      ((E.comap (QuotientGroup.mk' (CFSG.solvableRadical ↥H))).map H.subtype) := by
  have hRE : CFSG.solvableRadical ↥H ≤ E.comap (QuotientGroup.mk' (CFSG.solvableRadical ↥H)) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact E.one_mem
  have hLH : (E.comap (QuotientGroup.mk' (CFSG.solvableRadical ↥H))).map H.subtype ≤ H :=
    Subgroup.map_subtype_le _
  refine ⟨?_, Subgroup.map_mono hRE, hLH, ?_, ?_⟩
  · rw [oInf_subgroupOf_self]
    infer_instance
  · rw [CFSG.Open.IsSubnormal.iff_subgroupOf hLH,
      Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact hE.2.comap _
  · refine hasQuotShape_map_subtype_comap (QuotientGroup.mk'_surjective _) (fun h => ?_) E hE.1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, SetLike.mem_coe]
    exact (Subgroup.mem_map_iff_mem (x := h) H.subtype_injective).symm

omit [Finite G] in
theorem map_subtype_sup_eq (hTH : T ≤ H) {L : Subgroup ↥H} (h : L ⊔ T.subgroupOf H = ⊤) :
    L.map H.subtype ⊔ T = H := by
  have h1 := congrArg (Subgroup.map H.subtype) h
  rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTH, Subgroup.map_top,
    Subgroup.range_subtype] at h1

end CFSG.LocalAnalysis.WeakClosure81

end
