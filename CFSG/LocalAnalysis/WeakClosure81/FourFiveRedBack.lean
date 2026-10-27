module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveQuot

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

private theorem fourFive_isElemAbelian_of_map_injective {G : Type*} [Group G] {G' : Type*}
    [Group G'] {p : ℕ} {f : G →* G'} (hf : Function.Injective f) {A : Subgroup G}
    (h : IsElemAbelian p (A.map f)) : IsElemAbelian p A := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := E1.commute_of_isElemAbelian h (Subgroup.mem_map_of_mem f x.2)
      (Subgroup.mem_map_of_mem f y.2)
    exact hf (by simpa [map_mul] using this)
  · exact hf (by simpa [map_pow] using h.2 (f x) (Subgroup.mem_map_of_mem f hx))

theorem fourFive_isInvColl_preimage {Q : Type} [Group Q] {U : Subgroup Q}
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) :
    E1.IsInvColl (⊤ : Subgroup ↥U) {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω} := by
  refine ⟨fun _ _ => le_top, fun A' hA' => ?_, fun A' hA' x _ => ?_⟩
  · exact fourFive_isElemAbelian_of_map_injective U.subtype_injective
      (hΩ.isElemAbelian (A'.map U.subtype) hA')
  · show (CFSG.Quasithin.A1b.conjSub x A').map U.subtype ∈ Ω
    rw [E1.map_conjSub]
    exact hΩ.conj (A'.map U.subtype) hA' (U.subtype x) (Subgroup.mem_top _)

private theorem fourFive_sylow_of_le_aux {Q : Type} [Group Q] {T U : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (hTU : T ≤ U) :
    IsSylowIn 2 T U ∧ IsSylowIn 2 (T.subgroupOf U) (⊤ : Subgroup ↥U) := by
  have hTU' : IsSylowIn 2 T U :=
    ⟨hTU, hT.isPGroup, fun hdvd => hT.not_dvd_relIndex
      (hdvd.trans ⟨U.relIndex ⊤,
        (Subgroup.relIndex_mul_relIndex T U ⊤ hTU le_top).symm⟩)⟩
  refine ⟨hTU', ?_⟩
  have h := (E1.isSylowIn_subgroupOf_iff (H := U) hTU le_rfl).mpr hTU'
  rwa [Subgroup.subgroupOf_self] at h

theorem fourFive_eGen_map_subtype_le {Q : Type} [Group Q] [Finite Q] {T U : Subgroup Q}
    (hT : IsSylowIn 2 T ⊤) (hTU : T ≤ U) {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω)
    (n : ℕ) :
    (E1.eGen n ⊤ (T.subgroupOf U) {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω}).map U.subtype ≤
      E1.eGen n ⊤ T Ω := by
  have hmap := E1.eGen_map_subtype n U (T.subgroupOf U)
    {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω}
  have hTUmap : (T.subgroupOf U).map U.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTU
  rw [← hmap, hTUmap]
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  obtain ⟨A', hA', rfl⟩ := hA
  have hAΩ : A'.map U.subtype ∈ Ω := hA'
  have hK' : E1.IsE n U (T ⊓ U) (A'.map U.subtype) K := by
    rw [inf_eq_left.mpr hTU]
    exact hK
  have hτ : E1.tauOf ⊤ T (A'.map U.subtype) ≤ T ⊓ U :=
    le_inf (E1.tauOf_le _ _ _) ((E1.tauOf_le _ _ _).trans hTU)
  have hS : IsSylowIn 2 (T ⊓ U) U := by
    rw [inf_eq_left.mpr hTU]
    exact (fourFive_sylow_of_le_aux hT hTU).1
  have hKtop : E1.IsE n ⊤ T (A'.map U.subtype) K :=
    E1.eight_two hT hAT (hΩ.isElemAbelian (A'.map U.subtype) hAΩ) le_top hτ hS hK'
  exact le_iSup₂_of_le (A'.map U.subtype) hAΩ
    (le_iSup_of_le hAT (le_iSup₂_of_le K hKtop le_rfl))

theorem fourFive_weakClosure_map_subtype {Q : Type} [Group Q] {T U : Subgroup Q} (hTU : T ≤ U)
    (Ω : Set (Subgroup Q)) :
    (E1.weakClosure (T.subgroupOf U) {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω}).map U.subtype =
      E1.weakClosure T Ω := by
  have hmap := E1.weakClosure_map_image_of_injective U.subtype_injective (T.subgroupOf U)
    {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω}
  have hTUmap : (T.subgroupOf U).map U.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTU
  rw [← hmap, hTUmap]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    obtain ⟨A', hA', rfl⟩ := hA
    exact le_iSup₂_of_le (A'.map U.subtype) hA' (le_iSup_of_le hAT le_rfl)
  · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    have hAU : A ≤ U := hAT.trans hTU
    have hmapA : (A.subgroupOf U).map U.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAU
    have hA'sub : A.subgroupOf U ∈ {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω} := by
      simpa [hmapA] using hA
    exact le_iSup₂_of_le A ⟨A.subgroupOf U, hA'sub, hmapA⟩ (le_iSup_of_le hAT le_rfl)

theorem fourFive_dichotomy_of_quotient {Q : Type} [Group Q] [Finite Q] {n : ℕ}
    {T U C J : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hTU : T ≤ U) (hCT : C ≤ T)
    [(C.subgroupOf U).Normal] (hJU : J ≤ U)
    (hred : ∀ Ωq : Set (Subgroup (↥U ⧸ C.subgroupOf U)), E1.IsInvColl ⊤ Ωq →
      ((J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)) ≤
          E1.eGen n ⊤ ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) Ωq ⊔
            (T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)) ∨
        (J.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U)) ≤
          Subgroup.normalizer (E1.weakClosure
            ((T.subgroupOf U).map (QuotientGroup.mk' (C.subgroupOf U))) Ωq :
              Set (↥U ⧸ C.subgroupOf U))))
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) :
    J ≤ E1.eGen n ⊤ T Ω ⊔ T ∨ J ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set Q) := by
  set π : ↥U →* (↥U ⧸ C.subgroupOf U) := QuotientGroup.mk' (C.subgroupOf U) with hπ
  set Ω' : Set (Subgroup ↥U) := {A' : Subgroup ↥U | A'.map U.subtype ∈ Ω} with hΩ'def
  have hΩ' : E1.IsInvColl (⊤ : Subgroup ↥U) Ω' := fourFive_isInvColl_preimage hΩ
  have hΩbar : E1.IsInvColl (⊤ : Subgroup (↥U ⧸ C.subgroupOf U)) (Subgroup.map π '' Ω') :=
    E1.isInvColl_map_of_surjective π (QuotientGroup.mk'_surjective _) hΩ'
  have hTsub : IsSylowIn 2 (T.subgroupOf U) (⊤ : Subgroup ↥U) :=
    (fourFive_sylow_of_le_aux hT hTU).2
  have hCsubTsub : C.subgroupOf U ≤ T.subgroupOf U := fun x hx => hCT hx
  rcases hred (Subgroup.map π '' Ω') hΩbar with ha | hb
  · refine Or.inl ?_
    intro j hj
    set ju : ↥U := ⟨j, hJU hj⟩ with hju
    have hjumem : ju ∈ J.subgroupOf U := Subgroup.mem_subgroupOf.mpr hj
    have hπju : π ju ∈ E1.eGen n ⊤ ((T.subgroupOf U).map π) (Subgroup.map π '' Ω') ⊔
        (T.subgroupOf U).map π := ha (Subgroup.mem_map_of_mem π hjumem)
    have hle : E1.eGen n ⊤ ((T.subgroupOf U).map π) (Subgroup.map π '' Ω') ⊔
        (T.subgroupOf U).map π ≤
        (E1.eGen n ⊤ (T.subgroupOf U) Ω' ⊔ (T.subgroupOf U)).map π :=
      sup_le (fourFive_eGen_map_le (N := C.subgroupOf U) hTsub hΩ' n)
        (Subgroup.map_mono le_sup_right)
    obtain ⟨y, hy, hyeq⟩ := (Subgroup.mem_map).mp (hle hπju)
    have hker : y⁻¹ * ju ∈ C.subgroupOf U := (QuotientGroup.eq).mp hyeq
    have hCsuble : C.subgroupOf U ≤ E1.eGen n ⊤ (T.subgroupOf U) Ω' ⊔ (T.subgroupOf U) :=
      hCsubTsub.trans le_sup_right
    have hju : ju ∈ E1.eGen n ⊤ (T.subgroupOf U) Ω' ⊔ (T.subgroupOf U) := by
      have hmem := Subgroup.mul_mem _ hy (hCsuble hker)
      rwa [show y * (y⁻¹ * ju) = ju by group] at hmem
    have hjmap : (ju : Q) ∈
        (E1.eGen n ⊤ (T.subgroupOf U) Ω' ⊔ (T.subgroupOf U)).map U.subtype :=
      Subgroup.mem_map_of_mem _ hju
    have hle2 : (E1.eGen n ⊤ (T.subgroupOf U) Ω' ⊔ (T.subgroupOf U)).map U.subtype ≤
        E1.eGen n ⊤ T Ω ⊔ T := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hTU]
      exact sup_le_sup (fourFive_eGen_map_subtype_le hT hTU hΩ n) le_rfl
    exact hle2 hjmap
  · refine Or.inr ?_
    intro j hj
    set ju : ↥U := ⟨j, hJU hj⟩ with hju
    have hjumem : ju ∈ J.subgroupOf U := Subgroup.mem_subgroupOf.mpr hj
    have hπju : π ju ∈ Subgroup.normalizer
        ((E1.weakClosure (T.subgroupOf U) Ω').map π : Set (↥U ⧸ C.subgroupOf U)) := by
      have hthis := hb (Subgroup.mem_map_of_mem π hjumem)
      rw [show E1.weakClosure ((T.subgroupOf U).map π) (Subgroup.map π '' Ω') =
          (E1.weakClosure (T.subgroupOf U) Ω').map π from
          E1.weakClosure_map_quotient (N := C.subgroupOf U) hTsub hΩ'] at hthis
      exact hthis
    obtain ⟨g', hg', hg'eq⟩ :=
      E1.exists_mem_normalizer_of_mem_normalizer_map (N := C.subgroupOf U) hTsub hΩ' hπju
    have hker : g'⁻¹ * ju ∈ C.subgroupOf U := (QuotientGroup.eq).mp hg'eq
    have hWnorm : T.subgroupOf U ≤ Subgroup.normalizer
        (E1.weakClosure (T.subgroupOf U) Ω' : Set ↥U) := E1.le_normalizer_weakClosure hΩ'
    have hCsubnorm : C.subgroupOf U ≤ Subgroup.normalizer
        (E1.weakClosure (T.subgroupOf U) Ω' : Set ↥U) := hCsubTsub.trans hWnorm
    have hjunorm : ju ∈ Subgroup.normalizer
        (E1.weakClosure (T.subgroupOf U) Ω' : Set ↥U) := by
      have hmem := Subgroup.mul_mem _ hg' (hCsubnorm hker)
      rwa [show g' * (g'⁻¹ * ju) = ju by group] at hmem
    have hfinal : U.subtype ju ∈ Subgroup.normalizer
        ((E1.weakClosure (T.subgroupOf U) Ω').map U.subtype : Set Q) :=
      Subgroup.le_normalizer_map (f := U.subtype) (H := E1.weakClosure (T.subgroupOf U) Ω')
        (Subgroup.mem_map_of_mem _ hjunorm)
    rw [fourFive_weakClosure_map_subtype hTU Ω] at hfinal
    exact hfinal

end CFSG.LocalAnalysis.WeakClosure81
