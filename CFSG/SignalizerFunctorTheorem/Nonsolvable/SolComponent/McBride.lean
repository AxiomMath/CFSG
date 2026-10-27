module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Criteria

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem oStar_le_normalizer [Finite G] {K : Subgroup G} (hK : IsSolComponent K) :
    oStar G ≤ Subgroup.normalizer (K : Set G) := by
  refine sup_le hK.solvableRadical_le_normalizer (sSup_le fun L hL => ?_)
  have hLc : IsSolComponent L := hL
  by_cases hLK : L = K
  · rw [hLK]
    exact Subgroup.le_normalizer
  · exact (hK.normalizes_of_ne hLc (Ne.symm hLK)).2.1

theorem normal_subgroupOf_oStar [Finite G] {K : Subgroup G} (hK : IsSolComponent K) :
    K ≤ oStar G ∧ (K.subgroupOf (oStar G)).Normal :=
  ⟨le_oStar hK, Subgroup.normal_subgroupOf_of_le_normalizer (oStar_le_normalizer hK)⟩

theorem IsSolComponent.subgroupOf [Finite G] {K H : Subgroup G} (hK : IsSolComponent K)
    (hKH : K ≤ H) : IsSolComponent (K.subgroupOf H) := by
  rw [isSolComponent_iff_minimal] at hK ⊢
  obtain ⟨⟨hKsub, hKns⟩, hKmin⟩ := hK
  refine And.intro (And.intro hKsub.subgroupOf fun hs => hKns ?_) fun S' hS' hle => ?_
  · exact isSolvable_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH)
  · obtain ⟨hS'sub, hS'ns⟩ := hS'
    have hSK : S'.map H.subtype ≤ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hle hy
    have hS'eq : (S'.map H.subtype).subgroupOf H = S' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective S'
    have hSsub : (S'.map H.subtype).IsSubnormal := by
      refine Subgroup.IsSubnormal.trans hSK ?_ hKsub
      have := hS'sub.comap (Subgroup.inclusion hKH)
      rwa [← hS'eq, Subgroup.comap_inclusion_subgroupOf hKH] at this
    have hSns : ¬ Group.IsSolvable (S'.map H.subtype) := fun hs => hS'ns
      (Group.isSolvable_of_isSolvable_injective (f := H.subtype.subgroupMap S')
        (MonoidHom.subgroupMap_injective _ _ H.subtype_injective))
    have hKS := hKmin ⟨hSsub, hSns⟩ hSK
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hKS (Subgroup.mem_subgroupOf.mp hx)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem map_symm_map (φ : G ≃* G) (S : Subgroup G) :
    (S.map φ.symm.toMonoidHom).map φ.toMonoidHom = S := by
  have := CFSG.LocalCores.map_map_symm φ.symm S
  rwa [MulEquiv.symm_symm] at this

theorem isSubnormal_not_isSolvable_map {S : Subgroup G} (φ : G ≃* G)
    (hS : S.IsSubnormal ∧ ¬ Group.IsSolvable S) :
    (S.map φ.toMonoidHom).IsSubnormal ∧ ¬ Group.IsSolvable (S.map φ.toMonoidHom) :=
  ⟨hS.1.map φ.surjective, fun _ => hS.2 (Group.isSolvable_of_isSolvable_injective
    (f := φ.toMonoidHom.subgroupMap S) (MonoidHom.subgroupMap_injective _ _ φ.injective))⟩

theorem isSolComponent_map_mulEquiv [Finite G] {K : Subgroup G} (φ : G ≃* G)
    (hK : IsSolComponent K) : IsSolComponent (K.map φ.toMonoidHom) := by
  rw [isSolComponent_iff_minimal] at hK ⊢
  obtain ⟨hKP, hmin⟩ := hK
  refine And.intro (isSubnormal_not_isSolvable_map φ hKP) fun S hS hSK => ?_
  have hS' := isSubnormal_not_isSolvable_map φ.symm hS
  have h1 : S.map φ.symm.toMonoidHom ≤ K := by
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hSK
    rwa [CFSG.LocalCores.map_map_symm φ K] at this
  have h2 := Subgroup.map_mono (f := φ.toMonoidHom) (hmin hS' h1)
  rwa [map_symm_map] at h2

theorem isSolComponent_map_iff [Finite G] (φ : G ≃* G) {K : Subgroup G} :
    IsSolComponent (K.map φ.toMonoidHom) ↔ IsSolComponent K :=
  ⟨fun h => by
    have := isSolComponent_map_mulEquiv φ.symm h
    rwa [CFSG.LocalCores.map_map_symm φ K] at this, isSolComponent_map_mulEquiv φ⟩

instance solLayer_characteristic [Finite G] : (solLayer G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change MulEquiv.mapSubgroup φ (sSup {K : Subgroup G | IsSolComponent K}) = solLayer G
  rw [OrderIso.map_sSup, ← sSup_image]
  refine congrArg sSup (Set.ext fun K => ⟨?_, fun hK => ?_⟩)
  · rintro ⟨K', hK', rfl⟩
    exact (isSolComponent_map_iff φ).mpr hK'
  · exact ⟨K.map φ.symm.toMonoidHom, (isSolComponent_map_iff φ.symm).mpr hK,
      map_symm_map φ K⟩

instance oStar_characteristic [Finite G] : (oStar G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  change (CFSG.solvableRadical G ⊔ solLayer G).map φ.toMonoidHom =
    CFSG.solvableRadical G ⊔ solLayer G
  rw [Subgroup.map_sup,
    Subgroup.characteristic_iff_map_eq.mp (solvableRadical_characteristic (G := G)) φ,
    Subgroup.characteristic_iff_map_eq.mp (solLayer_characteristic (G := G)) φ]

section McBride

variable [Finite G] {H : Subgroup G}

theorem map_solvableRadical_eq_of_oStar_le (hH : oStar G ≤ H) :
    (CFSG.solvableRadical H).map H.subtype = CFSG.solvableRadical G := by
  have hRH : CFSG.solvableRadical G ≤ H := solvableRadical_le_oStar.trans hH
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
  apply le_antisymm
  · have hXs : Group.IsSolvable ((CFSG.solvableRadical H).map H.subtype) := by
      have := isSolvable_solvableRadical (G := H)
      exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective)
    have hXn : ((CFSG.solvableRadical H).map H.subtype).subgroupOf H = CFSG.solvableRadical H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hHX : H ≤ Subgroup.normalizer (((CFSG.solvableRadical H).map H.subtype : Subgroup G) :
        Set G) := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp ?_
      rw [hXn]
      infer_instance
    have hA : (oStar G).Normal := inferInstance
    have hXA : ⁅(CFSG.solvableRadical H).map H.subtype, oStar G⁆ ≤
        CFSG.solvableRadical G := by
      have hle : ⁅(CFSG.solvableRadical H).map H.subtype, oStar G⁆ ≤
          (CFSG.solvableRadical H).map H.subtype ⊓ oStar G := by
        refine Subgroup.commutator_le.mpr fun x hx a ha => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 : a * x⁻¹ * a⁻¹ ∈ (CFSG.solvableRadical H).map H.subtype :=
            (Subgroup.mem_normalizer_iff.mp (hHX (hH ha)) x⁻¹).mp (inv_mem hx)
          have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
          rw [this]
          exact mul_mem hx h1
        · have h1 : x * a * x⁻¹ ∈ oStar G := hA.conj_mem a ha x
          have : ⁅x, a⁆ = (x * a * x⁻¹) * a⁻¹ := by rw [commutatorElement_def]
          rw [this]
          exact mul_mem h1 (inv_mem ha)
      refine hle.trans ?_
      have hn : (((CFSG.solvableRadical H).map H.subtype ⊓ oStar G).subgroupOf
          (oStar G)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff inf_le_right]
        intro z a hz ha
        refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem ha (Subgroup.mem_inf.mp hz).2)
          (inv_mem ha)⟩
        exact (Subgroup.mem_normalizer_iff.mp (hHX (hH ha)) z).mp (Subgroup.mem_inf.mp hz).1
      have hsub : ((CFSG.solvableRadical H).map H.subtype ⊓ oStar G).IsSubnormal :=
        Subgroup.IsSubnormal.trans inf_le_right (Subgroup.Normal.isSubnormal hn)
          (Subgroup.Normal.isSubnormal hA)
      exact le_solvableRadical_of_isSubnormal hsub
        (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left))
    have hlay : CFSG.layer (G ⧸ CFSG.solvableRadical G) ≤ Subgroup.centralizer
        (((CFSG.solvableRadical H).map H.subtype).map
          (QuotientGroup.mk' (CFSG.solvableRadical G)) : Set _) := by
      refine sSup_le fun C hC => ?_
      obtain ⟨K, hK, rfl⟩ := exists_isSolComponent_map_eq hC
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_map_eq_bot_iff K _).mpr ?_)
      refine le_trans (Subgroup.commutator_mono (le_oStar hK) le_rfl) ?_
      rw [Subgroup.commutator_comm]
      exact hXA
    have h2 := Subgroup.le_centralizer_iff.mp hlay
    rw [centralizer_layer_eq_bot solvableRadical_quotient] at h2
    rw [← QuotientGroup.ker_mk' (CFSG.solvableRadical G), ← Subgroup.map_eq_bot_iff]
    exact le_bot_iff.mp h2
  · have hsolv : Group.IsSolvable ((CFSG.solvableRadical G).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := H.subtype.subgroupComap (CFSG.solvableRadical G))
        (MonoidHom.subgroupComap_injective _ _ H.subtype_injective)
    have hle : (CFSG.solvableRadical G).subgroupOf H ≤ CFSG.solvableRadical H :=
      le_solvableRadical Subgroup.normal_subgroupOf hsolv
    calc CFSG.solvableRadical G
        = ((CFSG.solvableRadical G).subgroupOf H).map H.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hRH).symm
      _ ≤ (CFSG.solvableRadical H).map H.subtype := Subgroup.map_mono hle

theorem map_solLayer_le_oStar (hH : oStar G ≤ H) :
    (solLayer H).map H.subtype ≤ oStar G := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun L' hL' => ?_
  have hL'c : IsSolComponent L' := hL'
  rw [← Subgroup.map_le_iff_le_comap]
  by_cases hex : ∃ K : Subgroup G, IsSolComponent K ∧ L'.map H.subtype = K
  · obtain ⟨K, hK, hKL⟩ := hex
    rw [hKL]
    exact le_oStar hK
  · exfalso
    push Not at hex
    have hcomm : ∀ K : Subgroup G, IsSolComponent K →
        ⁅L'.map H.subtype, K⁆ ≤ CFSG.solvableRadical G := by
      intro K hK
      have hKH : K ≤ H := (le_oStar hK).trans hH
      have hne : L' ≠ K.subgroupOf H := by
        intro h
        exact hex K hK (by rw [h, Subgroup.map_subgroupOf_eq_of_le hKH])
      have h1 := IsSolComponent.commutator_le_solvableRadical_of_ne hL'c (hK.subgroupOf hKH) hne
      have h2 := Subgroup.map_mono (f := H.subtype) h1
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
        map_solvableRadical_eq_of_oStar_le hH] at h2
    have hlay : CFSG.layer (G ⧸ CFSG.solvableRadical G) ≤ Subgroup.centralizer
        ((L'.map H.subtype).map (QuotientGroup.mk' (CFSG.solvableRadical G)) : Set _) := by
      refine sSup_le fun C hC => ?_
      obtain ⟨K, hK, rfl⟩ := exists_isSolComponent_map_eq hC
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((commutator_map_eq_bot_iff K _).mpr ?_)
      rw [Subgroup.commutator_comm]
      exact hcomm K hK
    have h2 := Subgroup.le_centralizer_iff.mp hlay
    rw [centralizer_layer_eq_bot solvableRadical_quotient] at h2
    have hLR : L'.map H.subtype ≤ CFSG.solvableRadical G := by
      rw [← QuotientGroup.ker_mk' (CFSG.solvableRadical G), ← Subgroup.map_eq_bot_iff]
      exact le_bot_iff.mp h2
    have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
    have hLs : Group.IsSolvable ↥(L'.map H.subtype) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLR)
    exact hL'c.not_isSolvable (isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective L' H.subtype H.subtype_injective).symm)

theorem solLayer_le_map_solLayer (hH : oStar G ≤ H) :
    solLayer G ≤ (solLayer H).map H.subtype := by
  refine sSup_le fun K hK => ?_
  have hKc : IsSolComponent K := hK
  have hKH : K ≤ H := (le_oStar hKc).trans hH
  calc K = (K.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hKH).symm
    _ ≤ (solLayer H).map H.subtype := Subgroup.map_mono (le_solLayer (hKc.subgroupOf hKH))

theorem oStar_map_eq (hH : oStar G ≤ H) : (oStar H).map H.subtype = oStar G := by
  change (CFSG.solvableRadical H ⊔ solLayer H).map H.subtype =
    CFSG.solvableRadical G ⊔ solLayer G
  rw [Subgroup.map_sup, map_solvableRadical_eq_of_oStar_le hH]
  exact le_antisymm (sup_le le_sup_left (map_solLayer_le_oStar hH))
    (sup_le le_sup_left ((solLayer_le_map_solLayer hH).trans le_sup_right))

end McBride

end CFSG.SignalizerFunctorTheorem.Nonsolvable
