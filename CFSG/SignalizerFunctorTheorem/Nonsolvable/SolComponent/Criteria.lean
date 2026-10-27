module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Dichotomy

public section

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

theorem center_eq_bot_of_solvableRadical_eq_bot {X : Type*} [Group X] [Finite X]
    (hX : CFSG.solvableRadical X = ⊥) {C : Subgroup X} (hC : C.IsSubnormal) :
    Subgroup.center C = ⊥ := by
  have hsub : ((Subgroup.center C).map C.subtype).IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hC
  have hsolv : Group.IsSolvable ((Subgroup.center C).map C.subtype) :=
    isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective (Subgroup.center C) C.subtype
      C.subtype_injective)
  have hle := le_solvableRadical_of_isSubnormal hsub hsolv
  rw [hX] at hle
  rw [eq_bot_iff]
  intro z hz
  have h1 := hle (Subgroup.mem_map_of_mem C.subtype hz)
  rw [Subgroup.mem_bot] at h1 ⊢
  exact Subtype.ext h1

theorem ker_subgroupMap_eq_solvableRadical [Finite G] {K : Subgroup G} (hK : K.IsSubnormal) :
    ((QuotientGroup.mk' (CFSG.solvableRadical G)).subgroupMap K).ker =
      CFSG.solvableRadical K := by
  ext x
  have h1 : x ∈ CFSG.solvableRadical K ↔ (x : G) ∈ (CFSG.solvableRadical K).map K.subtype :=
    (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  rw [h1, map_subtype_solvableRadical_eq_inf hK, Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    exact (QuotientGroup.eq_one_iff (x : G)).mp (congrArg Subtype.val h)
  · rintro ⟨-, h⟩
    exact Subtype.ext ((QuotientGroup.eq_one_iff (x : G)).mpr h)

theorem nonempty_quotient_solvableRadical_mulEquiv [Finite G] {K : Subgroup G}
    (hK : K.IsSubnormal) :
    Nonempty (↥K ⧸ CFSG.solvableRadical K ≃*
      ↥(K.map (QuotientGroup.mk' (CFSG.solvableRadical G)))) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (ker_subgroupMap_eq_solvableRadical hK).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk' (CFSG.solvableRadical G)).subgroupMap_surjective K))⟩

namespace IsSolComponent

variable [Finite G] {K : Subgroup G}

theorem isSimpleGroup_map (hK : IsSolComponent K) :
    IsSimpleGroup (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) := by
  have hZ := center_eq_bot_of_solvableRadical_eq_bot solvableRadical_quotient
    hK.isComponent_map.2
  have := hK.isComponent_map.1.2.1
  exact (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    ).isSimpleGroup

end IsSolComponent

theorem isSolComponent_of_isSimpleGroup_map [Finite G] {K : Subgroup G} (hp : Group.IsPerfect K)
    (hs : K.IsSubnormal)
    (hsimple : IsSimpleGroup (K.map (QuotientGroup.mk' (CFSG.solvableRadical G)))) :
    IsSolComponent K := by
  have := hp
  have := hsimple
  have hKb : Group.IsPerfect (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
    Group.IsPerfect.map _
  have hnc : ∃ a b : K.map (QuotientGroup.mk' (CFSG.solvableRadical G)), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : IsMulCommutative (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
      ⟨⟨hcon⟩⟩
    exact Group.IsPerfect.not_isMulCommutative
      (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) inferInstance
  exact ⟨hp, hs, (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1,
    hs.map (QuotientGroup.mk'_surjective _)⟩

theorem isSolComponent_iff_isSimpleGroup_map [Finite G] {K : Subgroup G} :
    IsSolComponent K ↔ Group.IsPerfect K ∧ K.IsSubnormal ∧
      IsSimpleGroup (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
  ⟨fun h => ⟨h.isPerfect, h.isSubnormal, h.isSimpleGroup_map⟩,
    fun ⟨hp, hs, hsimple⟩ => isSolComponent_of_isSimpleGroup_map hp hs hsimple⟩

theorem isSolComponent_iff_isSimpleGroup_quotient [Finite G] {K : Subgroup G} :
    IsSolComponent K ↔ K.IsSubnormal ∧ Group.IsPerfect K ∧
      IsSimpleGroup (↥K ⧸ CFSG.solvableRadical K) := by
  constructor
  · intro h
    obtain ⟨e⟩ := nonempty_quotient_solvableRadical_mulEquiv h.isSubnormal
    have := h.isSimpleGroup_map
    exact ⟨h.isSubnormal, h.isPerfect, e.isSimpleGroup⟩
  · rintro ⟨hs, hp, hsimple⟩
    obtain ⟨e⟩ := nonempty_quotient_solvableRadical_mulEquiv hs
    have := hsimple
    exact isSolComponent_of_isSimpleGroup_map hp hs e.symm.isSimpleGroup

theorem isSolComponent_iff_minimal [Finite G] {K : Subgroup G} :
    IsSolComponent K ↔
      Minimal (fun S : Subgroup G => S.IsSubnormal ∧ ¬ Group.IsSolvable S) K := by
  constructor
  · intro hK
    refine And.intro (And.intro hK.isSubnormal hK.not_isSolvable) fun S hS hSK => ?_
    rcases hK.le_or_commutator_le_solvableRadical hS.1 with h | h
    · exact h
    · exfalso
      have hSR : S ≤ CFSG.solvableRadical G := fun x hx =>
        hK.inf_le_solvableRadical_of_commutator_le hS.1 h ⟨hSK hx, hx⟩
      have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
      exact hS.2 (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hSR))
  · rintro ⟨⟨hKsub, hKns⟩, hmin⟩
    have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
    have hperf : Group.IsPerfect K := by
      have hPsub := isSubnormal_perfectResidual_map hKsub
      have hPperf := isPerfect_perfectResidual_map K
      have hPns : ¬ Group.IsSolvable ((CFSG.perfectResidual K).map K.subtype) := by
        have hne : CFSG.perfectResidual K ≠ ⊥ := fun hbot => hKns
          (CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mp
            hbot)
        have hne' : (CFSG.perfectResidual K).map K.subtype ≠ ⊥ := fun hbot => hne
          ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hbot)
        have : Nontrivial ((CFSG.perfectResidual K).map K.subtype) :=
          (Subgroup.nontrivial_iff_ne_bot _).mpr hne'
        exact Group.IsPerfect.not_isSolvable _
      have hKP : K ≤ (CFSG.perfectResidual K).map K.subtype :=
        hmin ⟨hPsub, hPns⟩ (Subgroup.map_subtype_le _)
      have heq : (CFSG.perfectResidual K).map K.subtype = K :=
        le_antisymm (Subgroup.map_subtype_le _) hKP
      exact heq ▸ hPperf
    have hsimple : IsSimpleGroup (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) := by
      rw [Subgroup.isSimpleGroup_iff]
      refine ⟨?_, fun T hTK hTn => ?_⟩
      · intro hbot
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
        exact hKns (Group.isSolvable_of_isSolvable_injective
          (Subgroup.inclusion_injective hbot))
      · have hNK : K ⊓ T.comap (QuotientGroup.mk' (CFSG.solvableRadical G)) ≤ K := inf_le_left
        have hNn : ((K ⊓ T.comap (QuotientGroup.mk' (CFSG.solvableRadical G))).subgroupOf
            K).Normal := by
          rw [Subgroup.normal_subgroupOf_iff hNK]
          intro n k hn hk
          obtain ⟨hnK, hnT⟩ := Subgroup.mem_inf.mp hn
          refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hk hnK) (inv_mem hk), ?_⟩
          have h1 := (Subgroup.normal_subgroupOf_iff hTK).mp hTn
            (QuotientGroup.mk' (CFSG.solvableRadical G) n)
            (QuotientGroup.mk' (CFSG.solvableRadical G) k) hnT (Subgroup.mem_map_of_mem _ hk)
          simpa using h1
        have hNsub : (K ⊓ T.comap (QuotientGroup.mk' (CFSG.solvableRadical G))).IsSubnormal :=
          Subgroup.IsSubnormal.trans hNK (Subgroup.Normal.isSubnormal hNn) hKsub
        by_cases hNs : Group.IsSolvable ↥(K ⊓ T.comap (QuotientGroup.mk' (CFSG.solvableRadical G)))
        · left
          have hNR := le_solvableRadical_of_isSubnormal hNsub hNs
          rw [eq_bot_iff]
          intro t ht
          obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp (hTK ht)
          have hkN : k ∈ K ⊓ T.comap (QuotientGroup.mk' (CFSG.solvableRadical G)) :=
            Subgroup.mem_inf.mpr ⟨hk, ht⟩
          have := hNR hkN
          rw [Subgroup.mem_bot]
          exact (QuotientGroup.eq_one_iff k).mpr this
        · right
          have hKN := hmin ⟨hNsub, hNs⟩ hNK
          refine le_antisymm hTK ?_
          rintro _ ⟨k, hk, rfl⟩
          exact (Subgroup.mem_inf.mp (hKN hk)).2
    exact isSolComponent_of_isSimpleGroup_map hperf hKsub hsimple

end CFSG.SignalizerFunctorTheorem.Nonsolvable
