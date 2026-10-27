module

public import CFSG.Quasithin.H13.NQBlockCcomponentQuotient
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup

theorem isCComponent_of_isComponent {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.IsComponent K) : CFSG.IsCComponent K :=
  mem_cComp_top_iff_isCComponent.mp (mem_cComp_top_of_isComponent hK)

theorem commutator_eq_bot_of_component_le_normalizer {G : Type*} [Group G] [Finite G]
    {J Y : Subgroup G} (hJ : CFSG.IsComponent J) (hYs : Group.IsSolvable Y)
    (hJY : J ≤ normalizer (Y : Set G)) : ⁅J, Y⁆ = ⊥ := by
  have hYN : Y ≤ J ⊔ Y := le_sup_right
  have hJN : J ≤ J ⊔ Y := le_sup_left
  have hnorm : (Y.subgroupOf (J ⊔ Y)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hYN).mpr (sup_le hJY le_normalizer)
  have hRs : Group.IsSolvable (Y.subgroupOf (J ⊔ Y)) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hYN).toMonoidHom)
      (subgroupOfEquivOfLe hYN).injective
  have h := (CFSG.LocalCores.component_solvable_centralizer hRs hnorm.isSubnormal).1
    (J.subgroupOf (J ⊔ Y)) (CFSG.LocalCores.component_overgroup hJ hJN)
  have h2 := congrArg (Subgroup.map (J ⊔ Y).subtype) h
  rwa [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_eq_left.mpr hJN,
    inf_eq_left.mpr hYN, Subgroup.map_bot] at h2

theorem le_generalizedFitting_inf_centralizer {E : Type*} [Group E] [Finite E] {Y : Subgroup E}
    (hYs : Group.IsSolvable Y) (hcomm : ⁅Y, CFSG.fittingSubgroup E⁆ = ⊥)
    (hall : ∀ J : Subgroup E, CFSG.IsComponent J → J ≤ normalizer (Y : Set E)) :
    Y ≤ CFSG.generalizedFitting E ⊓ centralizer (CFSG.generalizedFitting E : Set E) := by
  have hc : CFSG.generalizedFitting E ≤ centralizer (Y : Set E) := by
    refine sup_le ?_ (sSup_le fun J hJ => ?_)
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm)
    · exact commutator_eq_bot_iff_le_centralizer.mp
        (commutator_eq_bot_of_component_le_normalizer hJ hYs (hall J hJ))
  have hY : Y ≤ centralizer (CFSG.generalizedFitting E : Set E) := le_centralizer_iff.mp hc
  exact le_inf (hY.trans (CFSG.centralizer_generalizedFitting_le E)) hY

theorem pRank_le_one_of_le_abelian_normal {E : Type*} [Group E] [Finite E] {p : ℕ}
    [hp : Fact p.Prime] {Y Z : Subgroup E} (hYZ : Y ≤ Z) (hZn : Z.Normal)
    (hZc : IsMulCommutative Z) (hcyc : IsCyclic (CFSG.pCore p E)) :
    CFSG.pRank p Y ≤ 1 := by
  refine csSup_le' ?_
  rintro r ⟨A, hA, hcard⟩
  have hAp : IsPGroup p (A.map Y.subtype) := (IsElementaryAbelian.isPGroup p A).map _
  have hnil : Group.IsNilpotent Z := CommGroup.isNilpotent
  have hle : A.map Y.subtype ≤ CFSG.pCore p E := by
    have h := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore (A.map Y.subtype) Z p
      hp.out hAp hZn hnil
    rwa [inf_eq_left.mpr ((map_subtype_le A).trans hYZ)] at h
  have e : A ≃* (A.map Y.subtype).subgroupOf (CFSG.pCore p E) :=
    (A.equivMapOfInjective Y.subtype Y.subtype_injective).trans (subgroupOfEquivOfLe hle).symm
  have hAc : IsCyclic A := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hdvd : Nat.card A ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p A
  have h1 : p ^ r ∣ p ^ 1 := by rw [pow_one, ← hcard]; exact hdvd
  exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp h1

theorem nonempty_quotient_mulEquiv {H Q : Type*} [Group H] [Group Q] (f : H →* Q)
    {K : Subgroup H} {J : Subgroup Q} (hKJ : K.map f = J) (D : Subgroup K) [D.Normal]
    (hD : D.map K.subtype = K ⊓ f.ker) : Nonempty (K ⧸ D ≃* J) := by
  have hmem : ∀ k : K, (f.comp K.subtype) k ∈ J := fun k => hKJ ▸ mem_map_of_mem f k.2
  set φ : K →* J := (f.comp K.subtype).codRestrict J hmem with hφ
  have hφs : Function.Surjective φ := by
    rintro ⟨j, hj⟩
    rw [← hKJ] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact ⟨⟨k, hk⟩, rfl⟩
  have hker : D = φ.ker := by
    rw [hφ, MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
    apply map_injective K.subtype_injective
    change _ = (f.ker.subgroupOf K).map K.subtype
    rw [subgroupOf_map_subtype, inf_comm, hD]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφs)⟩

theorem cyclic_prime_core_Fitting_centralization_produces_escaping_Ccomponent
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] {X : Subgroup H}
    (hXs : Group.IsSolvable X)
    (hrank : 2 ≤ CFSG.pRank p (X.map (QuotientGroup.mk' (CFSG.pCore 2 H))))
    (hcyc : IsCyclic (CFSG.pCore p (H ⧸ CFSG.pCore 2 H)))
    (hcomm : ⁅X.map (QuotientGroup.mk' (CFSG.pCore 2 H)),
      CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)⁆ = ⊥) :
    ∃ K : Subgroup H, CFSG.IsCComponent K ∧ CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K) ∧
      ¬ K ≤ normalizer (X : Set H) ∧
      CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 H))) ∧
      ¬ K.map (QuotientGroup.mk' (CFSG.pCore 2 H)) ≤
        normalizer ((X.map (QuotientGroup.mk' (CFSG.pCore 2 H)) : Subgroup (H ⧸ CFSG.pCore 2 H)) :
          Set (H ⧸ CFSG.pCore 2 H)) ∧
      K ⊓ CFSG.pCore 2 H = (CFSG.pCore 2 K).map K.subtype := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYs : Group.IsSolvable (X.map (QuotientGroup.mk' (CFSG.pCore 2 H))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (CFSG.pCore 2 H)).subgroupMap_surjective X)
  obtain ⟨J, hJ, hJY⟩ : ∃ J : Subgroup (H ⧸ CFSG.pCore 2 H), CFSG.IsComponent J ∧
      ¬ J ≤ normalizer ((X.map (QuotientGroup.mk' (CFSG.pCore 2 H)) :
        Subgroup (H ⧸ CFSG.pCore 2 H)) : Set (H ⧸ CFSG.pCore 2 H)) := by
    by_contra hall
    push Not at hall
    have hYZ := le_generalizedFitting_inf_centralizer hYs hcomm hall
    have hZn : (CFSG.generalizedFitting (H ⧸ CFSG.pCore 2 H) ⊓
        centralizer (CFSG.generalizedFitting (H ⧸ CFSG.pCore 2 H) :
          Set (H ⧸ CFSG.pCore 2 H))).Normal := by
      have := (CFSG.LocalCores.generalized_fitting_characteristic
        (G := H ⧸ CFSG.pCore 2 H)).2
      infer_instance
    have hZc : IsMulCommutative ↥(CFSG.generalizedFitting (H ⧸ CFSG.pCore 2 H) ⊓
        centralizer (CFSG.generalizedFitting (H ⧸ CFSG.pCore 2 H) :
          Set (H ⧸ CFSG.pCore 2 H))) :=
      ⟨⟨fun a b => Subtype.ext (mem_centralizer_iff.mp a.2.2 b b.2.1).symm⟩⟩
    have := pRank_le_one_of_le_abelian_normal hYZ hZn hZc hcyc
    omega
  have hC : Group.IsSolvable (CFSG.pCore 2 H) := by
    have := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 H)).isNilpotent
    infer_instance
  obtain ⟨K, hKc, hKJ⟩ : ∃ K : Subgroup H, CFSG.IsCComponent K ∧
      K.map (QuotientGroup.mk' (CFSG.pCore 2 H)) = J :=
    ⟨_, (Ccomponent_solvable_quotient_bijection (CFSG.pCore 2 H) hC).2 J
      (isCComponent_of_isComponent hJ)⟩
  have hKcap : K ⊓ CFSG.pCore 2 H = (CFSG.pCore 2 K).map K.subtype := by
    have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
      {q : Nat.Primes | q.val = 2} hKc.2.2.1
    rw [← CFSG.pCore_eq_piCore K 2, ← CFSG.pCore_eq_piCore H 2] at h
    exact h.symm
  obtain ⟨e⟩ := nonempty_quotient_mulEquiv (QuotientGroup.mk' (CFSG.pCore 2 H)) hKJ
    (CFSG.pCore 2 K) (by rw [QuotientGroup.ker_mk', hKcap])
  refine ⟨K, hKc, CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hJ.1, fun hKX => hJY ?_,
    hKJ ▸ hJ, hKJ ▸ hJY, hKcap⟩
  rw [← hKJ]
  exact (map_mono hKX).trans (le_normalizer_map _)

end CFSG.Quasithin.H13.NQBlock
