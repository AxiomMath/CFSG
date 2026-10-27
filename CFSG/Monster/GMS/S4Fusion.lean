module

public import CFSG.Monster.GMS.S4FusionLeech
public import CFSG.Monster.GMS.Facts.Interfaces
import CFSG.Monster.GMS.Griess13.ChecksUniqueness

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

theorem mulEquiv_centralizer_apply_self
    {G G' : Type} [Group G] [Group G'] [Finite G'] {d₀ : B}
    (I' : GMSInterfaces d₀ G') {a' z₀' : G'} (hG' : GMSF1Type d₀ a' z₀') {t : G} {t' : G'}
    (ht2 : orderOf t = 2) (ht' : IsConj a' t')
    (φ : ↥(Subgroup.centralizer ({t} : Set G)) ≃* ↥(Subgroup.centralizer ({t'} : Set G'))) :
    ((φ ⟨t, mem_centralizer_self t⟩ : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') =
      t' := by
  obtain ⟨b', z', u', hT'⟩ := exists_twoClasses_of_isConj I'.sls I'.tableV I'.leech hG' ht'
  refine S4Fusion.eq_of_forall_comm hT' (φ _).2 ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht2]
  · intro y hy
    obtain ⟨y₀, hy₀⟩ := φ.surjective ⟨y, hy⟩
    have hcomm : y₀ * ⟨t, mem_centralizer_self t⟩ =
        ⟨t, mem_centralizer_self t⟩ * y₀ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y₀.2)
    have h1 := congrArg (fun x : ↥(Subgroup.centralizer ({t} : Set G)) =>
      ((φ x : ↥(Subgroup.centralizer ({t'} : Set G'))) : G')) hcomm
    simp only [map_mul, Subgroup.coe_mul, hy₀] at h1
    exact h1

theorem isConj_iff_of_mulEquiv_twoA
    {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']
    {d₀ d₀' : B} (I : GMSInterfaces d₀ G) (I' : GMSInterfaces d₀' G') (hNF : Co2StabFacts)
    {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {a' z₀' : G'} (hG' : GMSF1Type d₀' a' z₀')
    {t : G} {t' : G'} (ht : IsConj a t) (ht' : IsConj a' t')
    (φ : ↥(Subgroup.centralizer ({t} : Set G)) ≃* ↥(Subgroup.centralizer ({t'} : Set G')))
    (s : ↥(Subgroup.centralizer ({t} : Set G))) :
    IsConj a (s : G) ↔ IsConj a' ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') := by
  obtain ⟨b, z, u, hT⟩ := exists_twoClasses_of_isConj I.sls I.tableV I.leech hG ht
  obtain ⟨b', z', u', hT'⟩ := exists_twoClasses_of_isConj I'.sls I'.tableV I'.leech hG' ht'
  have hA : ∀ x : G, IsConj a x ↔ IsConj t x := fun x => ⟨fun h => ht.symm.trans h,
    fun h => ht.trans h⟩
  have hA' : ∀ x : G', IsConj a' x ↔ IsConj t' x := fun x => ⟨fun h => ht'.symm.trans h,
    fun h => ht'.trans h⟩
  rw [hA, hA']
  have hφt := mulEquiv_centralizer_apply_self I' hG' hT.orderOf_a ht' φ
  have hord : ∀ x : ↥(Subgroup.centralizer ({t} : Set G)),
      orderOf ((φ x : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') = orderOf (x : G) := by
    intro x
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
  by_cases hs2 : orderOf (s : G) = 2
  swap
  · refine iff_of_false (fun h => hs2 ?_) (fun h => hs2 ?_)
    · exact (orderOf_eq_of_isConj h).symm.trans hT.orderOf_a
    · rw [← hord s]
      exact (orderOf_eq_of_isConj h).symm.trans hT'.orderOf_a
  have hs2' : orderOf ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') = 2 := by
    rw [hord s]
    exact hs2
  by_cases hst : (s : G) = t
  ·
    have hsφ : ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') = t' := by
      have : s = ⟨t, mem_centralizer_self t⟩ := Subtype.ext hst
      rw [this]
      exact hφt
    rw [hst, hsφ]
    exact iff_of_true (IsConj.refl t) (IsConj.refl t')
  have hst' : ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') ≠ t' := by
    intro e
    apply hst
    have : φ s = φ ⟨t, mem_centralizer_self t⟩ := Subtype.ext (e.trans hφt.symm)
    exact congrArg Subtype.val (φ.injective this)
  have hcard : Nat.card ↥(Subgroup.centralizer ({t'} : Set G') ⊓
      Subgroup.centralizer ({((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G')} :
        Set G')) =
      Nat.card ↥(Subgroup.centralizer ({t} : Set G) ⊓
        Subgroup.centralizer ({(s : G)} : Set G)) := by
    rw [← S4Fusion.card_centralizer_subtype (φ s), ← S4Fusion.card_centralizer_subtype s]
    exact (Nat.card_congr (centralizerMulEquiv φ s).toEquiv).symm
  have hPiff : S4Fusion.HasNormalTwoCommutator t (s : G) ↔
      S4Fusion.HasNormalTwoCommutator t'
        ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') := by
    refine ⟨fun h => S4Fusion.HasNormalTwoCommutator.map φ h, fun h => ?_⟩
    have := S4Fusion.HasNormalTwoCommutator.map φ.symm h
    rwa [φ.symm_apply_apply] at this
  have hts : t * (s : G) = (s : G) * t := (Subgroup.mem_centralizer_singleton_iff.mp s.2).symm
  have hts' : t' * ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') =
      ((φ s : ↥(Subgroup.centralizer ({t'} : Set G'))) : G') * t' :=
    (Subgroup.mem_centralizer_singleton_iff.mp (φ s).2).symm
  have hnot : ∀ x : G, IsConj z₀ x → ¬ IsConj t x := fun x hz hx =>
    hT.not_isConj (hx.trans hz.symm)
  have hnot' : ∀ x : G', IsConj z₀' x → ¬ IsConj t' x := fun x hz hx =>
    hT'.not_isConj (hx.trans hz.symm)
  obtain ⟨hBZ, hBU, hZU⟩ := S4Fusion.tableVOrder_ne
  rcases S4Fusion.fusion_cases hT s.2 hs2 hst with ⟨h1, hc1⟩ | ⟨h1, hc1⟩ | ⟨hc1, h1⟩ <;>
    rcases S4Fusion.fusion_cases hT' (φ s).2 hs2' hst' with ⟨h2, hc2⟩ | ⟨h2, hc2⟩ | ⟨hc2, h2⟩
  · exact iff_of_true h1 h2
  · rw [hc1, hc2] at hcard
    exact absurd hcard.symm hBU
  · rw [hc1, hc2] at hcard
    exact absurd hcard.symm hBZ
  · rw [hc1, hc2] at hcard
    exact absurd hcard hBU
  · exact iff_of_false h1 h2
  · rw [hc1, hc2] at hcard
    exact absurd hcard hZU
  · rw [hc1, hc2] at hcard
    exact absurd hcard hBZ
  · rw [hc1, hc2] at hcard
    exact absurd hcard.symm hZU
  ·
    rcases h1 with ⟨hz1, hm1⟩ | ⟨hA1, hB1⟩ <;> rcases h2 with ⟨hz2, hm2⟩ | ⟨hA2, hB2⟩
    · exact iff_of_false (hnot _ hz1) (hnot' _ hz2)
    · exact absurd (hPiff.mp (S4Fusion.hasNormalTwoCommutator_of_isConj_mul co1ModuleUniqueness
        hT (IsConj.refl t) hz1 hts hm1))
        (S4Fusion.not_hasNormalTwoCommutator co1ModuleUniqueness hNF hT' (IsConj.refl t') hA2
          hts' hB2)
    · exact absurd (hPiff.mpr (S4Fusion.hasNormalTwoCommutator_of_isConj_mul co1ModuleUniqueness
        hT' (IsConj.refl t') hz2 hts' hm2))
        (S4Fusion.not_hasNormalTwoCommutator co1ModuleUniqueness hNF hT (IsConj.refl t) hA1
          hts hB1)
    · exact iff_of_true hA1 hA2

end CFSG.Monster.GMS
