module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

@[expose] def IsSec (S : Type*) [Group S] (G : Type*) [Group G] : Prop :=
  ∃ H : Subgroup G, ∃ φ : H →* S, Function.Surjective φ

variable {S G G' : Type*} [Group S] [Group G] [Group G']

private lemma isSec_of_injective {K : Type*} [Group K] (φ : K →* S) (hφ : Function.Surjective φ)
    (j : K →* G) (hj : Function.Injective j) : IsSec S G := by
  refine ⟨j.range, φ.comp (MonoidHom.ofInjective hj).symm.toMonoidHom, ?_⟩
  intro s
  obtain ⟨k, rfl⟩ := hφ s
  exact ⟨MonoidHom.ofInjective hj k, by simp⟩

theorem isSec_of_surjective (f : G →* S) (hf : Function.Surjective f) : IsSec S G :=
  isSec_of_injective f hf (MonoidHom.id G) (fun _ _ h => h)

theorem IsSec.card_dvd [Finite G] (h : IsSec S G) : Nat.card S ∣ Nat.card G := by
  obtain ⟨H, φ, hφ⟩ := h
  exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card H)

theorem IsSec.of_subgroup {H : Subgroup G} (h : IsSec S H) : IsSec S G := by
  obtain ⟨K, φ, hφ⟩ := h
  exact isSec_of_injective φ hφ (H.subtype.comp K.subtype)
    (H.subtype_injective.comp K.subtype_injective)

theorem IsSec.of_surjective {f : G →* G'} (hf : Function.Surjective f) (h : IsSec S G') :
    IsSec S G := by
  obtain ⟨K, φ, hφ⟩ := h
  refine ⟨K.comap f,
    φ.comp ((f.comp (K.comap f).subtype).codRestrict K fun x => Subgroup.mem_comap.mp x.2), ?_⟩
  intro s
  obtain ⟨k, hk⟩ := hφ s
  obtain ⟨g, hg⟩ := hf k.1
  have hgK : f g ∈ K := by
    rw [hg]
    exact k.2
  refine ⟨⟨g, Subgroup.mem_comap.mpr hgK⟩, ?_⟩
  have hgk : (⟨f g, hgK⟩ : K) = k := Subtype.ext hg
  exact (congrArg φ hgk).trans hk

theorem IsSec.of_mulEquiv (e : G ≃* G') (h : IsSec S G) : IsSec S G' :=
  IsSec.of_surjective (f := e.symm.toMonoidHom) e.symm.surjective h

private lemma map_subgroupOf_eq_bot_or_top [IsSimpleGroup S] {H N : Subgroup G} [N.Normal]
    (φ : H →* S) (hφ : Function.Surjective φ) :
    (N.subgroupOf H).map φ = ⊥ ∨ (N.subgroupOf H).map φ = ⊤ := by
  have hK : (N.subgroupOf H).Normal := inferInstance
  have hnorm : ((N.subgroupOf H).map φ).Normal := Subgroup.Normal.map hK φ hφ
  exact IsSimpleGroup.eq_bot_or_eq_top_of_normal _

private lemma isSec_quotient_of_map_eq_bot {H N : Subgroup G} [N.Normal] (φ : H →* S)
    (hφ : Function.Surjective φ) (h : (N.subgroupOf H).map φ = ⊥) : IsSec S (G ⧸ N) := by
  have hπ' : Function.Surjective ((QuotientGroup.mk' N).subgroupMap H) :=
    (QuotientGroup.mk' N).subgroupMap_surjective H
  have hker : ((QuotientGroup.mk' N).subgroupMap H).ker ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxN : x ∈ N.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact (QuotientGroup.eq_one_iff ((x : H) : G)).mp (congrArg Subtype.val hx)
    have hmem : φ x ∈ (N.subgroupOf H).map φ := Subgroup.mem_map_of_mem φ hxN
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  let π' := (QuotientGroup.mk' N).subgroupMap H
  let e := QuotientGroup.quotientKerEquivOfSurjective π' hπ'
  refine ⟨H.map (QuotientGroup.mk' N),
    (QuotientGroup.lift π'.ker φ hker).comp e.symm.toMonoidHom, ?_⟩
  intro s
  obtain ⟨x, rfl⟩ := hφ s
  refine ⟨π' x, ?_⟩
  have hx : e.symm (π' x) = (QuotientGroup.mk x : H ⧸ π'.ker) := e.symm_apply_eq.mpr rfl
  show QuotientGroup.lift π'.ker φ hker (e.symm (π' x)) = φ x
  exact congrArg (QuotientGroup.lift π'.ker φ hker) hx

theorem IsSec.quotient_of_not_dvd [Finite G] [IsSimpleGroup S] [Finite S]
    (hS : 3 ∣ Nat.card S) {N : Subgroup G} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    (h : IsSec S G) : IsSec S (G ⧸ N) := by
  obtain ⟨H, φ, hφ⟩ := h
  refine isSec_quotient_of_map_eq_bot φ hφ ?_
  rcases map_subgroupOf_eq_bot_or_top (N := N) φ hφ with hbot | htop
  · exact hbot
  · exfalso
    have h1 : Nat.card S = Nat.card ((N.subgroupOf H).map φ) := by
      rw [htop, Subgroup.card_top]
    have h2 : Nat.card S ∣ Nat.card (N.subgroupOf H) := by
      rw [h1]
      exact Subgroup.card_map_dvd (N.subgroupOf H) φ
    have h3 : Nat.card (N.subgroupOf H) ∣ Nat.card N :=
      Subgroup.card_comap_dvd_of_injective N H.subtype H.subtype_injective
    exact hN (hS.trans (h2.trans h3))

theorem IsSec.quotient_of_isSolvable [Finite G] [IsSimpleGroup S] (hS : ¬ IsSolvable S)
    {N : Subgroup G} [N.Normal] (hN : IsSolvable N) (h : IsSec S G) : IsSec S (G ⧸ N) := by
  obtain ⟨H, φ, hφ⟩ := h
  refine isSec_quotient_of_map_eq_bot φ hφ ?_
  rcases map_subgroupOf_eq_bot_or_top (N := N) φ hφ with hbot | htop
  · exact hbot
  · exfalso
    haveI : Group.IsSolvable N := hN
    let jN : (N.subgroupOf H) →* N :=
      (H.subtype.comp (N.subgroupOf H).subtype).codRestrict N
        fun x => Subgroup.mem_subgroupOf.mp x.2
    have hjN : Function.Injective jN := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val hab
      exact h'
    haveI : Group.IsSolvable (N.subgroupOf H) := Group.isSolvable_of_isSolvable_injective hjN
    have hψ : Function.Surjective (φ.comp (N.subgroupOf H).subtype) := by
      intro s
      have hs : s ∈ (N.subgroupOf H).map φ := by
        rw [htop]
        exact Subgroup.mem_top s
      obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
      exact ⟨⟨x, hx⟩, hxs⟩
    exact hS (Group.isSolvable_of_surjective hψ)

theorem IsSec.of_index_not_dvd [Finite G] [IsSimpleGroup S] [Finite S]
    (hS : 3 ∣ Nat.card S) {D : Subgroup G} [D.Normal] (hD : ¬ 3 ∣ D.index)
    (h : IsSec S G) : IsSec S D := by
  obtain ⟨H, φ, hφ⟩ := h
  rcases map_subgroupOf_eq_bot_or_top (N := D) φ hφ with hbot | htop
  · exfalso
    have hker : D.subgroupOf H ≤ φ.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have hmem : φ x ∈ (D.subgroupOf H).map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hq : Function.Surjective (QuotientGroup.lift (D.subgroupOf H) φ hker) := by
      intro s
      obtain ⟨x, rfl⟩ := hφ s
      exact ⟨(QuotientGroup.mk x : H ⧸ D.subgroupOf H), rfl⟩
    have h1 : Nat.card S ∣ D.index := by
      have h2 : Nat.card S ∣ Nat.card (H ⧸ D.subgroupOf H) :=
        Subgroup.card_dvd_of_surjective hq
      have h3 : Nat.card (H ⧸ D.subgroupOf H) = D.relIndex H := rfl
      rw [h3] at h2
      exact h2.trans (Subgroup.relIndex_dvd_index_of_normal D H)
    exact hD (hS.trans h1)
  · have hψ : Function.Surjective (φ.comp (D.subgroupOf H).subtype) := by
      intro s
      have hs : s ∈ (D.subgroupOf H).map φ := by
        rw [htop]
        exact Subgroup.mem_top s
      obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hs
      exact ⟨⟨x, hx⟩, hxs⟩
    let j : (D.subgroupOf H) →* D :=
      (H.subtype.comp (D.subgroupOf H).subtype).codRestrict D
        fun x => Subgroup.mem_subgroupOf.mp x.2
    have hj : Function.Injective j := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have h' := congrArg Subtype.val hab
      exact h'
    exact isSec_of_injective _ hψ j hj

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
