module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.NormalizerGeometry
public import CFSG.CharacterTheory.TwoRankLowerBound.RankTransport
public import CFSG.Assembly.OrderReductions.InvolutionGraph

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.OrderReductions.InvolutionGraph
open scoped Pointwise

variable {G : Type*} [Group G]

theorem map_conj_one (U : Subgroup G) :
    U.map (MulAut.conj (1 : G)).toMonoidHom = U := by
  have hhom : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
      MonoidHom.id_apply]
  rw [hhom, Subgroup.map_id]

@[expose] def conjugateInvolutions (U : Subgroup G) : Set G :=
  Group.conjugatesOfSet ((U : Set G) \ {1})

theorem mem_conjugateInvolutions_iff (U : Subgroup G) {x : G} :
    x ∈ conjugateInvolutions U ↔
      ∃ g : G, x ∈ U.map (MulAut.conj g).toMonoidHom ∧ x ≠ 1 := by
  constructor
  · intro hx
    obtain ⟨u, hu, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    refine ⟨g, Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hu.1, ?_⟩
    intro hone
    apply hu.2
    apply Set.mem_singleton_iff.mpr
    apply (MulAut.conj g).injective
    simpa only [MulAut.conj_apply, map_one] using hone
  · rintro ⟨g, hx, hxne⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    apply Group.mem_conjugatesOfSet_iff.mpr
    refine ⟨u, ⟨hu, ?_⟩, isConj_iff.mpr ⟨g, rfl⟩⟩
    intro hone
    have huone := Set.mem_singleton_iff.mp hone
    exact hxne (by simp only [huone, map_one])

theorem conjugateInvolutions_conj_mem (U : Subgroup G) {x : G}
    (hx : x ∈ conjugateInvolutions U) (g : G) :
    (MulAut.conj g) x ∈ conjugateInvolutions U :=
  Group.conj_mem_conjugatesOfSet hx

theorem conjugateInvolutions_order_two (U : Subgroup G) (hUel : IsElemAbelian 2 U)
    {x : G} (hx : x ∈ conjugateInvolutions U) : orderOf x = 2 := by
  obtain ⟨g, hxg, hxne⟩ := (mem_conjugateInvolutions_iff U).mp hx
  have hel := CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel
    (MulAut.conj g).toMonoidHom
  exact orderOf_eq_prime_iff.mpr ⟨hel.2 x hxg, hxne⟩

theorem distinct_conjugates_inf_eq_bot (U : Subgroup G) (hTI : fusionIsTI U)
    (a b : G)
    (hne : U.map (MulAut.conj a).toMonoidHom ≠ U.map (MulAut.conj b).toMonoidHom) :
    U.map (MulAut.conj a).toMonoidHom ⊓
      U.map (MulAut.conj b).toMonoidHom = ⊥ := by
  apply Subgroup.map_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
    (MulAut.conj a⁻¹).injective
  rw [Subgroup.map_inf _ _ _ (MulAut.conj a⁻¹).injective,
    map_conj_map_conj, map_conj_map_conj, inv_mul_cancel]
  rw [map_conj_one, Subgroup.map_bot]
  apply hTI (a⁻¹ * b)
  intro heq
  apply hne
  apply Subgroup.map_injective (f := (MulAut.conj a⁻¹).toMonoidHom)
    (MulAut.conj a⁻¹).injective
  rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel]
  simpa only [map_conj_one] using heq.symm

theorem conjugates_eq_of_common_nonidentity (U : Subgroup G) (hTI : fusionIsTI U)
    (a b : G) {x : G} (hxne : x ≠ 1)
    (hxa : x ∈ U.map (MulAut.conj a).toMonoidHom)
    (hxb : x ∈ U.map (MulAut.conj b).toMonoidHom) :
    U.map (MulAut.conj a).toMonoidHom = U.map (MulAut.conj b).toMonoidHom := by
  by_contra hne
  exact hxne (Subgroup.mem_bot.mp
    ((distinct_conjugates_inf_eq_bot U hTI a b hne) ▸
      (show x ∈ U.map (MulAut.conj a).toMonoidHom ⊓
        U.map (MulAut.conj b).toMonoidHom from ⟨hxa, hxb⟩)))

variable [Finite G]

omit [Finite G] in
theorem conjugateInvolutions_inter_sylow (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G))
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) :
    conjugateInvolutions U ∩ (T : Set G) = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨hx, hxT⟩
    obtain ⟨g, hxg, hxne⟩ := (mem_conjugateInvolutions_iff U).mp hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxg
    refine ⟨?_, by simpa only [Set.mem_singleton_iff] using hxne⟩
    have hmem : g * u * g⁻¹ ∈ (T : Subgroup G) := hxT
    change g * u * g⁻¹ ∈ (U : Set G)
    simpa only [inv_inv] using hclosed u hu g⁻¹ (by simpa only [inv_inv] using hmem)
  · rintro ⟨hxU, hxne⟩
    exact ⟨Group.subset_conjugatesOfSet ⟨hxU, hxne⟩, hUT hxU⟩

theorem conjugates_eq_of_normalizing_member (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (a b : G) {x : G}
    (hxa : x ∈ U.map (MulAut.conj a).toMonoidHom) (hxne : x ≠ 1)
    (hxn : x ∈ Subgroup.normalizer
      (U.map (MulAut.conj b).toMonoidHom : Set G)) :
    U.map (MulAut.conj a).toMonoidHom = U.map (MulAut.conj b).toMonoidHom := by
  let e := MulAut.conj a⁻¹
  have hxU : e x ∈ U := by
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hxa
    rw [map_conj_map_conj, inv_mul_cancel] at hmem
    rw [map_conj_one] at hmem
    exact hmem
  have hxne' : e x ≠ 1 := fun h => hxne (e.injective (h.trans (map_one e).symm))
  have hxn' : e x ∈ Subgroup.normalizer
      (U.map (MulAut.conj (a⁻¹ * b)).toMonoidHom : Set G) := by
    have hmem := Subgroup.mem_map_of_mem e.toMonoidHom hxn
    rw [Subgroup.map_equiv_normalizer_eq] at hmem
    rw [map_conj_map_conj] at hmem
    exact hmem
  have heq := conjugate_eq_of_mem_normalizer T U hUT hUel hclosed hTI hxU hxne'
    (a⁻¹ * b) hxn'
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_conj_map_conj, map_conj_map_conj, inv_mul_cancel]
  simpa only [map_conj_one] using heq.symm

theorem conjugateInvolutions_inter_normalizer (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) :
    conjugateInvolutions U ∩ Subgroup.normalizer (U : Set G) = (U : Set G) \ {1} := by
  ext x
  constructor
  · rintro ⟨hxD, hxN⟩
    obtain ⟨g, hxg, hxne⟩ := (mem_conjugateInvolutions_iff U).mp hxD
    have hxN' : x ∈ Subgroup.normalizer
        (U.map (MulAut.conj (1 : G)).toMonoidHom : Set G) := by
      rw [map_conj_one]
      exact hxN
    have heq := conjugates_eq_of_normalizing_member T U hUT hUel hclosed hTI g 1
      hxg hxne hxN'
    have hxU : x ∈ U := by
      rw [heq] at hxg
      simpa only [map_conj_one] using hxg
    exact ⟨hxU, by simpa only [Set.mem_singleton_iff] using hxne⟩
  · rintro ⟨hxU, hxne⟩
    exact ⟨Group.subset_conjugatesOfSet ⟨hxU, hxne⟩, U.le_normalizer hxU⟩

theorem conjugates_eq_of_commuting_members (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (a b : G) {x y : G}
    (hxa : x ∈ U.map (MulAut.conj a).toMonoidHom) (hxne : x ≠ 1)
    (hyb : y ∈ U.map (MulAut.conj b).toMonoidHom) (hyne : y ≠ 1)
    (hcomm : Commute x y) :
    U.map (MulAut.conj a).toMonoidHom = U.map (MulAut.conj b).toMonoidHom := by
  have hfixed : (MulAut.conj y) x = x := by
    change y * x * y⁻¹ = x
    rw [← hcomm.eq]
    group
  have hxya : x ∈ (U.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj y).toMonoidHom := by
    rw [← hfixed]
    exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hxa
  rw [map_conj_map_conj] at hxya
  have hnormalizes : y ∈ Subgroup.normalizer
      (U.map (MulAut.conj a).toMonoidHom : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (U.map (MulAut.conj a).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      U.map (MulAut.conj a).toMonoidHom
    rw [map_conj_map_conj]
    exact (conjugates_eq_of_common_nonidentity U hTI a (y * a) hxne hxa hxya).symm
  exact (conjugates_eq_of_normalizing_member T U hUT hUel hclosed hTI b a
    hyb hyne hnormalizes).symm

theorem conjugateInvolutions_mul_mem (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) {x y : G} (hx : x ∈ conjugateInvolutions U)
    (hy : y ∈ conjugateInvolutions U) (hne : x ≠ y) (hcomm : Commute x y) :
    x * y ∈ conjugateInvolutions U := by
  obtain ⟨a, hxa, hxne⟩ := (mem_conjugateInvolutions_iff U).mp hx
  obtain ⟨b, hyb, hyne⟩ := (mem_conjugateInvolutions_iff U).mp hy
  have heq := conjugates_eq_of_commuting_members T U hUT hUel hclosed hTI a b
    hxa hxne hyb hyne hcomm
  have hya : y ∈ U.map (MulAut.conj a).toMonoidHom := heq.symm ▸ hyb
  refine (mem_conjugateInvolutions_iff U).mpr
    ⟨a, (U.map (MulAut.conj a).toMonoidHom).mul_mem hxa hya, ?_⟩
  intro hxy
  have heqxy : x = y⁻¹ := mul_eq_one_iff_eq_inv.mp hxy
  exact hne (heqxy.trans (inv_eq_self_of_orderOf_eq_two
    (conjugateInvolutions_order_two U hUel hy)))

omit [Finite G] in
@[expose] def conjugateCommutingGraph (U : Subgroup G) (hUel : IsElemAbelian 2 U) :
    SimpleGraph (conjugateInvolutions U) :=
  (commutingGraph G).comap
    (fun x => (⟨x, conjugateInvolutions_order_two U hUel x.property⟩ : Involution G))

theorem conjugateCommutingGraph_adj_iff (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x y : conjugateInvolutions U) :
    (conjugateCommutingGraph U hUel).Adj x y ↔
      x ≠ y ∧ ∃ g : G, (x : G) ∈ U.map (MulAut.conj g).toMonoidHom ∧
        (y : G) ∈ U.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hadj
    have hxy : x ≠ y := fun h => hadj.1 (congrArg
      (fun v : conjugateInvolutions U =>
        (⟨v, conjugateInvolutions_order_two U hUel v.property⟩ : Involution G)) h)
    obtain ⟨a, hxa, hxne⟩ := (mem_conjugateInvolutions_iff U).mp x.property
    obtain ⟨b, hyb, hyne⟩ := (mem_conjugateInvolutions_iff U).mp y.property
    have heq := conjugates_eq_of_commuting_members T U hUT hUel hclosed hTI a b
      hxa hxne hyb hyne hadj.2
    exact ⟨hxy, a, hxa, heq.symm ▸ hyb⟩
  · rintro ⟨hxy, g, hxg, hyg⟩
    have hel := CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel
      (MulAut.conj g).toMonoidHom
    refine ⟨?_, ?_⟩
    · intro heq
      change (⟨(x : G), conjugateInvolutions_order_two U hUel x.property⟩ : Involution G) =
        ⟨(y : G), conjugateInvolutions_order_two U hUel y.property⟩ at heq
      exact hxy (Subtype.ext (congrArg (fun v : Involution G => (v : G)) heq))
    · exact congrArg Subtype.val
        (isMulCommutative_iff.mp hel.1 (⟨x, hxg⟩ : U.map (MulAut.conj g).toMonoidHom)
          (⟨y, hyg⟩ : U.map (MulAut.conj g).toMonoidHom))

theorem conjugateCommutingGraph_reachable_iff (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x y : conjugateInvolutions U) :
    (conjugateCommutingGraph U hUel).Reachable x y ↔
      ∃ g : G, (x : G) ∈ U.map (MulAut.conj g).toMonoidHom ∧
        (y : G) ∈ U.map (MulAut.conj g).toMonoidHom := by
  constructor
  · intro hreach
    apply hreach.elim
    intro walk
    clear hreach
    induction walk with
    | @nil v =>
      obtain ⟨g, hxg, _⟩ := (mem_conjugateInvolutions_iff U).mp v.property
      exact ⟨g, hxg, hxg⟩
    | @cons x v y hadj tail ih =>
      obtain ⟨g, hxg, hvg⟩ :=
        ((conjugateCommutingGraph_adj_iff T U hUT hUel hclosed hTI x v).mp hadj).2
      obtain ⟨a, hva, hya⟩ := ih
      have hvne := ((mem_conjugateInvolutions_iff U).mp v.property).choose_spec.2
      have heq := conjugates_eq_of_common_nonidentity U hTI g a hvne hvg hva
      exact ⟨g, hxg, heq.symm ▸ hya⟩
  · rintro ⟨g, hxg, hyg⟩
    by_cases hxy : x = y
    · exact hxy ▸ SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable
        ((conjugateCommutingGraph_adj_iff T U hUT hUel hclosed hTI x y).mpr
          ⟨hxy, g, hxg, hyg⟩)

theorem conjugateCommutingGraph_component_support (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x : conjugateInvolutions U) (g : G)
    (hxg : (x : G) ∈ U.map (MulAut.conj g).toMonoidHom) :
    ((conjugateCommutingGraph U hUel).connectedComponentMk x).supp =
      {y : conjugateInvolutions U | (y : G) ∈ U.map (MulAut.conj g).toMonoidHom} := by
  ext y
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  constructor
  · intro heq
    have hreach := SimpleGraph.ConnectedComponent.exact heq
    obtain ⟨a, hya, hxa⟩ :=
      (conjugateCommutingGraph_reachable_iff T U hUT hUel hclosed hTI y x).mp hreach
    have hxne := ((mem_conjugateInvolutions_iff U).mp x.property).choose_spec.2
    have heqg := conjugates_eq_of_common_nonidentity U hTI a g hxne hxa hxg
    exact heqg ▸ hya
  · intro hyg
    exact SimpleGraph.ConnectedComponent.sound
      ((conjugateCommutingGraph_reachable_iff T U hUT hUel hclosed hTI y x).mpr
        ⟨g, hyg, hxg⟩)

theorem conjugateCommutingGraph_all_components (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (C : (conjugateCommutingGraph U hUel).ConnectedComponent) :
    ∃ g : G, C.supp =
      {y : conjugateInvolutions U | (y : G) ∈ U.map (MulAut.conj g).toMonoidHom} := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h x =>
    obtain ⟨g, hxg, _⟩ := (mem_conjugateInvolutions_iff U).mp x.property
    exact ⟨g, conjugateCommutingGraph_component_support T U hUT hUel hclosed hTI x g hxg⟩

theorem normalizer_in_distinct_conjugate_eq_bot (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (g : G) (hg : U.map (MulAut.conj g).toMonoidHom ≠ U) :
    (Subgroup.normalizer (U : Set G)).subgroupOf
      (U.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  by_contra hne
  have hxN : (x : G) ∈ Subgroup.normalizer
      (U.map (MulAut.conj (1 : G)).toMonoidHom : Set G) := by
    rw [map_conj_one]
    exact hx
  have heq := conjugates_eq_of_normalizing_member T U hUT hUel hclosed hTI g 1
    x.property hne hxN
  exact hg (by simpa only [map_conj_one] using heq)

theorem conjugateCommutingGraph_not_preconnected (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal) :
    ¬ (conjugateCommutingGraph U hUel).Preconnected := by
  intro hconnected
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hzneG : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  have hzD : (z : G) ∈ conjugateInvolutions U :=
    Group.subset_conjugatesOfSet ⟨z.property, by simpa only [Set.mem_singleton_iff] using hzneG⟩
  have hN : Subgroup.normalizer (U : Set G) = ⊤ := by
    apply top_unique
    intro g _
    let z' := (MulAut.conj g) (z : G)
    have hz'D : z' ∈ conjugateInvolutions U := conjugateInvolutions_conj_mem U hzD g
    have hreached := hconnected (⟨z, hzD⟩ : conjugateInvolutions U) ⟨z', hz'D⟩
    obtain ⟨a, hza, hz'a⟩ :=
      (conjugateCommutingGraph_reachable_iff T U hUT hUel hclosed hTI _ _).mp hreached
    have ha : U.map (MulAut.conj a).toMonoidHom = U := by
      have hz1 : (z : G) ∈ U.map (MulAut.conj (1 : G)).toMonoidHom :=
        (map_conj_one U).symm ▸ z.property
      have heq := conjugates_eq_of_common_nonidentity U hTI a 1 hzneG hza hz1
      simpa only [map_conj_one] using heq
    have hzg : z' ∈ U.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom z.property
    have hz'ne : z' ≠ 1 := by
      intro h
      exact hzneG ((MulAut.conj g).injective (h.trans (map_one (MulAut.conj g)).symm))
    have hgU : U.map (MulAut.conj g).toMonoidHom = U := by
      have heq := conjugates_eq_of_common_nonidentity U hTI g a hz'ne hzg hz'a
      exact heq.trans ha
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hgU
  exact hnormal (Subgroup.normalizer_eq_top_iff.mp hN)

end CFSG.ShultStronglyClosedTI
