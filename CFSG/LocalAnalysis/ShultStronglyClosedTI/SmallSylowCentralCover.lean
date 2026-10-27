module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer

public noncomputable section

open scoped commutatorElement IsMulCommutative

namespace CFSG.ShultStronglyClosedTI

theorem central_kernel_sylow_unique {E J : Type*} [Group E] [Finite E] [Group J]
    {p : ℕ} [Fact p.Prime] (f : E →* J)
    (hcentral : f.ker ≤ Subgroup.center E) (C D : Sylow p f.ker) :
    C = D := by
  have hcomm : IsMulCommutative f.ker := by
    exact ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp
      (hcentral a.property) b.val).symm)⟩⟩
  let : IsMulCommutative f.ker := hcomm
  let : Unique (Sylow p f.ker) :=
    Sylow.unique_of_normal C (Subgroup.normal_of_isMulCommutative _)
  exact Subsingleton.elim _ _

theorem central_kernel_sylow_restriction {E J : Type*} [Group E] [Finite E] [Group J]
    {p : ℕ} [Fact p.Prime] (f : E →* J)
    (hcentral : f.ker ≤ Subgroup.center E) (C : Sylow p f.ker) (P : Sylow p E) :
    (f.subgroupMap (P : Subgroup E)).ker =
      (((C : Subgroup f.ker).map f.ker.subtype).subgroupOf (P : Subgroup E)) := by
  have hKcenter : IsMulCommutative f.ker := by
    exact ⟨⟨fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp
      (hcentral a.property) b.val).symm)⟩⟩
  let : IsMulCommutative f.ker := hKcenter
  let : (C : Subgroup f.ker).Normal := Subgroup.normal_of_isMulCommutative _
  have hPC : ((P : Subgroup E).comap f.ker.subtype) ≤ (C : Subgroup f.ker) := by
    exact (P.isPGroup'.comap_of_injective f.ker.subtype Subtype.coe_injective).le_sylow_of_normal C
  ext a
  constructor
  · intro ha
    have hak : f a.val = 1 := congrArg Subtype.val ha
    have hac : (⟨a.val, hak⟩ : f.ker) ∈ (C : Subgroup f.ker) := hPC a.property
    exact Subgroup.mem_map.mpr ⟨⟨a.val, hak⟩, hac, rfl⟩
  · intro ha
    change f.subgroupMap (P : Subgroup E) a = 1
    apply Subtype.ext
    obtain ⟨c, _, hc⟩ := Subgroup.mem_map.mp ha
    change f a.val = 1
    change c.val = a.val at hc
    rw [← hc]
    exact c.property

theorem central_kernel_sylow_restriction_le_derived {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J]
    {p : ℕ} [Fact p.Prime] (f : E →* J)
    (hcentral : f.ker ≤ Subgroup.center E) (C : Sylow p f.ker) (P : Sylow p E) :
    (f.subgroupMap (P : Subgroup E)).ker ≤ commutator (P : Subgroup E) := by
  rw [central_kernel_sylow_restriction f hcentral C P]
  intro a ha
  have hcenter : a.val ∈ Subgroup.center E := by
    obtain ⟨c, _, hc⟩ := Subgroup.mem_map.mp ha
    change c.val = a.val at hc
    rw [← hc]
    exact hcentral c.property
  exact central_element_mem_sylow_derived P a hcenter

theorem elementary_rank_two_generators {K : Type*} [Group K] [Finite K]
    [IsMulCommutative K] {p : ℕ} [Fact p.Prime]
    (hpow : ∀ a : K, a ^ p = 1) (hcard : Nat.card K = p ^ 2) :
    ∃ x y : K, Subgroup.closure ({x, y} : Set K) = ⊤ := by
  have hp : p.Prime := Fact.out
  have hnontrivial : Nontrivial K := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    let : Subsingleton K := hsub
    have hone : Nat.card K = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hp2 := hp.two_le
    rw [hcard, pow_two] at hone
    nlinarith
  let : Nontrivial K := hnontrivial
  obtain ⟨x, hx⟩ := exists_ne (1 : K)
  have hxorder : orderOf x = p := by
    exact (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hpow x))).resolve_left
      (fun h => hx (orderOf_eq_one_iff.mp h))
  let N := Subgroup.zpowers x
  let : N.Normal := Subgroup.normal_of_isMulCommutative N
  have hNcard : Nat.card N = p := by rw [Nat.card_zpowers, hxorder]
  have hquot : Nat.card (K ⧸ N) = p := by
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    calc
      Nat.card (K ⧸ N) * p = Nat.card K := by
        rw [← hNcard, ← N.card_eq_card_quotient_mul_card_subgroup]
      _ = p * p := by rw [hcard, pow_two]
  let : IsCyclic (K ⧸ N) := isCyclic_of_prime_card hquot
  obtain ⟨a, ha⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic (K ⧸ N))
  let q := QuotientGroup.mk' N
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective N a
  have hmap : (Subgroup.zpowers y).map q = ⊤ := by rw [MonoidHom.map_zpowers, hy, ha]
  have hsup : Subgroup.zpowers y ⊔ N = ⊤ := by
    have h := Subgroup.comap_map_eq q (Subgroup.zpowers y)
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  refine ⟨x, y, top_unique ?_⟩
  rw [← hsup]
  exact sup_le
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
    (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))

theorem commutative_of_pair_and_center {H : Type*} [Group H]
    (x y : H) (C : Subgroup H) (hC : C ≤ Subgroup.center H)
    (hxy : Commute x y) (hgen : Subgroup.closure ({x, y} : Set H) ⊔ C = ⊤) :
    IsMulCommutative H := by
  let s : Set H := {x, y} ∪ (C : Set H)
  have hpairs : s.Pairwise Commute := by
    intro a ha b hb _
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Commute.refl _
        · exact hxy
        · exact hxy.symm
        · exact Commute.refl _
      · exact Subgroup.mem_center_iff.mp (hC hb) a
    · exact (Subgroup.mem_center_iff.mp (hC ha) b).symm
  have hcl : Subgroup.closure s = ⊤ := by
    rw [Subgroup.closure_union, Subgroup.closure_eq]
    exact hgen
  have hcomm : IsMulCommutative (Subgroup.closure s) :=
    Subgroup.isMulCommutative_closure hpairs
  rw [hcl] at hcomm
  let : IsMulCommutative (⊤ : Subgroup H) := hcomm
  exact ⟨⟨fun a b => congrArg Subtype.val
    (mul_comm (⟨a, Subgroup.mem_top a⟩ : (⊤ : Subgroup H)) ⟨b, Subgroup.mem_top b⟩)⟩⟩

theorem central_two_generator_derived_eq_zpowers {H K : Type*} [Group H] [Group K]
    [IsMulCommutative K] (f : H →* K)
    (hcentral : f.ker ≤ Subgroup.center H) (x y : H)
    (hgen : Subgroup.closure ({f x, f y} : Set K) = ⊤) :
    commutator H = Subgroup.zpowers ⁅x, y⁆ := by
  have hderived : commutator H ≤ f.ker := Abelianization.commutator_subset_ker f
  have hz : ⁅x, y⁆ ∈ commutator H :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  let N := Subgroup.zpowers ⁅x, y⁆
  have hNcenter : N ≤ Subgroup.center H :=
    Subgroup.zpowers_le.mpr (hcentral (hderived hz))
  let : N.Normal := Subgroup.normal_of_le_center hNcenter
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hmap : (Subgroup.closure ({x, y} : Set H)).map f = ⊤ := by
    rw [MonoidHom.map_closure, Set.image_pair]
    exact hgen
  have hjoin : Subgroup.closure ({x, y} : Set H) ⊔ f.ker = ⊤ := by
    have h := Subgroup.comap_map_eq f (Subgroup.closure ({x, y} : Set H))
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm
  have hqjoin := congrArg (Subgroup.map q) hjoin
  rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair,
    Subgroup.map_top_of_surjective q hqsurj] at hqjoin
  have hqcenter : f.ker.map q ≤ Subgroup.center (H ⧸ N) :=
    (Subgroup.map_mono hcentral).trans (Subgroup.map_center_le_center hqsurj)
  have hqxy : Commute (q x) (q y) := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff ⁅x, y⁆).mpr (Subgroup.mem_zpowers ⁅x, y⁆)
  have hqcomm : IsMulCommutative (H ⧸ N) :=
    commutative_of_pair_and_center (q x) (q y) (f.ker.map q) hqcenter hqxy hqjoin
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hqcomm
  · exact Subgroup.zpowers_le.mpr hz

theorem central_two_generator_derived_bound {H K : Type*} [Group H] [Group K]
    [IsMulCommutative K] {p : ℕ} [Fact p.Prime]
    (f : H →* K)
    (hcentral : f.ker ≤ Subgroup.center H) (hpow : ∀ a : K, a ^ p = 1)
    (x y : H) (hgen : Subgroup.closure ({f x, f y} : Set K) = ⊤) :
    IsCyclic (commutator H) ∧ Nat.card (commutator H) ≤ p := by
  have hderived : commutator H ≤ f.ker := Abelianization.commutator_subset_ker f
  have hz : ⁅x, y⁆ ∈ Subgroup.center H := hcentral (hderived
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)))
  have hx : x ^ p ∈ Subgroup.center H := by
    apply hcentral
    change f (x ^ p) = 1
    rw [map_pow, hpow]
  have hxp : Commute (x ^ p) y := (Subgroup.mem_center_iff.mp hx y).symm
  have hcz : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hz x
  have hzp : ⁅x, y⁆ ^ p = 1 :=
    (hcz.commutatorElement_pow_left p).trans hxp.commutator_eq
  rw [central_two_generator_derived_eq_zpowers f hcentral x y hgen]
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos (orderOf_dvd_of_pow_eq_one hzp)

theorem central_cover_cyclic_sylow_kernel_eq_bot {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J]
    {p : ℕ} [Fact p.Prime] (f : E →* J) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center E) (C : Sylow p f.ker) (Q : Sylow p J)
    (hcyclic : IsCyclic (Q : Subgroup J)) : (C : Subgroup f.ker) = ⊥ := by
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hsurj p Q
  have hmap : (P : Subgroup E).map f = (Q : Subgroup J) := by
    rw [← Sylow.coe_mapSurjective hsurj P, hP]
  let r := f.subgroupMap (P : Subgroup E)
  have hrcentral : r.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro a ha
    have hak : f a.val = 1 := congrArg Subtype.val ha
    exact Subgroup.mem_center_iff.mpr (fun b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hcentral hak) b.val))
  have hrcyclic : IsCyclic ((P : Subgroup E).map f) := hmap.symm ▸ hcyclic
  let : IsCyclic ((P : Subgroup E).map f) := hrcyclic
  let : IsMulCommutative (P : Subgroup E) :=
    r.isMulCommutative_of_isCyclic_of_ker_le_center hrcentral
  have hrbot : r.ker = ⊥ := by
    apply le_antisymm _ bot_le
    have h := central_kernel_sylow_restriction_le_derived f hcentral C P
    rw [commutator_eq_bot] at h
    exact h
  let A : Subgroup E := (C : Subgroup f.ker).map f.ker.subtype
  have hAP : A ≤ (P : Subgroup E) := central_pSubgroup_le_sylow P A
    ((Subgroup.map_subtype_le (C : Subgroup f.ker)).trans hcentral)
    (C.isPGroup'.map f.ker.subtype)
  apply le_antisymm _ bot_le
  intro c hc
  have ha : c.val ∈ (P : Subgroup E) := hAP (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
  have har : (⟨c.val, ha⟩ : (P : Subgroup E)) ∈ r.ker := by
    apply Subtype.ext
    exact c.property
  have hone := Subgroup.mem_bot.mp (hrbot ▸ har)
  have hvalue : c.val = 1 := congrArg (fun a : (P : Subgroup E) => a.val) hone
  exact Subgroup.mem_bot.mpr (Subtype.ext hvalue)

theorem central_cover_elementary_rank_two_sylow_kernel_bound {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J]
    {p : ℕ} [Fact p.Prime] (f : E →* J) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center E) (C : Sylow p f.ker) (Q : Sylow p J)
    (helementary : CFSG.Open.IsElemAbelian p (Q : Subgroup J))
    (hcard : Nat.card (Q : Subgroup J) = p ^ 2) :
    IsCyclic (C : Subgroup f.ker) ∧ Nat.card (C : Subgroup f.ker) ≤ p := by
  let : Finite J := Finite.of_surjective f hsurj
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hsurj p Q
  have hmap : (P : Subgroup E).map f = (Q : Subgroup J) := by
    rw [← Sylow.coe_mapSurjective hsurj P, hP]
  let r := f.subgroupMap (P : Subgroup E)
  have hrcentral : r.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro a ha
    have hak : f a.val = 1 := congrArg Subtype.val ha
    exact Subgroup.mem_center_iff.mpr (fun b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hcentral hak) b.val))
  have hrelem : CFSG.Open.IsElemAbelian p ((P : Subgroup E).map f) :=
    hmap.symm ▸ helementary
  let : IsMulCommutative ((P : Subgroup E).map f) := hrelem.1
  have hrpow : ∀ a : (P : Subgroup E).map f, a ^ p = 1 := by
    intro a
    exact Subtype.ext (hrelem.2 a.val a.property)
  have hrcard : Nat.card ((P : Subgroup E).map f) = p ^ 2 := hmap.symm ▸ hcard
  obtain ⟨a, b, hab⟩ := elementary_rank_two_generators hrpow hrcard
  obtain ⟨x, hx⟩ := f.subgroupMap_surjective (P : Subgroup E) a
  obtain ⟨y, hy⟩ := f.subgroupMap_surjective (P : Subgroup E) b
  have hgen : Subgroup.closure ({r x, r y} : Set ((P : Subgroup E).map f)) = ⊤ := by
    rw [hx, hy]
    exact hab
  have hbound := central_two_generator_derived_bound r hrcentral hrpow x y hgen
  have hrderived : r.ker = commutator (P : Subgroup E) := le_antisymm
    (central_kernel_sylow_restriction_le_derived f hcentral C P)
    (Abelianization.commutator_subset_ker r)
  let A : Subgroup E := (C : Subgroup f.ker).map f.ker.subtype
  have hAP : A ≤ (P : Subgroup E) := central_pSubgroup_le_sylow P A
    ((Subgroup.map_subtype_le (C : Subgroup f.ker)).trans hcentral)
    (C.isPGroup'.map f.ker.subtype)
  have hlocal : A.subgroupOf (P : Subgroup E) = commutator (P : Subgroup E) :=
    (central_kernel_sylow_restriction f hcentral C P).symm.trans hrderived
  let e : (C : Subgroup f.ker) ≃* commutator (P : Subgroup E) :=
    ((C : Subgroup f.ker).equivMapOfInjective f.ker.subtype Subtype.coe_injective).trans
      ((Subgroup.subgroupOfEquivOfLe hAP).symm.trans (MulEquiv.subgroupCongr hlocal))
  let : IsCyclic (commutator (P : Subgroup E)) := hbound.1
  exact ⟨isCyclic_of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).le.trans hbound.2⟩

theorem small_sylow_central_cover_bound {E J : Type*}
    [Group E] [Finite E] [Group.IsPerfect E] [Group J] [Finite J]
    {p : ℕ} [Fact p.Prime] (f : E →* J) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center E) (C : Sylow p f.ker) (Q : Sylow p J) :
    (IsCyclic (Q : Subgroup J) → (C : Subgroup f.ker) = ⊥) ∧
      (CFSG.Open.IsElemAbelian p (Q : Subgroup J) →
        Nat.card (Q : Subgroup J) = p ^ 2 →
          IsCyclic (C : Subgroup f.ker) ∧ Nat.card (C : Subgroup f.ker) ≤ p) :=
  ⟨central_cover_cyclic_sylow_kernel_eq_bot f hsurj hcentral C Q,
    central_cover_elementary_rank_two_sylow_kernel_bound f hsurj hcentral C Q⟩

end CFSG.ShultStronglyClosedTI
