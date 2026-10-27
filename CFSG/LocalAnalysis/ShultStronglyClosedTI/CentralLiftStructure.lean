module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CentralExtensions

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open scoped commutatorElement

theorem central_lift_derived_series_stable {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect B] (f : A →* B) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center A) (n : ℕ) :
    derivedSeries A (n + 1) = commutator A := by
  let : Group.IsPerfect (commutator A) :=
    CFSG.ComponentClassification.CentralExtensions.derived_perfect f hsurj hcentral
  induction n with
  | zero => exact derivedSeries_one (G := A)
  | succ n ih =>
      rw [derivedSeries_succ, ih]
      exact Subgroup.commutator_eq_self

theorem central_lift_subgroup_map_kernel {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (L : Subgroup G) :
    (f.subgroupMap L).ker = f.ker.subgroupOf L := by
  ext l
  change f.subgroupMap L l = 1 ↔ f l.val = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem central_lift_derived_sup_kernel {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect B] (f : A →* B) (hsurj : Function.Surjective f) :
    commutator A ⊔ f.ker = ⊤ := by
  have h := Subgroup.comap_map_eq f (commutator A)
  rw [CFSG.ComponentClassification.CentralExtensions.derived_map_eq_top f hsurj,
    Subgroup.comap_top] at h
  exact h.symm

theorem central_lift_derived_quotient_card_le_kernel {A B : Type*}
    [Group A] [Finite A] [Group B] [Group.IsPerfect B]
    (f : A →* B) (hsurj : Function.Surjective f) :
    Nat.card (A ⧸ commutator A) ≤ Nat.card f.ker := by
  have hsup := central_lift_derived_sup_kernel f hsurj
  let q := QuotientGroup.mk' (commutator A)
  apply Nat.card_le_card_of_surjective (q.domRestrict f.ker)
  intro y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator A) y
  have ha : a ∈ commutator A ⊔ f.ker := hsup.symm ▸ Subgroup.mem_top a
  obtain ⟨d, hd, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  refine ⟨⟨k, hk⟩, ?_⟩
  change q k = q (d * k)
  have hdq : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
  rw [map_mul, hdq, one_mul]

def centralLiftCenterQuotientEquiv {A B : Type*} [Group A] [Group B]
    [Group.IsPerfect A] (f : A →* B) (hsurj : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center A) :
    (A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B) := by
  let q := (QuotientGroup.mk' (Subgroup.center B)).comp f
  have hker : q.ker = Subgroup.center A := by
    have hpreimage : q.ker = (Subgroup.center B).comap f := by
      ext a
      exact QuotientGroup.eq_one_iff (f a)
    rw [hpreimage]
    exact CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
      f hsurj hcentral
  exact QuotientGroup.liftEquiv (Subgroup.center A)
    ((QuotientGroup.mk'_surjective _).comp hsurj) hker.symm

theorem central_lift_model_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hmodel : fusionIsBenderGroup B) : fusionIsBenderGroup A := by
  rcases hmodel with ⟨f, hf, ⟨m⟩⟩ | ⟨f, hf, ⟨m⟩⟩ | ⟨a, ha, ⟨m⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.trans m⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.trans m⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.trans m⟩⟩)

variable {G : Type*} [Group G]

@[expose] def centralLiftKernel (x : Subgroup.center G) : Subgroup G :=
  Subgroup.zpowers (x : G)

theorem centralLiftKernel_le_center (x : Subgroup.center G) :
    centralLiftKernel x ≤ Subgroup.center G := Subgroup.zpowers_le.mpr x.property

instance centralLiftKernel_normal (x : Subgroup.center G) :
    (centralLiftKernel x).Normal :=
  Subgroup.normal_of_le_center (centralLiftKernel_le_center x)

theorem centralLiftKernel_card_two (x : Subgroup.center G)
    (horder : orderOf (x : G) = 2) : Nat.card (centralLiftKernel x) = 2 := by
  change Nat.card (Subgroup.zpowers (x : G)) = 2
  rw [Nat.card_zpowers, horder]

variable {G : Type*} [Group G] [Finite G]

theorem central_lift_hull_perfect (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZcard : Nat.card Z ≤ 2)
    (himage : IsQuasisimple
      ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' Z))) :
    Group.IsPerfect (Subgroup.normalClosure (U : Set G)) := by
  let L : Subgroup G := Subgroup.normalClosure (U : Set G)
  let π := QuotientGroup.mk' Z
  let Q : Subgroup (G ⧸ Z) := L.map π
  let f : L →* Q := π.subgroupMap L
  have hQ : IsQuasisimple Q := himage
  let : Group.IsPerfect Q := ⟨hQ.1⟩
  let : Nontrivial Q := CFSG.ComponentClassification.Quasisimple.nontrivial hQ
  have hnormalU : ¬ U.Normal := by
    intro hn
    let : U.Normal := hn
    have hLU : L = U := Subgroup.normalClosure_eq_self U
    have hcommQ : IsMulCommutative Q := by
      change IsMulCommutative (L.map π)
      rw [hLU]
      exact (CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel π).1
    exact Group.IsPerfect.not_isMulCommutative Q hcommQ
  have hUbot : U ≠ ⊥ := by
    intro hbot
    simp [hbot] at hcard
  have hUL : U ≤ L := Subgroup.subset_normalClosure
  have hsurj : Function.Surjective f := π.subgroupMap_surjective L
  have hfker : f.ker = Z.subgroupOf L := by
    change (π.subgroupMap L).ker = Z.subgroupOf L
    rw [central_lift_subgroup_map_kernel]
    rw [QuotientGroup.ker_mk']
  have hfcentral : f.ker ≤ Subgroup.center L := by
    rw [hfker]
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZ ha)) b.val)
  let : Group.IsPerfect (commutator L) :=
    CFSG.ComponentClassification.CentralExtensions.derived_perfect f hsurj hfcentral
  have hkernelCard : Nat.card f.ker ≤ Nat.card Z := by
    rw [hfker]
    apply Nat.card_le_card_of_injective
      (fun a : Z.subgroupOf L => (⟨a.val.val, a.property⟩ : Z))
    intro a b h
    have hab : a.val.val = b.val.val := congrArg (fun z : Z => z.val) h
    exact Subtype.ext (Subtype.ext hab)
  have habCard : Nat.card (L ⧸ commutator L) ≤ 2 :=
    (central_lift_derived_quotient_card_le_kernel f hsurj).trans
      (hkernelCard.trans hZcard)
  let V : Subgroup L := U.subgroupOf L
  let p := (QuotientGroup.mk' (commutator L)).domRestrict V
  have hVcard : Nat.card V = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv
  have hpker : p.ker ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective p := by
      intro a b hab
      have hmem : a⁻¹ * b ∈ p.ker := by
        change p (a⁻¹ * b) = 1
        rw [map_mul, map_inv, hab, inv_mul_cancel]
      have hone : a⁻¹ * b = 1 := Subgroup.mem_bot.mp (hbot ▸ hmem)
      exact inv_mul_eq_one.mp hone
    have hVle := (Nat.card_le_card_of_injective p hinj).trans habCard
    rw [hVcard] at hVle
    omega
  obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hpker
  let a : G := u.val.val.val
  have haU : a ∈ U := u.val.property
  have hane : a ≠ 1 := by
    intro h
    exact hune (Subtype.ext (Subtype.ext (Subtype.ext h)))
  let K : Subgroup G := (commutator L).map L.subtype
  let : (commutator L).Characteristic := by
    change (derivedSeries L 1).Characteristic
    infer_instance
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  have haK : a ∈ K := by
    apply Subgroup.mem_map.mpr
    refine ⟨u.val.val, ?_, rfl⟩
    exact (QuotientGroup.eq_one_iff u.val.val).mp u.property
  have haD : a ∈ conjugateInvolutions U :=
    Group.subset_conjugatesOfSet ⟨haU, by simpa only [Set.mem_singleton_iff] using hane⟩
  have hdisconnected := conjugateCommutingGraph_not_preconnected
    T U hUT hUbot hUel hclosed hTI hnormalU
  have hDK : conjugateInvolutions U ⊆ (K : Set G) := by
    intro b hb
    have hconj := NormalGraph.conjugacy_transitive (conjugateInvolutions U)
      (fun b hb => conjugateInvolutions_order_two U hUel hb)
      (fun b hb g => conjugateInvolutions_conj_mem U hb g)
      (fun b hb c hc hne hcomm =>
        conjugateInvolutions_mul_mem T U hUT hUel hclosed hTI hb hc hne hcomm)
      hdisconnected ⟨a, haD⟩ ⟨b, hb⟩
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    exact (inferInstance : K.Normal).conj_mem a haK g
  have hLK : L ≤ K := by
    change Subgroup.normalClosure (U : Set G) ≤ K
    rw [← closure_conjugateInvolutions_eq_normalClosure U]
    exact (Subgroup.closure_le K).2 hDK
  apply Group.IsPerfect.mk
  apply top_unique
  intro l _
  obtain ⟨k, hk, heq⟩ := Subgroup.mem_map.mp (hLK l.property)
  exact (Subtype.ext heq) ▸ hk

theorem central_lift_hull_structure (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (hZcard : Nat.card Z ≤ 2)
    (himage : IsQuasisimple
      ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' Z)))
    (hmodel : fusionIsBenderGroup
      (((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' Z)) ⧸
        Subgroup.center ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' Z)))) :
    let L := Subgroup.normalClosure (U : Set G)
    let Q := L.map (QuotientGroup.mk' Z)
    L.Normal ∧ Group.IsPerfect L ∧ IsQuasisimple L ∧
      (Z.subgroupOf L ≤ Subgroup.center L) ∧
      ((QuotientGroup.mk' Z).subgroupMap L).ker = Z.subgroupOf L ∧
      Nonempty ((L ⧸ Subgroup.center L) ≃* (Q ⧸ Subgroup.center Q)) ∧
      fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
  let L := Subgroup.normalClosure (U : Set G)
  let Q := L.map (QuotientGroup.mk' Z)
  let f := (QuotientGroup.mk' Z).subgroupMap L
  let : Group.IsPerfect L :=
    central_lift_hull_perfect T U hUT hUel hcard hclosed hTI Z hZ hZcard himage
  have hker : f.ker = Z.subgroupOf L := by
    rw [central_lift_subgroup_map_kernel]
    simp only [QuotientGroup.ker_mk']
  have hcentral : Z.subgroupOf L ≤ Subgroup.center L := by
    intro a ha
    apply Subgroup.mem_center_iff.mpr
    intro b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hZ ha)) b.val)
  have hfcentral : f.ker ≤ Subgroup.center L := hker ▸ hcentral
  have hsurj := (QuotientGroup.mk' Z).subgroupMap_surjective L
  let e := centralLiftCenterQuotientEquiv f hsurj hfcentral
  refine ⟨inferInstance, inferInstance,
    CFSG.ComponentClassification.CentralExtensions.quasisimple_of_surjective
      himage f hsurj hfcentral, hcentral, hker, ⟨e⟩, ?_⟩
  exact central_lift_model_transport e hmodel

theorem central_involution_hull_structure (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (x : Subgroup.center G) (horder : orderOf (x : G) = 2)
    (himage : IsQuasisimple
      ((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))))
    (hmodel : fusionIsBenderGroup
      (((Subgroup.normalClosure (U : Set G)).map (QuotientGroup.mk' (centralLiftKernel x))) ⧸
        Subgroup.center ((Subgroup.normalClosure (U : Set G)).map
          (QuotientGroup.mk' (centralLiftKernel x))))) :
    let L := Subgroup.normalClosure (U : Set G)
    let Q := L.map (QuotientGroup.mk' (centralLiftKernel x))
    L.Normal ∧ Group.IsPerfect L ∧ IsQuasisimple L ∧
      ((centralLiftKernel x).subgroupOf L ≤ Subgroup.center L) ∧
      ((QuotientGroup.mk' (centralLiftKernel x)).subgroupMap L).ker =
        (centralLiftKernel x).subgroupOf L ∧
      Nonempty ((L ⧸ Subgroup.center L) ≃* (Q ⧸ Subgroup.center Q)) ∧
      fusionIsBenderGroup (L ⧸ Subgroup.center L) := by
  exact central_lift_hull_structure T U hUT hUel hcard hclosed hTI (centralLiftKernel x)
    (centralLiftKernel_le_center x) (le_of_eq (centralLiftKernel_card_two x horder))
    himage hmodel

end CFSG.ShultStronglyClosedTI
