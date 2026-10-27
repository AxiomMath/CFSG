module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerQuotient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientStrongClosure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem ti_central_quotient_injective_on_vertices (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    Set.InjOn (QuotientGroup.mk' Z) (conjugateInvolutions U) :=
  NormalGraph.quotient_injective_on_vertices (conjugateInvolutions U)
    (fun _ hx => conjugateInvolutions_order_two U hUel hx)
    (fun _ hx _ hy hne hc => conjugateInvolutions_mul_mem T U hUT hUel hclosed hTI
      hx hy hne hc)
    (conjugateCommutingGraph_not_preconnected T U hUT hU hUel hclosed hTI hnormal) Z hZ

theorem ti_subgroup_inf_central_eq_bot (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) : U ⊓ Z = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro a ⟨haU, haZ⟩
  by_contra hane
  have haD : a ∈ conjugateInvolutions U :=
    Group.subset_conjugatesOfSet ⟨haU, by simpa only [Set.mem_singleton_iff] using hane⟩
  exact NormalGraph.no_central_vertex (conjugateInvolutions U)
    (fun _ hx => conjugateInvolutions_order_two U hUel hx)
    (conjugateCommutingGraph_not_preconnected T U hUT hU hUel hclosed hTI hnormal)
    haD (hZ haZ)

theorem ti_central_quotient_injective_on_subgroup (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    Set.InjOn (QuotientGroup.mk' Z) (U : Set G) := by
  apply quotient_injective_on_subgroup U Z ?_
    (ti_subgroup_inf_central_eq_bot T U hUT hU hUel hclosed hTI hnormal Z hZ)
  intro a ha b hb hab
  exact ti_central_quotient_injective_on_vertices T U hUT hU hUel hclosed hTI hnormal Z hZ
    (Group.subset_conjugatesOfSet ha) (Group.subset_conjugatesOfSet hb) hab

@[expose] def tiCentralQuotientSubgroupEquiv (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    U ≃* U.map (QuotientGroup.mk' Z) := by
  let f := (QuotientGroup.mk' Z).subgroupMap U
  apply MulEquiv.ofBijective f
  constructor
  · intro a b hab
    exact Subtype.ext (ti_central_quotient_injective_on_subgroup T U hUT hU hUel
      hclosed hTI hnormal Z hZ a.property b.property (congrArg Subtype.val hab))
  · rintro ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨a, ha⟩, rfl⟩

theorem tiCentralQuotientSubgroupEquiv_apply (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (a : U) :
    (tiCentralQuotientSubgroupEquiv T U hUT hU hUel hclosed hTI hnormal Z hZ a : G ⧸ Z) =
      (QuotientGroup.mk' Z) (a : G) := rfl

theorem ti_central_quotient_conjugate_eq_iff (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (g : G) :
    (U.map (QuotientGroup.mk' Z)).map
        (MulAut.conj ((QuotientGroup.mk' Z) g)).toMonoidHom = U.map (QuotientGroup.mk' Z) ↔
      U.map (MulAut.conj g).toMonoidHom = U := by
  let π := QuotientGroup.mk' Z
  have hinj := ti_central_quotient_injective_on_vertices T U hUT hU hUel hclosed hTI
    hnormal Z hZ
  have horder := NormalGraph.quotient_vertices_order_two (conjugateInvolutions U)
    (fun _ hx => conjugateInvolutions_order_two U hUel hx)
    (conjugateCommutingGraph_not_preconnected T U hUT hU hUel hclosed hTI hnormal) Z hZ
  rw [← map_conj_natural U π g]
  constructor
  · intro heq
    have hreflect : ∀ {a b : G}, a ∈ conjugateInvolutions U → b ∈ U →
        π a = π b → a = b := by
      intro a b ha hb hab
      have hbne : b ≠ 1 := by
        intro hone
        have haorder := horder (π a) ⟨a, ha, rfl⟩
        rw [hab, hone, map_one, orderOf_one] at haorder
        omega
      exact hinj ha (Group.subset_conjugatesOfSet
        ⟨hb, by simpa only [Set.mem_singleton_iff] using hbne⟩) hab
    apply le_antisymm
    · intro a ha
      by_cases haone : a = 1
      · exact haone ▸ U.one_mem
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp ha
      have hbne : b ≠ 1 := by
        intro hone
        exact haone (hba.symm.trans (by simp only [hone, map_one]))
      have haD : a ∈ conjugateInvolutions U := by
        rw [← hba]
        exact conjugateInvolutions_conj_mem U (Group.subset_conjugatesOfSet
          ⟨hb, by simpa only [Set.mem_singleton_iff] using hbne⟩) g
      have haq : π a ∈ U.map π := heq ▸ Subgroup.mem_map_of_mem π ha
      obtain ⟨c, hc, hca⟩ := Subgroup.mem_map.mp haq
      exact (hreflect haD hc hca.symm) ▸ hc
    · intro a ha
      by_cases haone : a = 1
      · exact haone ▸ (U.map (MulAut.conj g).toMonoidHom).one_mem
      have haq : π a ∈ (U.map (MulAut.conj g).toMonoidHom).map π :=
        heq.symm ▸ Subgroup.mem_map_of_mem π ha
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp haq
      obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
      have hbne : b ≠ 1 := by
        intro hone
        have haD : a ∈ conjugateInvolutions U := Group.subset_conjugatesOfSet
          ⟨ha, by simpa only [Set.mem_singleton_iff] using haone⟩
        have haorder := horder (π a) ⟨a, haD, rfl⟩
        rw [← hba, hone, map_one, orderOf_one] at haorder
        omega
      have hcne : c ≠ 1 := by
        intro hone
        exact hbne (hcb.symm.trans (by simp only [hone, map_one]))
      have hbD : b ∈ conjugateInvolutions U := by
        rw [← hcb]
        exact conjugateInvolutions_conj_mem U (Group.subset_conjugatesOfSet
          ⟨hc, by simpa only [Set.mem_singleton_iff] using hcne⟩) g
      exact (hreflect hbD ha hba) ▸ hb
  · intro heq
    rw [heq]

theorem ti_central_quotient_normalizer_preimage (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    (Subgroup.normalizer (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
      (QuotientGroup.mk' Z) = Subgroup.normalizer (U : Set G) := by
  ext g
  change (QuotientGroup.mk' Z) g ∈ Subgroup.normalizer
    (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) ↔ g ∈ Subgroup.normalizer (U : Set G)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.mem_normalizer_iff_map_conj_eq]
  exact ti_central_quotient_conjugate_eq_iff T U hUT hU hUel hclosed hTI hnormal Z hZ g

theorem ti_central_quotient_not_normal (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    ¬ (U.map (QuotientGroup.mk' Z)).Normal := by
  intro hnormalImage
  have hpre := ti_central_quotient_normalizer_preimage T U hUT hU hUel hclosed hTI
    hnormal Z hZ
  rw [Subgroup.normalizer_eq_top_iff.mpr hnormalImage, Subgroup.comap_top] at hpre
  exact hnormal (Subgroup.normalizer_eq_top_iff.mp hpre.symm)

theorem ti_central_quotient_TI (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    fusionIsTI (U.map (QuotientGroup.mk' Z)) := by
  let π := QuotientGroup.mk' Z
  have hinj := ti_central_quotient_injective_on_vertices T U hUT hU hUel hclosed hTI
    hnormal Z hZ
  intro y hne
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
  have hconj : U.map (MulAut.conj g).toMonoidHom ≠ U := by
    intro heq
    exact hne ((ti_central_quotient_conjugate_eq_iff T U hUT hU hUel hclosed hTI
      hnormal Z hZ g).mpr heq)
  apply le_antisymm ?_ bot_le
  rintro q ⟨hqU, hqconj⟩
  apply Subgroup.mem_bot.mpr
  by_contra hqne
  obtain ⟨a, ha, haq⟩ := Subgroup.mem_map.mp hqU
  obtain ⟨b, hb, hbq⟩ := Subgroup.mem_map.mp hqconj
  obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp hb
  change π c = b at hcb
  have hane : a ≠ 1 := by
    intro hone
    exact hqne (haq.symm.trans (by simp only [hone, map_one]))
  have hcne : c ≠ 1 := by
    intro hone
    have hbone : b = 1 := hcb.symm.trans (by simp only [hone, map_one])
    exact hqne (hbq.symm.trans (by simp only [hbone, map_one]))
  have haD : a ∈ conjugateInvolutions U := Group.subset_conjugatesOfSet
    ⟨ha, by simpa only [Set.mem_singleton_iff] using hane⟩
  have hcD : c ∈ conjugateInvolutions U := Group.subset_conjugatesOfSet
    ⟨hc, by simpa only [Set.mem_singleton_iff] using hcne⟩
  have heq : π a = π ((MulAut.conj g) c) := by
    calc
      π a = q := haq
      _ = (MulAut.conj (π g)) b := hbq.symm
      _ = π ((MulAut.conj g) c) := by
        rw [← hcb]
        simp only [MulAut.conj_apply, map_mul, map_inv]
  have hactual : a = (MulAut.conj g) c :=
    hinj haD (conjugateInvolutions_conj_mem U hcD g) heq
  have haconj : a ∈ U.map (MulAut.conj g).toMonoidHom :=
    hactual.symm ▸ Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hc
  exact hane (Subgroup.mem_bot.mp ((hTI g hconj) ▸
    (show a ∈ U ⊓ U.map (MulAut.conj g).toMonoidHom from ⟨ha, haconj⟩)))

theorem central_involution_quotient_card_lt (x : Subgroup.center G)
    (horder : orderOf (x : G) = 2) :
    Nat.card (G ⧸ centralLiftKernel x) < Nat.card G := by
  have hcard := (centralLiftKernel x).card_eq_card_quotient_mul_card_subgroup
  rw [centralLiftKernel_card_two x horder] at hcard
  have hpos : 0 < Nat.card (G ⧸ centralLiftKernel x) := Nat.card_pos
  omega

theorem central_involution_quotient_datum (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hU : U ≠ ⊥) (hUel : IsElemAbelian 2 U)
    (hcard : 4 ≤ Nat.card U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G))
    (hTI : fusionIsTI U) (hnormal : ¬ U.Normal)
    (x : Subgroup.center G) (horder : orderOf (x : G) = 2) :
    let Z := centralLiftKernel x
    let π := QuotientGroup.mk' Z
    let V := U.map π
    let L := Subgroup.normalClosure (U : Set G)
    let K := Subgroup.normalClosure (V : Set (G ⧸ Z))
    ∃ e : U ≃* V,
      (∀ a : U, (e a : G ⧸ Z) = π (a : G)) ∧
      V ≤ (T.mapSurjective (QuotientGroup.mk'_surjective Z) : Subgroup (G ⧸ Z)) ∧
      V ≠ ⊥ ∧ IsElemAbelian 2 V ∧ Nat.card V = Nat.card U ∧ 4 ≤ Nat.card V ∧
      fusionStronglyClosed (V : Set (G ⧸ Z))
        (T.mapSurjective (QuotientGroup.mk'_surjective Z) : Subgroup (G ⧸ Z)) ∧
      fusionIsTI V ∧ ¬ V.Normal ∧ K = L.map π ∧
      (Subgroup.normalizer (V : Set (G ⧸ Z))).comap π = Subgroup.normalizer (U : Set G) ∧
      U ⊓ Z = ⊥ ∧ Nat.card (G ⧸ Z) < Nat.card G := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := centralLiftKernel x
  let π := QuotientGroup.mk' Z
  let e := tiCentralQuotientSubgroupEquiv T U hUT hU hUel hclosed hTI hnormal Z
    (centralLiftKernel_le_center x)
  have hcardImage : Nat.card (U.map π) = Nat.card U := (Nat.card_congr e.toEquiv).symm
  have hnotnormal := ti_central_quotient_not_normal T U hUT hU hUel hclosed hTI
    hnormal Z (centralLiftKernel_le_center x)
  have hne : U.map π ≠ ⊥ := by
    intro hbot
    exact hnotnormal (hbot ▸ inferInstance)
  refine ⟨e, fun _ => rfl, ?_, hne,
    CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map U hUel π,
    hcardImage, hcardImage.symm ▸ hcard, ?_, ?_, hnotnormal, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.map_mono hUT
  · exact stronglyClosed_map_surjective π (QuotientGroup.mk'_surjective Z) T U hUT hclosed
  · exact ti_central_quotient_TI T U hUT hU hUel hclosed hTI hnormal Z
      (centralLiftKernel_le_center x)
  · exact (Subgroup.map_normalClosure (U : Set G) π
      (QuotientGroup.mk'_surjective Z)).symm
  · exact ti_central_quotient_normalizer_preimage T U hUT hU hUel hclosed hTI hnormal Z
      (centralLiftKernel_le_center x)
  · exact ti_subgroup_inf_central_eq_bot T U hUT hU hUel hclosed hTI hnormal Z
      (centralLiftKernel_le_center x)
  · exact central_involution_quotient_card_lt x horder

end CFSG.ShultStronglyClosedTI
