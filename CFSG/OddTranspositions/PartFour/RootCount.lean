module

public import CFSG.OddTranspositions.PartFour.LineCount

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem ncard_blockImage_blockLine_diff_eq_one_of_eq_insert (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ Dalpha D hC.alpha)
    (hline : blockLine D hC.alpha β =
      insert hC.alpha ((fun x => cimg x β) '' (Malpha D hC.alpha : Set G))) :
    (blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha})).ncard = 1 := by
  have hβmem : β ∈ blockLine D hC.alpha β \ {hC.alpha} :=
    ⟨right_mem_blockLine hβ.1 hβ.2.1, by simpa using hβ.2.2.1⟩
  have hset : blockImage hC '' (blockLine D hC.alpha β \ {hC.alpha}) =
      {blockImage hC β} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro T ⟨γ, hγ, rfl⟩
      have hγline := hline ▸ hγ.1
      rcases Set.mem_insert_iff.mp hγline with hγα | horbit
      · exact absurd hγα hγ.2
      · obtain ⟨x, hx, hxβ⟩ := horbit
        rw [← hxβ, blockImage_cimg hC β hx]
        exact Set.mem_singleton _
    · rintro T rfl
      exact ⟨β, hβmem, rfl⟩
  rw [hset, Set.ncard_singleton]

private theorem rootCount_map_closure_subtype_eq (hC : HypothesisC D) {α' : Set G}
    (hα' : α' ∈ Dalpha D hC.alpha) :
    (Subgroup.closure {c : Halpha D hC.alpha | (c : G) ∈ α'}).map
        (Halpha D hC.alpha).subtype = Subgroup.closure α' := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact hc
  · intro hx
    exact ⟨⟨x, Subgroup.subset_closure (mem_DalphaStar_iff.mpr ⟨α', hα', hx⟩)⟩, hx, rfl⟩

private theorem rootCount_injective_mk_closure (hC : HypothesisC D) {α' : Set G}
    (hα' : α' ∈ Dalpha D hC.alpha)
    (hker : ∀ z ∈ Subgroup.closure α', z ∈ Malpha D hC.alpha → z = 1)
    {K : Subgroup (Halpha D hC.alpha)}
    (hK : K = Subgroup.closure {c : Halpha D hC.alpha | (c : G) ∈ α'}) :
    Function.Injective (fun k : K =>
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (k : Halpha D hC.alpha)) := by
  intro k1 k2 hEq
  apply Subtype.ext
  have hR : (k1 : Halpha D hC.alpha)⁻¹ * (k2 : Halpha D hC.alpha) ∈
      CFSG.solvableRadical (Halpha D hC.alpha) := (QuotientGroup.eq).mp hEq
  have hmK : (k1 : Halpha D hC.alpha)⁻¹ * (k2 : Halpha D hC.alpha) ∈ K :=
    K.mul_mem (K.inv_mem k1.2) k2.2
  have hcl : (((k1 : Halpha D hC.alpha)⁻¹ * (k2 : Halpha D hC.alpha) : Halpha D hC.alpha) : G) ∈
      Subgroup.closure α' := by
    rw [← rootCount_map_closure_subtype_eq hC hα', ← hK]
    exact Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype hmK
  have hM : (((k1 : Halpha D hC.alpha)⁻¹ * (k2 : Halpha D hC.alpha) : Halpha D hC.alpha) : G) ∈
      Malpha D hC.alpha :=
    Subgroup.mem_map_of_mem (Halpha D hC.alpha).subtype hR
  have hone : (((k1 : Halpha D hC.alpha)⁻¹ * (k2 : Halpha D hC.alpha) : Halpha D hC.alpha) : G) =
      1 := hker _ hcl hM
  exact inv_mul_eq_one.mp (Subtype.ext hone)

private theorem rootCount_card_insert_Vmem (hC : HypothesisC D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {V : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hV : V ⊆ imageClass hC)
    {R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hR₀ : (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
      insert 1 V) :
    Nat.card R₀ = V.ncard + 1 := by
  have h1not : (1 : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ∉ V := by
    intro h1
    have hmem : (1 : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ∈
        imageClass hC := hV h1
    have hord : orderOf (1 : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) =
        2 := imageClass_involutions hC hHns 1 hmem
    rw [orderOf_one] at hord
    exact absurd hord (by norm_num)
  rw [show Nat.card R₀ =
      (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))).ncard from
        Nat.card_coe_set_eq _,
    hR₀, Set.ncard_insert_of_notMem h1not (Set.toFinite _)]

private theorem rootCount_card_closure_le_card_root (hC : HypothesisC D)
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    {α' : Set G} (hα' : α' ∈ Dalpha D hC.alpha)
    (hker : ∀ z ∈ Subgroup.closure α', z ∈ Malpha D hC.alpha → z = 1)
    {V : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hV : V ⊆ imageClass hC) (hblockV : blockImage hC α' ⊆ V)
    (hVcard : V.ncard = α'.ncard)
    {R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hR₀ : (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
      insert 1 V) :
    Nat.card (Subgroup.closure α') ≤ V.ncard + 1 := by
  have hR₀card : Nat.card R₀ = V.ncard + 1 := rootCount_card_insert_Vmem hC hHns hV hR₀
  let K : Subgroup (Halpha D hC.alpha) :=
    Subgroup.closure {c : Halpha D hC.alpha | (c : G) ∈ α'}
  have hKmap : K.map (Halpha D hC.alpha).subtype = Subgroup.closure α' :=
    rootCount_map_closure_subtype_eq hC hα'
  have hKmapmk : K.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) ≤ R₀ := by
    change (Subgroup.closure {c : Halpha D hC.alpha | (c : G) ∈ α'}).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) ≤ R₀
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro y ⟨c, hc, rfl⟩
    have hcV : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) c ∈ V :=
      hblockV ⟨c, hc, rfl⟩
    rw [hR₀]
    exact Set.mem_insert_of_mem _ hcV
  let f : K → R₀ := fun k => ⟨QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
    (k : Halpha D hC.alpha), hKmapmk (Subgroup.mem_map_of_mem _ k.2)⟩
  have hfinj : Function.Injective f := by
    intro k1 k2 hEq
    exact rootCount_injective_mk_closure hC hα' hker rfl
      (by simpa only [f] using congrArg Subtype.val hEq)
  have hcardK : Nat.card (Subgroup.closure α') = Nat.card K := by
    rw [← hKmap, Subgroup.card_map_of_injective (Halpha D hC.alpha).subtype_injective]
  calc Nat.card (Subgroup.closure α') = Nat.card K := hcardK
    _ ≤ Nat.card R₀ := Nat.card_le_card_of_injective f hfinj
    _ = V.ncard + 1 := hR₀card

theorem card_closure_le_of_root (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hroot : ∀ x ∈ imageClass hC,
      ∃ R₀ : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
        (R₀ : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) =
          insert 1 (Vmem (imageClass hC) x))
    {α' : Set G} (hα' : α' ∈ Dalpha D hC.alpha)
    (hr1 : (blockImage hC '' (blockLine D hC.alpha α' \ {hC.alpha})).ncard = 1)
    (hker : ∀ z ∈ Subgroup.closure α', z ∈ Malpha D hC.alpha → z = 1) :
    Nat.card (Subgroup.closure α') ≤ α'.ncard + 1 := by
  obtain ⟨a', ha'⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hα'.1
  let b : Halpha D hC.alpha :=
    ⟨a', Subgroup.subset_closure (mem_DalphaStar_iff.mpr ⟨α', hα', ha'⟩)⟩
  have hblockV : blockImage hC α' ⊆
      Vmem (imageClass hC) (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b) :=
    blockImage_subset_Vmem h89 h113 hC hrad hW hn3 hMZ hα'
      (right_mem_blockLine hα'.1 hα'.2.1) hα'.2.2.1 ha'
  have hVcard := ncard_Vmem_eq h89 h113 hC hrad hW hn3 hMZ hHns hα' (b := b) ha'
  rw [hr1, one_mul] at hVcard
  obtain ⟨R₀, hR₀⟩ := hroot _ ⟨b, ⟨α', hα', ha'⟩, rfl⟩
  have hle := rootCount_card_closure_le_card_root hC hHns hα' hker
    (fun v hv => (mem_Vmem.mp hv).1) hblockV hVcard hR₀
  rwa [hVcard] at hle

end CFSG.OddTranspositions.PartFour
