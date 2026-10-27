module

public import CFSG.Monster.B.TwoA.Fischer.Socle
public import CFSG.Monster.B.Generic.AffineObstruction

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix MulAction
open scoped Pointwise

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem closure_preimage_coe_eq_subgroupOf {G : Type*} [Group G] (K : Subgroup G) {s : Set G}
    (hs : s ⊆ K) :
    Subgroup.closure (((↑) : K → G) ⁻¹' s) = (Subgroup.closure s).subgroupOf K := by
  apply Subgroup.map_injective K.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.subgroupOf_map_subtype, Subgroup.coe_subtype,
    Set.image_preimage_eq_of_subset fun x hx => ⟨⟨x, hs hx⟩, rfl⟩,
    inf_eq_left.2 ((Subgroup.closure_le K).2 hs)]

theorem orderOf_two_zmod_eleven : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem carrier_conjClasses_mk {u : V} (hu : u ∈ Y) :
    (ConjClasses.mk (⟨lab u, lab_mem_sliceGroup hu⟩ : sliceGroup lab Y)).carrier =
      {g : sliceGroup lab Y | (g : S) ∈ lab '' Y} := by
  ext g
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨act ((c : S)⁻¹) u, hS.mapsTo _ ((sliceGroup lab Y).inv_mem c.2) u hu, ?_⟩
    have h1 : (c : S) * g * (c : S)⁻¹ = lab u := congrArg Subtype.val hc
    rw [hS.lab_act, ← h1]
    group
  · rintro ⟨y, hy, hgy⟩
    obtain ⟨b, hb, hbu⟩ := hS.transitive u hu y hy
    refine ⟨(⟨b, hb⟩ : sliceGroup lab Y)⁻¹, Subtype.ext ?_⟩
    change b⁻¹ * (g : S) * b⁻¹⁻¹ = lab u
    rw [← hgy, ← hbu, hS.lab_act]
    group

omit hS in
theorem closure_labels_eq_top :
    Subgroup.closure {g : sliceGroup lab Y | (g : S) ∈ lab '' Y} = ⊤ :=
  Subgroup.closure_closure_coe_preimage

abbrev labelsIn (C : Set V) : Set (sliceGroup lab Y) := {g | (g : S) ∈ lab '' C}

omit hS in
theorem closure_labelsIn {C : Set V} (hCY : C ⊆ Y) :
    Subgroup.closure (labelsIn (lab := lab) (Y := Y) C) =
      (Subgroup.closure (lab '' C)).subgroupOf (sliceGroup lab Y) :=
  closure_preimage_coe_eq_subgroupOf _ fun _ ⟨_, hz, hzx⟩ => hzx ▸ lab_mem_sliceGroup (hCY hz)

theorem toConjAct_mem_stabilizer {C : Set V} (g : setStab act lab Y C) :
    ConjAct.toConjAct (⟨g, g.2.1⟩ : sliceGroup lab Y) ∈
      stabilizer (ConjAct (sliceGroup lab Y)) (labelsIn (lab := lab) (Y := Y) C) := by
  rw [mem_stabilizer_iff]
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul]
  change ((g : S)⁻¹ * (x : S) * (g : S)⁻¹⁻¹ ∈ lab '' C) ↔ (x : S) ∈ lab '' C
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨act (g : S) z, (g.2.2 z).2 hz, ?_⟩
    rw [hS.lab_act, hzx]
    group
  · rintro ⟨z, hz, hzx⟩
    refine ⟨act ((g : S)⁻¹) z, (g.2.2 _).1 (by rw [act_act_inv]; exact hz), ?_⟩
    rw [hS.lab_act, hzx]

@[expose] def labelsInEquiv {C : Set V} (hCY : C ⊆ Y) : C ≃ labelsIn (lab := lab) (Y := Y) C :=
  Equiv.ofBijective (fun z => ⟨⟨lab z, lab_mem_sliceGroup (hCY z.2)⟩, z, z.2, rfl⟩)
    ⟨fun z z' h => Subtype.ext (hS.injOn (hCY z.2) (hCY z'.2)
      (congrArg (fun c : labelsIn (lab := lab) (Y := Y) C => ((c : sliceGroup lab Y) : S)) h)),
    fun c => by
      obtain ⟨z, hz, hzc⟩ := c.2
      exact ⟨⟨z, hz⟩, Subtype.ext (Subtype.ext hzc)⟩⟩

theorem coe_labelsInEquiv {C : Set V} (hCY : C ⊆ Y) (z : C) :
    (((hS.labelsInEquiv hCY z : labelsIn (lab := lab) (Y := Y) C) : sliceGroup lab Y) : S) =
      lab z :=
  rfl

theorem dvd_card_range_toPermHom {C : Set V} (hCY : C ⊆ Y) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓC : ℓ ∣ Nat.card (setStabPerm act lab Y C).range) :
    ℓ ∣ Nat.card (MulAction.toPermHom (stabilizer (ConjAct (sliceGroup lab Y))
      (labelsIn (lab := lab) (Y := Y) C)) (labelsIn (lab := lab) (Y := Y) C)).range := by
  have := Fact.mk hℓ
  have : Finite C := (hS.finite.subset hCY).to_subtype
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' ℓ hℓC
  obtain ⟨g, hg⟩ := σ.2
  let e := hS.labelsInEquiv hCY
  let f : stabilizer (ConjAct (sliceGroup lab Y)) (labelsIn (lab := lab) (Y := Y) C) :=
    ⟨_, hS.toConjAct_mem_stabilizer g⟩
  have hf : MulAction.toPermHom _ _ f = e.permCongrHom (setStabPerm act lab Y C g) := by
    ext c
    obtain ⟨z, rfl⟩ := e.surjective c
    rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change ((ConjAct.toConjAct (⟨g, g.2.1⟩ : sliceGroup lab Y) • (e z : sliceGroup lab Y) :
      sliceGroup lab Y) : S) = lab (act (g : S) z)
    rw [ConjAct.toConjAct_smul, hS.lab_act]
    rfl
  have hord : orderOf (MulAction.toPermHom (stabilizer (ConjAct (sliceGroup lab Y))
      (labelsIn (lab := lab) (Y := Y) C)) (labelsIn (lab := lab) (Y := Y) C) f) = ℓ := by
    rw [hf, MulEquiv.orderOf_eq, hg, Subgroup.orderOf_coe, hσ]
  rw [← hord, ← Subgroup.orderOf_mk _ (MonoidHom.mem_range.2 ⟨f, rfl⟩)]
  exact orderOf_dvd_natCard _

theorem commutator_eq_top_of_clique {C : Set V} (hCY : C ⊆ Y) (hCne : C.Nonempty)
    (hA : CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)))
    (hAcard : Nat.card (Subgroup.closure (lab '' C)) = 2 ^ 10)
    (h11 : 11 ∣ Nat.card (setStabPerm act lab Y C).range) :
    commutator (sliceGroup lab Y) = ⊤ := by
  have := hS.finite_sliceGroup
  have := Fact.mk Nat.prime_two
  obtain ⟨u, hu⟩ := hCne
  have hcar := hS.carrier_conjClasses_mk (hCY hu)
  have hle : Subgroup.closure (lab '' C) ≤ sliceGroup lab Y :=
    Subgroup.closure_mono (Set.image_mono hCY)
  have hA' : CFSG.IsElementaryAbelian 2 (Subgroup.closure (labelsIn (lab := lab) (Y := Y) C)) := by
    rw [closure_labelsIn hCY]
    exact CFSG.IsElementaryAbelian.subgroupOf hle
  have hAcard' : Nat.card (Subgroup.closure (labelsIn (lab := lab) (Y := Y) C)) = 2 ^ 10 := by
    rw [closure_labelsIn hCY, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hAcard]
  rw [← Group.isPerfect_def]
  refine CFSG.Monster.B.Generic.conjugate_involution_affine_obstruction
    (ConjClasses.mk (⟨lab u, lab_mem_sliceGroup (hCY hu)⟩ : sliceGroup lab Y)) ?_ ?_
    (labelsIn (lab := lab) (Y := Y) C) ?_ ⟨⟨lab u, lab_mem_sliceGroup (hCY hu)⟩, u, hu, rfl⟩ 10
    hA' hAcard' 11 (by norm_num) (by norm_num) (hS.dvd_card_range_toPermHom hCY (by norm_num) h11)
    (by rw [orderOf_two_zmod_eleven]; norm_num)
  · rw [hcar]
    rintro x ⟨y, hy, hyx⟩
    rw [← Subgroup.orderOf_coe, ← hyx, hS.orderOf_lab y hy]
  · rw [hcar]
    exact closure_labels_eq_top
  · rw [hcar]
    rintro x ⟨z, hz, hzx⟩
    exact ⟨z, hCY hz, hzx⟩

theorem lab_sq {y : V} (hy : y ∈ Y) : lab y ^ 2 = 1 := by
  rw [← hS.orderOf_lab y hy]
  exact pow_orderOf_eq_one _

theorem orderOf_lab_mul_mem {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) :
    orderOf (lab y * lab z) ∈ ({1, 2, 3} : Finset ℕ) := by
  by_cases hc : Commute (lab y) (lab z)
  · have h2 : (lab y * lab z) ^ 2 = 1 := by
      rw [hc.mul_pow, hS.lab_sq hy, hS.lab_sq hz, one_mul]
    have hd := orderOf_dvd_of_pow_eq_one h2
    have hle := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : orderOf (lab y * lab z) <;> simp_all
  · rw [hS.orderOf_mul y hy z hz hc]
    simp

theorem orderOf_lab_mul_eq_two_iff {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) (hyz : y ≠ z) :
    orderOf (lab y * lab z) = 2 ↔ (sliceGraph lab Y).Adj y z := by
  constructor
  · intro h
    by_contra hadj
    have hc : ¬Commute (lab y) (lab z) := fun hc => hadj ⟨hy, hz, hyz, hc⟩
    rw [hS.orderOf_mul y hy z hz hc] at h
    omega
  · intro hadj
    refine orderOf_eq_prime ?_ ?_
    · rw [hadj.2.2.2.mul_pow, hS.lab_sq hy, hS.lab_sq hz, one_mul]
    · intro h1
      have hzy : lab z = lab y := by
        have h2 : (lab y)⁻¹ = lab y := inv_eq_self_of_orderOf_eq_two (hS.orderOf_lab y hy)
        rw [← h2]
        exact (inv_eq_of_mul_eq_one_right h1).symm
      exact hyz (hS.injOn hy hz hzy.symm)

omit hS in
@[expose] def induceNeighborSetEquiv (y : Y) :
    ((sliceGraph lab Y).induce Y).neighborSet y ≃ (sliceGraph lab Y).neighborSet y where
  toFun z := ⟨z.1.1, z.2⟩
  invFun z := ⟨⟨z.1, mem_of_mem_neighborSet z.2⟩, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit hS in
@[expose] def induceCommonNeighborsEquiv (y z : Y) :
    ((sliceGraph lab Y).induce Y).commonNeighbors y z ≃
      (sliceGraph lab Y).commonNeighbors y z where
  toFun w := ⟨w.1.1, w.2⟩
  invFun w := ⟨⟨w.1, ((sliceGraph lab Y).mem_commonNeighbors.1 w.2).1.2.1⟩, w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem isSRGWith [Fintype Y] [DecidableRel ((sliceGraph lab Y).induce Y).Adj] :
    ((sliceGraph lab Y).induce Y).IsSRGWith 3510 693 180 126 where
  card := by rw [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, hS.ncard]
  regular y := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card,
      Nat.card_congr (induceNeighborSetEquiv (lab := lab) y), Nat.card_coe_set_eq, hS.valency y y.2]
  of_adj y z h := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (induceCommonNeighborsEquiv (lab := lab) y z),
      Nat.card_coe_set_eq, hS.lambda y z h]
  of_not_adj y z hyz h := by
    rw [Fintype.card_eq_nat_card, Nat.card_congr (induceCommonNeighborsEquiv (lab := lab) y z),
      Nat.card_coe_set_eq, hS.mu y y.2 z z.2 (fun e => hyz (Subtype.ext e)) h]

theorem simple_of_clique (hC : ∃ C ⊆ Y, C.Nonempty ∧
      CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C)) ∧
      Nat.card (Subgroup.closure (lab '' C)) = 2 ^ 10 ∧
      11 ∣ Nat.card (setStabPerm act lab Y C).range) :
    IsSimpleGroup (sliceGroup lab Y) ∧ ¬ IsMulCommutative (sliceGroup lab Y) ∧
    Nat.card (sliceGroup lab Y) = 64561751654400 ∧
    commutator (sliceGroup lab Y) = ⊤ ∧
    (∃ D : ConjClasses (sliceGroup lab Y),
      D.carrier = {g : sliceGroup lab Y | (g : S) ∈ lab '' Y}) ∧
    (lab '' Y).ncard = 3510 ∧
    (∀ y ∈ Y, orderOf (lab y) = 2) ∧
    Subgroup.closure {g : sliceGroup lab Y | (g : S) ∈ lab '' Y} = ⊤ ∧
    (∀ y ∈ Y, ∀ z ∈ Y, orderOf (lab y * lab z) ∈ ({1, 2, 3} : Finset ℕ)) ∧
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → (orderOf (lab y * lab z) = 2 ↔ (sliceGraph lab Y).Adj y z)) ∧
    ∀ [Fintype Y] [DecidableRel ((sliceGraph lab Y).induce Y).Adj],
      ((sliceGraph lab Y).induce Y).IsSRGWith 3510 693 180 126 := by
  obtain ⟨C, hCY, hCne, hA, hAcard, h11⟩ := hC
  obtain ⟨u, hu⟩ := hCne
  have hperf := hS.commutator_eq_top_of_clique hCY ⟨u, hu⟩ hA hAcard h11
  obtain ⟨hsimp, hnc, -⟩ := hS.simple_derived_socle
  have e : sliceGroup lab Y ≃* commutator (sliceGroup lab Y) :=
    ((MulEquiv.subgroupCongr hperf).trans Subgroup.topEquiv).symm
  refine ⟨e.isSimpleGroup, fun hcomm => hnc ⟨⟨fun a b => Subtype.ext
      (mul_comm' (a : sliceGroup lab Y) (b : sliceGroup lab Y))⟩⟩,
    hS.card_sliceGroup, hperf, ⟨_, hS.carrier_conjClasses_mk (hCY hu)⟩,
    by rw [hS.injOn.ncard_image, hS.ncard], hS.orderOf_lab,
    closure_labels_eq_top, fun y hy z hz => hS.orderOf_lab_mul_mem hy hz,
    fun y hy z hz hyz => hS.orderOf_lab_mul_eq_two_iff hy hz hyz, hS.isSRGWith⟩

theorem exists_isSliceMaxClique : ∃ C : Set V, IsSliceMaxClique lab Y C := by
  obtain ⟨u, hu⟩ : Y.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hS.ncard]; norm_num)
  have hfin : {D : Set V | D ⊆ Y ∧ (sliceGraph lab Y).IsClique D}.Finite :=
    hS.finite.finite_subsets.subset fun _ hD => hD.1
  obtain ⟨C, hC⟩ := hfin.exists_maximal ⟨{u}, Set.singleton_subset_iff.2 hu,
    Set.pairwise_singleton _ _⟩
  exact ⟨C, hC⟩

theorem simple :
    IsSimpleGroup (sliceGroup lab Y) ∧ ¬ IsMulCommutative (sliceGroup lab Y) ∧
    Nat.card (sliceGroup lab Y) = 64561751654400 ∧
    commutator (sliceGroup lab Y) = ⊤ ∧
    (∃ D : ConjClasses (sliceGroup lab Y),
      D.carrier = {g : sliceGroup lab Y | (g : S) ∈ lab '' Y}) ∧
    (lab '' Y).ncard = 3510 ∧
    (∀ y ∈ Y, orderOf (lab y) = 2) ∧
    Subgroup.closure {g : sliceGroup lab Y | (g : S) ∈ lab '' Y} = ⊤ ∧
    (∀ y ∈ Y, ∀ z ∈ Y, orderOf (lab y * lab z) ∈ ({1, 2, 3} : Finset ℕ)) ∧
    (∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → (orderOf (lab y * lab z) = 2 ↔ (sliceGraph lab Y).Adj y z)) ∧
    ∀ [Fintype Y] [DecidableRel ((sliceGraph lab Y).induce Y).Adj],
      ((sliceGraph lab Y).induce Y).IsSRGWith 3510 693 180 126 := by
  obtain ⟨C, hC⟩ := hS.exists_isSliceMaxClique
  obtain ⟨-, -, hK⟩ := hS.maximal_clique_stabilizer_kernel
  obtain ⟨-, -, hcl, hA, hR, -, h11, -⟩ := hK C hC
  rw [hcl] at hA hR
  exact hS.simple_of_clique ⟨C, hC.1.1, hS.nonempty_of_isSliceMaxClique hC, hA, hR, h11⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
