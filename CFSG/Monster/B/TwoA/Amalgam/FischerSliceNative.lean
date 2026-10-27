module

public import CFSG.Monster.B.TwoA.Amalgam.ExactOrder
public import CFSG.Monster.B.TwoA.Fischer.Slice

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.Classical.UnitarySix (IsoPt ProjSU tPt projAct)

theorem cnGroup_eq_sliceGroup
    (v w : CVert) :
    cnGroup v w = Fischer.sliceGroup clabelS (cgraph.commonNeighbors v w) :=
  rfl

theorem clabelS_cvPerm
    (a : Shat) (x : CVert) : clabelS (cvPerm a x) = a * clabelS x * a⁻¹ := by
  rw [cvPerm_apply, clabelS_cvMul, inv_inv]

section Slice

variable {v w : CVert} (hw : w ∈ sphereThree v)
include hw

theorem adj_iff_commute_of_mem
    {y z : CVert} (hy : y ∈ cgraph.commonNeighbors v w)
    (hz : z ∈ cgraph.commonNeighbors v w) (hne : y ≠ z) :
    cgraph.Adj y z ↔ Commute (clabelS y) (clabelS z) := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ :=
    native_order_three_common_neighbor_three_transposition_group.choose_spec.2 v w hw
  exact h y hy z hz hne

theorem sliceGraph_adj_iff
    {y z : CVert} :
    (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).Adj y z ↔
      y ∈ cgraph.commonNeighbors v w ∧ z ∈ cgraph.commonNeighbors v w ∧ cgraph.Adj y z := by
  rw [Fischer.sliceGraph_adj]
  constructor
  · rintro ⟨hy, hz, hne, hc⟩
    exact ⟨hy, hz, (adj_iff_commute_of_mem hw hy hz hne).2 hc⟩
  · rintro ⟨hy, hz, ha⟩
    exact ⟨hy, hz, ha.ne, (adj_iff_commute_of_mem hw hy hz ha.ne).1 ha⟩

theorem sliceGraph_neighborSet
    {u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u =
      cgraph.neighborSet u ∩ cgraph.commonNeighbors v w := by
  ext z
  rw [SimpleGraph.mem_neighborSet, sliceGraph_adj_iff hw]
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hu, h.2, h.1⟩⟩

theorem sliceGraph_commonNeighbors
    {y z : CVert} (hy : y ∈ cgraph.commonNeighbors v w)
    (hz : z ∈ cgraph.commonNeighbors v w) :
    (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).commonNeighbors y z =
      Subtype.val '' ((cgraph.induce (cgraph.commonNeighbors v w)).commonNeighbors ⟨y, hy⟩
        ⟨z, hz⟩) := by
  ext x
  rw [SimpleGraph.mem_commonNeighbors, sliceGraph_adj_iff hw, sliceGraph_adj_iff hw]
  constructor
  · rintro ⟨⟨-, hx, h1⟩, -, -, h2⟩
    exact ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨⟨x, hx⟩, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨hy, hx, h1⟩, hz, hx, h2⟩

theorem ncard_sliceGraph_commonNeighbors
    {y z : CVert} (hy : y ∈ cgraph.commonNeighbors v w)
    (hz : z ∈ cgraph.commonNeighbors v w) :
    ((Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).commonNeighbors y z).ncard =
      Nat.card ((cgraph.induce (cgraph.commonNeighbors v w)).commonNeighbors ⟨y, hy⟩
        ⟨z, hz⟩) := by
  rw [sliceGraph_commonNeighbors hw hy hz, Set.ncard_image_of_injective _ Subtype.val_injective,
    Nat.card_coe_set_eq]

theorem sliceGraph_isClique_image_iff
    (D : Set (cgraph.commonNeighbors v w)) :
    (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).IsClique (Subtype.val '' D) ↔
      (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D := by
  constructor
  · intro h a ha b hb hab
    have h1 := h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ fun e => hab (Subtype.ext e)
    exact ((sliceGraph_adj_iff hw).1 h1).2.2
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact (sliceGraph_adj_iff hw).2 ⟨a.2, b.2, h ha hb fun e => hab (congrArg Subtype.val e)⟩

theorem isSliceMaxClique_image_iff
    (D : Set (cgraph.commonNeighbors v w)) :
    Fischer.IsSliceMaxClique clabelS (cgraph.commonNeighbors v w) (Subtype.val '' D) ↔
      Maximal (cgraph.induce (cgraph.commonNeighbors v w)).IsClique D := by
  rw [Fischer.IsSliceMaxClique]
  constructor
  · intro h
    refine ⟨(sliceGraph_isClique_image_iff hw D).1 h.1.2, fun D' hD' hle => ?_⟩
    have h2 := h.2 ⟨Subtype.coe_image_subset _ D', (sliceGraph_isClique_image_iff hw D').2 hD'⟩
      (Set.image_mono hle)
    exact (Set.image_subset_image_iff Subtype.val_injective).1 h2
  · intro h
    refine ⟨⟨Subtype.coe_image_subset _ D, (sliceGraph_isClique_image_iff hw D).2 h.1⟩,
      fun F hF hle => ?_⟩
    have hFe : F = Subtype.val '' (Subtype.val ⁻¹' F : Set (cgraph.commonNeighbors v w)) := by
      rw [Subtype.image_preimage_coe, Set.inter_eq_right.2 hF.1]
    rw [hFe] at hF hle ⊢
    have hD' := (sliceGraph_isClique_image_iff hw _).1 hF.2
    exact Set.image_mono (h.2 hD' ((Set.image_subset_image_iff Subtype.val_injective).1 hle))

omit hw in
theorem sliceStab_eq (u : CVert) :
    Fischer.sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u = cnGroup v w ⊓ vStab u := by
  ext a
  rw [Fischer.mem_sliceStab, Subgroup.mem_inf, mem_vStab, cvPerm_apply, ← cnGroup_eq_sliceGroup]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · conv_lhs => rw [← h]
    rw [cvMul_inv_cancel']
  · conv_lhs => rw [← h]
    rw [cvMul_inv_cancel]

theorem slice_local_unitary
    {u : CVert} (hu : u ∈ cgraph.commonNeighbors v w) :
    ∃ (τ : (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u ≃ IsoPt)
      (φ : Fischer.sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u →* ProjSU),
      Function.Surjective φ ∧
      (∀ a : Fischer.sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u,
        φ a = 1 ↔ (a : Shat) ∈ Subgroup.zpowers (clabelS u)) ∧
      (∀ (z : (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u)
        (a : Fischer.sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u),
        (a : Shat) = clabelS z → φ a = tPt (τ z)) ∧
      ∀ (a : Fischer.sliceStab cvPerm clabelS (cgraph.commonNeighbors v w) u)
        (z z' : (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u),
        (z' : CVert) = cvPerm (a : Shat) z → τ z' = projAct (φ a) (τ z) := by
  have hex := native_three_transposition_group_exact_order v w hw (nonempty_localHom v).some
  obtain ⟨-, -, -, -, hloc⟩ := hex
  have hloc' := hloc u hu
  obtain ⟨-, -, -, ⟨τ, φ, hφs, hφk, hφl, hφe⟩, -, -⟩ := hloc'
  have hns := sliceGraph_neighborSet hw hu
  let e := MulEquiv.subgroupCongr (sliceStab_eq (v := v) (w := w) u)
  have he : ∀ a, ((e a : (cnGroup v w ⊓ vStab u : Subgroup Shat)) : Shat) = a := fun a =>
    MulEquiv.subgroupCongr_apply _ a
  have hC : ∀ a, (φ.comp e.toMonoidHom) a = φ (e a) := fun a => rfl
  have hE : ∀ x : (Fischer.sliceGraph clabelS (cgraph.commonNeighbors v w)).neighborSet u,
      ((Set.equivOfEq hns).trans τ) x = τ ⟨x, hns.subset x.2⟩ := fun x => rfl
  refine ⟨(Set.equivOfEq hns).trans τ, φ.comp e.toMonoidHom, fun p => ?_, fun a => ?_,
    fun z a ha => ?_, fun a z z' hz' => ?_⟩
  · have hb := hφs p
    obtain ⟨b, hb⟩ := hb
    exact ⟨e.symm b, (hC _).trans ((congrArg φ (e.apply_symm_apply b)).trans hb)⟩
  · exact (Iff.of_eq (congrArg (· = 1) (hC a))).trans ((hφk (e a)).trans
      (Iff.of_eq (congrArg (· ∈ Subgroup.zpowers (clabelS u)) (he a))))
  · exact (hC a).trans ((hφl ⟨z, hns.subset z.2⟩ (e a) ((he a).trans ha)).trans
      (congrArg tPt (hE z).symm))
  ·
    have hinv : (((e a)⁻¹ : (cnGroup v w ⊓ vStab u : Subgroup Shat)) : Shat) = (a : Shat)⁻¹ :=
      (Subgroup.coe_inv _ (e a)).trans (congrArg (·⁻¹) (he a))
    have hz'' : (z' : CVert) =
        cvMul (z : CVert) (((e a)⁻¹ : (cnGroup v w ⊓ vStab u : Subgroup Shat)) : Shat) :=
      (hz'.trans (cvPerm_apply _ _)).trans (congrArg (cvMul (z : CVert)) hinv.symm)
    have hmem : cvMul (z : CVert) (((e a)⁻¹ : (cnGroup v w ⊓ vStab u : Subgroup Shat)) : Shat) ∈
        cgraph.neighborSet u ∩ cgraph.commonNeighbors v w :=
      (congrArg (· ∈ cgraph.neighborSet u ∩ cgraph.commonNeighbors v w) hz'').mp
        (hns.subset z'.2)
    have h1 := hφe (e a)⁻¹ ⟨z, hns.subset z.2⟩ hmem
    have h2 : (projAct (φ (e a)⁻¹))⁻¹ = projAct (φ (e a)) :=
      (congrArg (·⁻¹) ((congrArg projAct (map_inv φ (e a))).trans
        (map_inv projAct (φ (e a))))).trans (inv_inv _)
    have h3 : (⟨(z' : CVert), hns.subset z'.2⟩ :
        ↥(cgraph.neighborSet u ∩ cgraph.commonNeighbors v w)) = ⟨_, hmem⟩ := Subtype.ext hz''
    calc ((Set.equivOfEq hns).trans τ) z' = τ ⟨(z' : CVert), hns.subset z'.2⟩ := hE z'
      _ = τ ⟨_, hmem⟩ := congrArg τ h3
      _ = (projAct (φ (e a)⁻¹))⁻¹ (τ ⟨z, hns.subset z.2⟩) := h1
      _ = projAct (φ (e a)) (τ ⟨z, hns.subset z.2⟩) :=
        congrArg (fun g : Equiv.Perm IsoPt => g (τ ⟨z, hns.subset z.2⟩)) h2
      _ = projAct ((φ.comp e.toMonoidHom) a) (((Set.equivOfEq hns).trans τ) z) :=
        (congrArg₂ (fun g x => projAct g x) (hC a) (hE z)).symm

end Slice

theorem native_isFischerSlice
    {v w : CVert} (hw : w ∈ sphereThree v) :
    Fischer.IsFischerSlice cvPerm clabelS (cgraph.commonNeighbors v w) := by
  classical
  have H : ∀ x : CVert, LocalHom x := fun x => (nonempty_localHom x).some
  have hTT := native_order_three_common_neighbor_three_transposition_group.choose_spec.2 v w hw
  obtain ⟨-, -, hfaith, hinj, hord, -, horder, -⟩ := hTT
  have hE := native_order_three_common_neighbors_exact_3510.1 v w hw
  have hU := native_order_three_common_neighbor_local_unitary_graph.2.2 v w hw
  have : Fintype (cgraph.commonNeighbors v w) := Fintype.ofFinite _
  have hsrg : (cgraph.induce (cgraph.commonNeighbors v w)).IsSRGWith 3510 693 180 126 := hE.2.1
  have hmaps : ∀ a ∈ cnGroup v w, ∀ y ∈ cgraph.commonNeighbors v w,
      cvMul y a ∈ cgraph.commonNeighbors v w := fun a ha y hy => by
    have haQ := Subgroup.mem_inf.1 (cnGroup_le H v w ha)
    exact cvMul_mem_commonNeighbors (mem_vStab.1 haQ.1) (mem_vStab.1 haQ.2) hy
  refine
    { lab_act := clabelS_cvPerm
      finite := Set.toFinite _
      ncard := hE.2.2.1
      injOn := hinj
      orderOf_lab := hord
      orderOf_mul := fun y hy z hz hc => ?_
      mapsTo := fun a ha y hy => by
        rw [cvPerm_apply]
        exact hmaps _ (inv_mem ha) y hy
      faithful := fun a ha hfix => ?_
      transitive := fun y hy z hz => ?_
      valency := fun y hy => by
        rw [sliceGraph_neighborSet hw hy]
        exact (hU.2.2.2.2 y hy).1
      lambda := fun y z h => ?_
      mu := fun y hy z hz hne hna => ?_
      local_unitary := fun u hu => slice_local_unitary hw hu }
  · have hne : y ≠ z := fun e => hc (e ▸ Commute.refl _)
    have hna : ¬cgraph.Adj y z := fun ha => hc ((adj_iff_commute_of_mem hw hy hz hne).1 ha)
    exact (horder y hy z hz hne).2 hna
  · refine hfaith a ha fun x hx => ?_
    have h := hfix x hx
    rw [cvPerm_apply] at h
    calc cvMul x a = cvMul (cvMul x a⁻¹) a := by rw [h]
      _ = x := cvMul_inv_cancel' x a
  · obtain ⟨h, hh, hhy⟩ := exists_mem_cnGroup_cvMul_eq hw hy hz
    exact ⟨h⁻¹, inv_mem hh, by rw [cvPerm_apply, inv_inv, hhy]⟩
  · obtain ⟨hy, hz, ha⟩ := (sliceGraph_adj_iff hw).1 h
    have h1 := hsrg.of_adj ⟨y, hy⟩ ⟨z, hz⟩ ha
    rw [← Nat.card_eq_fintype_card] at h1
    rw [ncard_sliceGraph_commonNeighbors hw hy hz]
    exact h1
  · have hna' : ¬cgraph.Adj y z := fun ha => hna ((sliceGraph_adj_iff hw).2 ⟨hy, hz, ha⟩)
    have hne' : (⟨y, hy⟩ : cgraph.commonNeighbors v w) ≠ ⟨z, hz⟩ := fun e =>
      hne (congrArg Subtype.val e)
    have h1 := hsrg.of_not_adj hne' hna'
    rw [← Nat.card_eq_fintype_card] at h1
    rw [ncard_sliceGraph_commonNeighbors hw hy hz]
    exact h1

end CFSG.Monster.B.TwoA.Amalgam
