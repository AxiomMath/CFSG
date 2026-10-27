module

public import CFSG.Monster.B.TwoA.Fischer.CliqueCode
public import CFSG.Monster.B.Fischer.DesignRecognition

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical CFSG.Monster.B.Classical.UnitarySix CFSG.Monster.B.Classical.Plane
  CFSG.Monster.B.TwoA.Unitary.Clique CFSG.Fischer CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary CFSG.Monster.B.Fischer CFSG.Monster.B.Classical.Mog22
open scoped IsMulCommutative LinearAlgebra.Projectivization MatrixGroups

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Design

variable (lab) (C : Set V) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Fintype C]

@[expose] def cliqueDesign : Finset (Finset C) :=
  @Finset.filter _ (fun T => Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C)
    (fun _ => Classical.propDecidable _) Finset.univ

variable {lab C}

theorem mem_cliqueDesign {T : Finset C} :
    T ∈ cliqueDesign lab C ↔ Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C := by
  classical
  rw [cliqueDesign, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ T)

open _root_.Classical in
theorem exists_finset_image_eq {B : Set V} (hB : B ⊆ C) :
    ∃ T : Finset C, Subtype.val '' (T : Set C) = B := by
  refine ⟨Finset.univ.filter fun z => (z : V) ∈ B, Set.ext fun v => ⟨?_, fun hv => ?_⟩⟩
  · rintro ⟨z, hz, rfl⟩
    exact (Finset.mem_filter.1 hz).2
  · exact ⟨⟨v, hB hv⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩, rfl⟩

end Design

theorem image_val_injective {C : Set V} :
    Function.Injective fun T : Finset C => Subtype.val '' (T : Set C) := fun _ _ h =>
  Finset.coe_injective (Set.image_injective.2 Subtype.val_injective h)

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

section Steiner

variable {C : Set V} (hC : IsSliceMaxClique lab Y C)
  [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Fintype C]
include hC

theorem isSteiner3Design : IsSteiner3Design (cliqueDesign lab C) := by
  obtain ⟨_, -, h22, -, -, -, hB6, hT3, -⟩ := hS.clique_code_steiner_design hC
  refine ⟨by rw [← Nat.card_eq_fintype_card, h22], fun T hT => ?_, fun T hT => ?_⟩
  · have h := (hB6 _ (mem_cliqueDesign.1 hT)).2
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset] at h
  · obtain ⟨B, ⟨hB, hTB⟩, huniq⟩ := hT3 (Subtype.val '' (T : Set C))
      (by rintro _ ⟨z, -, rfl⟩; exact z.2)
      (by rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset, hT])
    obtain ⟨T', rfl⟩ := exists_finset_image_eq (hB6 B hB).1
    refine ⟨T', ⟨mem_cliqueDesign.2 hB, fun z hz => ?_⟩, fun T'' hT'' => ?_⟩
    · obtain ⟨z', hz', hzz⟩ := hTB ⟨z, hz, rfl⟩
      rw [Subtype.val_injective hzz] at hz'
      exact hz'
    · refine image_val_injective (huniq _ ⟨mem_cliqueDesign.1 hT''.1, ?_⟩)
      exact Set.image_mono (Finset.coe_subset.2 hT''.2)

end Steiner

theorem setStabPerm_mem_designAut {C : Set V}
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Fintype C]
    (f : setStab act lab Y C) : setStabPerm act lab Y C f ∈ designAut (cliqueDesign lab C) := by
  have himg : ∀ (a : setStab act lab Y C) (B : Finset C),
      Subtype.val '' ((B.map (setStabPerm act lab Y C a).toEmbedding : Finset C) : Set C) =
        act (a : S) '' (Subtype.val '' (B : Set C)) := fun a B => by
    rw [Finset.coe_map, Set.image_image, Set.image_image]
    rfl
  have hmem : ∀ (a : setStab act lab Y C) {B : Set V}, B ∈ cliqueBlocks lab C →
      act (a : S) '' B ∈ cliqueBlocks lab C := fun a B hB =>
    image_mem_cliqueBlocks hS.lab_act (fun x hx => (a.2.2 x).2 hx) (setStabPerm act lab Y C a)
      (fun _ => rfl) hB
  intro B
  rw [mem_cliqueDesign, mem_cliqueDesign, himg]
  refine ⟨fun h => ?_, hmem f⟩
  have h' := hmem f⁻¹ h
  have e : act ((f⁻¹ : setStab act lab Y C) : S) '' (act (f : S) '' (Subtype.val '' (B : Set C))) =
      Subtype.val '' (B : Set C) := by
    rw [Set.image_image]
    refine Eq.trans (Set.image_congr fun x _ => ?_) (Set.image_id _)
    show act ((f : S)⁻¹) (act (f : S) x) = x
    rw [map_inv]
    exact (act (f : S)).symm_apply_apply x
  rwa [e] at h'

end IsFischerSlice

theorem mem_neighborSet_of_ne {C : Set V} (hC : IsSliceMaxClique lab Y C) {u : V} (hu : u ∈ C)
    {y : C} (hy : y ≠ ⟨u, hu⟩) : (y : V) ∈ (sliceGraph lab Y).neighborSet u :=
  mem_neighborSet_of_mem_clique hC.1.2 hu y.2 fun h => hy (Subtype.ext h)

namespace LocalChart

variable {u : V} (L : LocalChart act lab Y u) {C : Set V} (hC : IsSliceMaxClique lab Y C)
  (hu : u ∈ C) (g : SU frobeniusF4 6) (hWe : L.img C = planePts (smulSub g W0))
include hC

theorem chartIota_bijective :
    Function.Bijective fun y : {y : C // y ≠ ⟨u, hu⟩} => Ωproj.symm (L.coordC g hWe y) := by
  refine ⟨fun y y' h => Subtype.ext (L.coordC_injOn g hWe (mem_neighborSet_of_ne hC hu y.2)
    (mem_neighborSet_of_ne hC hu y'.2) (Ωproj.symm.injective h)), fun p => ?_⟩
  obtain ⟨z, hz, hzp⟩ := L.exists_coordC_eq g hWe (Ωproj p)
  refine ⟨⟨z, fun h => (sliceGraph lab Y).ne_of_adj hz (congrArg Subtype.val h).symm⟩, ?_⟩
  change Ωproj.symm (L.coordC g hWe z) = p
  rw [hzp, Equiv.symm_apply_apply]

@[expose] def chartIota : {y : C // y ≠ ⟨u, hu⟩} ≃ Fin 21 :=
  Equiv.ofBijective _ (L.chartIota_bijective hC hu g hWe)

theorem chartIota_apply (y : {y : C // y ≠ ⟨u, hu⟩}) :
    L.chartIota hC hu g hWe y = Ωproj.symm (L.coordC g hWe y) := rfl

theorem coordC_chartIota_symm (p : Fin 21) :
    L.coordC g hWe ((L.chartIota hC hu g hWe).symm p : C) = Ωproj p := by
  have h := (L.chartIota hC hu g hWe).apply_symm_apply p
  rw [chartIota_apply, Equiv.symm_apply_eq] at h
  exact h

theorem mem_planeImg_iff [DecidableEq C] {A : Submodule F4 UnitarySix.V} {T : Finset C}
    (hT : Subtype.val '' (T : Set C) = insert u (Subtype.val '' (L.τ ⁻¹' planePts A)))
    (p : Fin 21) :
    p ∈ planeImg (L.chartIota hC hu g hWe) T ↔ Ω p ∈ A.comap (planeEmb g) := by
  set y : {y : C // y ≠ ⟨u, hu⟩} := (L.chartIota hC hu g hWe).symm p with hy
  have hyn := mem_neighborSet_of_ne hC hu y.2
  have hyu : ((y : C) : V) ≠ u := fun h => y.2 (Subtype.ext h)
  have h1 : (y : C) ∈ T ↔ L.τ ⟨_, hyn⟩ ∈ planePts A := by
    rw [← Finset.mem_coe, ← Subtype.val_injective.mem_set_image, hT, Set.mem_insert_iff,
      or_iff_right hyu]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [show z = ⟨_, hyn⟩ from Subtype.ext hzy] at hz
    · exact fun h => ⟨_, h, rfl⟩
  rw [mem_planeImg, ← hy, h1]
  refine (mem_planePts_iff_eW g A ⟨_, L.mem_planePts_of_mem g hWe ⟨_, hyn⟩ (y : C).2⟩).trans ?_
  rw [← L.coordC_of_mem g hWe _ hyn, hy, coordC_chartIota_symm, Ωproj_apply,
    Projectivization.submodule_mk, Submodule.span_singleton_le_iff_mem]

section Recognition

variable (hS : IsFischerSlice act lab Y) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
  [Fintype C] [DecidableEq C]
include hS

theorem image_planeImg_eq :
    ((cliqueDesign lab C).filter (⟨u, hu⟩ ∈ ·)).image (planeImg (L.chartIota hC hu g hWe)) =
      Finset.univ.image projLine := by
  ext P
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨T, ⟨hT, huT⟩, rfl⟩
    obtain ⟨A, hAW, hA2, hTA⟩ := (L.mem_cliqueBlocks_and_mem_iff hS hC hu g hWe _).1
      ⟨mem_cliqueDesign.1 hT, ⟨_, huT, rfl⟩⟩
    obtain ⟨a, ha⟩ := (exists_projLine_iff _).2 ⟨A.comap (planeEmb g),
      by rw [finrank_comap_planeEmb hAW, hA2], L.mem_planeImg_iff hC hu g hWe hTA⟩
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨W', hW'2, hW'⟩ := (exists_projLine_iff (projLine a)).1 ⟨a, rfl⟩
    have hAW := map_planeEmb_le g W'
    have hA2 : Module.finrank F4 (W'.map (planeEmb g)) = 2 := by
      rw [finrank_map_planeEmb, hW'2]
    obtain ⟨hB, -⟩ := (L.mem_cliqueBlocks_and_mem_iff hS hC hu g hWe _).2 ⟨_, hAW, hA2, rfl⟩
    obtain ⟨T, hT⟩ := exists_finset_image_eq (C := C)
      (Set.insert_subset hu (L.image_preimage_subset g hWe hAW))
    refine ⟨T, ⟨mem_cliqueDesign.2 (by rw [hT]; exact hB), ?_⟩, Finset.ext fun p => ?_⟩
    · have h : u ∈ Subtype.val '' (T : Set C) := by
        rw [hT]
        exact Set.mem_insert u _
      obtain ⟨z, hz, hzu⟩ := h
      rwa [show z = ⟨u, hu⟩ from Subtype.ext hzu] at hz
    · rw [L.mem_planeImg_iff hC hu g hWe hT,
        Submodule.comap_map_eq_of_injective (planeEmb_injective g), ← hW' p]

omit [DecidableEq C] in
theorem exists_designAut_psl (A : PSL(3, F4)) :
    ∃ σ ∈ designAut (cliqueDesign lab C), σ ⟨u, hu⟩ = ⟨u, hu⟩ ∧
      ∀ p, σ ((L.chartIota hC hu g hWe).symm p : C) =
        (L.chartIota hC hu g hWe).symm (pslPerm A p) := by
  let σW : Equiv.Perm (planePts (smulSub g W0)) :=
    ((eW g).trans (MulAction.toPerm A)).trans (eW g).symm
  have hσW : ∀ q, eW g (σW q) = A • eW g q := fun q => by
    simp only [σW, Equiv.trans_apply, Equiv.apply_symm_apply, MulAction.toPerm_apply]
  obtain ⟨a, ha, hau, hact⟩ := (hS.mem_range_restrL_iff_setStab hC hu L hWe σW).1
    ((mem_range_restrL_iff g σW).2 ⟨A, hσW⟩)
  have hb : a ∈ sliceStab act lab Y u := ⟨ha.1, hau⟩
  refine ⟨setStabPerm act lab Y C ⟨a, ha⟩, hS.setStabPerm_mem_designAut _, Subtype.ext hau,
    fun p => ?_⟩
  set y := (L.chartIota hC hu g hWe).symm p with hy
  have hyn := mem_neighborSet_of_ne hC hu y.2
  have hzn := hS.act_mem_neighborSet hb hyn
  have hmem := L.mem_planePts_of_mem g hWe ⟨_, hyn⟩ (y : C).2
  have key : L.coordC g hWe (setStabPerm act lab Y C ⟨a, ha⟩ (y : C)) = A • Ωproj p := by
    have h := hact ⟨_, hmem⟩ ⟨_, hyn⟩ ⟨_, hzn⟩ rfl rfl
    have e1 : ∀ hz : L.τ ⟨_, hzn⟩ ∈ planePts (smulSub g W0),
        eW g ⟨L.τ ⟨_, hzn⟩, hz⟩ = A • Ωproj p := fun hz => by
      rw [show (⟨L.τ ⟨_, hzn⟩, hz⟩ : planePts (smulSub g W0)) = σW ⟨_, hmem⟩ from
        Subtype.ext h.symm, hσW, ← L.coordC_of_mem g hWe _ hyn, hy, coordC_chartIota_symm]
    rw [L.coordC_of_mem g hWe (setStabPerm act lab Y C ⟨a, ha⟩ (y : C)) hzn]
    exact e1 _
  have hfix : setStabPerm act lab Y C ⟨a, ha⟩ ⟨u, hu⟩ = ⟨u, hu⟩ := Subtype.ext hau
  have hne : setStabPerm act lab Y C ⟨a, ha⟩ (y : C) ≠ ⟨u, hu⟩ := fun h =>
    y.2 ((setStabPerm act lab Y C ⟨a, ha⟩).injective (h.trans hfix.symm))
  have h2 : (L.chartIota hC hu g hWe).symm (pslPerm A p) = ⟨_, hne⟩ := by
    rw [Equiv.symm_apply_eq, chartIota_apply, pslPerm_apply]
    exact congrArg Ωproj.symm key.symm
  rw [h2]

end Recognition

end LocalChart

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y)
include hS

theorem exists_cliqueEta
    {C : Set V} (hC : IsSliceMaxClique lab Y C)
    [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] [Fintype C] [DecidableEq C] :
    ∃ η : C ≃ X₀, ∀ T : Finset C,
      T ∈ cliqueDesign lab C ↔ T.image (fun z => (η z : Fin 24)) ∈ ℬ₀ := by
  obtain ⟨u, hu⟩ := hS.nonempty_of_isSliceMaxClique hC
  obtain ⟨L⟩ := hS.nonempty_localChart (hC.1.1 hu)
  obtain ⟨W, hW, hWe⟩ := L.exists_img_eq hS hC hu
  obtain ⟨g, rfl⟩ := hW.exists_eq_smulSub
  obtain ⟨j, hinj, himg, -, hiff⟩ := twenty_two_derived_plane_design_recognition.1 C
    (cliqueDesign lab C) ⟨u, hu⟩ (L.chartIota hC hu g hWe) (hS.isSteiner3Design hC)
    (L.image_planeImg_eq hC hu g hWe hS) (L.exists_designAut_psl hC hu g hWe hS)
  have hmem : ∀ z, etaMap (L.chartIota hC hu g hWe) j z ∈ X₀ := fun z => by
    rw [← himg]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ z)
  have hbij : Function.Bijective fun z : C => (⟨_, hmem z⟩ : X₀) := by
    refine ⟨fun z z' h => hinj (congrArg Subtype.val h), fun i => ?_⟩
    have hi : (i : Fin 24) ∈ Finset.univ.image (etaMap (L.chartIota hC hu g hWe) j) := by
      rw [himg]
      exact i.2
    obtain ⟨z, -, hz⟩ := Finset.mem_image.1 hi
    exact ⟨z, Subtype.ext hz⟩
  exact ⟨Equiv.ofBijective _ hbij, fun T => hiff T⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
