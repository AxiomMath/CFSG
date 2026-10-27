module

public import CFSG.Monster.B.TwoA.Amalgam.Chamber
public import CFSG.Monster.B.Geometry.ResidueTransfer
public import CFSG.Blueprint.Chevalley

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Geometry
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Blueprint.Chevalley
open scoped Pointwise

@[expose] def cosetCS :
    ChamberSystem (Fin 4) Chamber where
  adj := chamberAdj
  equivalence := chamberAdj_equivalence

@[simp] theorem cosetCS_adj
    (i : Fin 4) : cosetCS.adj i = chamberAdj i := rfl

abbrev baseChamber :
    Chamber := chamberOf 1

abbrev inclE
    (i : Fin 4) (g : Pc i) : Eam := Subgroup.inclusion (Pc_le_Eam i) g

theorem coe_inclE
    (i : Fin 4) (g : Pc i) : ((inclE i g : Eam) : Dfull) = g := rfl

@[expose] def chamberMulPerm
    (g : Eam) : Equiv.Perm Chamber where
  toFun c := chamberMul c g
  invFun c := chamberMul c g⁻¹
  left_inv c := by
    change chamberMul (chamberMul c g) g⁻¹ = c
    rw [← chamberMul_mul, mul_inv_cancel, chamberMul_one]
  right_inv c := by
    change chamberMul (chamberMul c g⁻¹) g = c
    rw [← chamberMul_mul, inv_mul_cancel, chamberMul_one]

theorem chamberMulPerm_apply
    (g : Eam) (c : Chamber) : chamberMulPerm g c = chamberMul c g := rfl

theorem chamberMulPerm_mem_typeAut
    (g : Eam) : chamberMulPerm g ∈ cosetCS.typeAut :=
  ChamberSystem.mem_typeAut.mpr fun i c d => chamberAdj_chamberMul i c d g

theorem exists_chamberMul_eq
    (c d : Chamber) : ∃ g : Eam, chamberMul c g = d := by
  obtain ⟨a, rfl⟩ := chamberOf_surjective c
  obtain ⟨b, rfl⟩ := chamberOf_surjective d
  exact ⟨a⁻¹ * b, by rw [chamberMul_chamberOf, mul_inv_cancel_left]⟩

theorem chamberMulPerm_chamberOf
    (g h : Eam) : chamberMulPerm g (chamberOf h) = chamberOf (h * g) :=
  rfl

theorem image_residue_chamberMulPerm
    (J : Set (Fin 4)) (g : Eam) :
    chamberMulPerm g '' cosetCS.residue J baseChamber = cosetCS.residue J (chamberOf g) := by
  rw [ChamberSystem.image_residue_of_mem_typeAut (chamberMulPerm_mem_typeAut g),
    chamberMulPerm_chamberOf, one_mul]

theorem mem_Qam_iff
    {j : Fin 4} {x : Dfull} : x ∈ Qam j ↔ ∀ k, k ≠ j → x ∈ Pc k := by
  simp only [Qam, Subgroup.mem_iInf]

theorem mem_Bam_iff
    {x : Dfull} : x ∈ Bam ↔ ∀ k, x ∈ Pc k := by
  simp only [Bam, Subgroup.mem_iInf]

theorem mem_Qam_iff_of_mem_Pc
    {i j : Fin 4} {x : Dfull} (hx : x ∈ Pc i) :
    x ∈ Qam j ↔ ∀ k, k ≠ i → k ≠ j → x ∈ Pc k := by
  rw [mem_Qam_iff]
  refine ⟨fun h k _ hkj => h k hkj, fun h k hkj => ?_⟩
  by_cases hki : k = i
  · rw [hki]
    exact hx
  · exact h k hki hkj

theorem mem_Bam_iff_of_mem_Pc
    {i : Fin 4} {x : Dfull} (hx : x ∈ Pc i) :
    x ∈ Bam ↔ ∀ k, k ≠ i → x ∈ Pc k := by
  rw [mem_Bam_iff]
  refine ⟨fun h k _ => h k, fun h k => ?_⟩
  by_cases hki : k = i
  · rw [hki]
    exact hx
  · exact h k hki

theorem Qam_le_Pc_self
    {i j : Fin 4} (hij : j ≠ i) : Qam j ≤ Pc i := Qam_le_Pc hij.symm

@[expose] def parGroup
    (J : Set (Fin 4)) : Subgroup Dfull :=
  Bam ⊔ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j

theorem Bam_le_parGroup
    (J : Set (Fin 4)) : Bam ≤ parGroup J := le_sup_left

theorem Qam_le_parGroup
    {J : Set (Fin 4)} {j : Fin 4} (hj : j ∈ J) : Qam j ≤ parGroup J :=
  le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)

theorem parGroup_le_Eam
    (J : Set (Fin 4)) : parGroup J ≤ Eam :=
  sup_le Bam_le_Eam (iSup₂_le fun j _ => Qam_le_Eam j)

theorem parGroup_eq_iSup
    {J : Set (Fin 4)} {j₀ : Fin 4} (hj₀ : j₀ ∈ J) :
    parGroup J = ⨆ (j : Fin 4) (_ : j ∈ J), Qam j :=
  sup_eq_right.mpr ((Bam_le_Qam j₀).trans (le_iSup₂_of_le j₀ hj₀ le_rfl))

theorem mem_residue_chamberOf_iff
    (J : Set (Fin 4)) (g h : Eam) :
    chamberOf h ∈ cosetCS.residue J (chamberOf g) ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ parGroup J := by
  constructor
  · rintro ⟨γ, hγ, hJ, hend⟩
    induction γ generalizing g with
    | nil =>
      have := chamberOf_eq_iff.mp hend
      exact Bam_le_parGroup J this
    | cons p γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      obtain ⟨g', hg'⟩ := chamberOf_surjective p.2
      rw [← hg'] at h1 h2
      rw [galleryEnd_cons, ← hg'] at hend
      have hq : ((g * g'⁻¹ : Eam) : Dfull) ∈ parGroup J :=
        Qam_le_parGroup (hJ p.1 (by simp [galleryType])) ((chamberAdj_iff _ g g').mp h1)
      have hih := ih g' h2 (fun j hj => hJ j (by simp [galleryType] at hj ⊢; tauto)) hend
      have e : ((h * g⁻¹ : Eam) : Dfull) =
          ((h * g'⁻¹ : Eam) : Dfull) * ((g * g'⁻¹ : Eam) : Dfull)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact mul_mem hih (inv_mem hq)
  · intro hmem
    let S : Subgroup Dfull :=
      { carrier := {x | ∃ hx : x ∈ Eam, chamberOf (⟨x, hx⟩ * g) ∈ cosetCS.residue J (chamberOf g)}
        one_mem' := ⟨one_mem _, by
          have e : chamberOf (⟨1, one_mem _⟩ * g) = chamberOf g := congrArg chamberOf (one_mul g)
          rw [e]
          exact cosetCS.self_mem_residue J _⟩
        mul_mem' := by
          rintro x y ⟨hx, hxR⟩ ⟨hy, hyR⟩
          refine ⟨mul_mem hx hy, ?_⟩
          have h1 : chamberMulPerm (g⁻¹ * ⟨y, hy⟩ * g) (chamberOf (⟨x, hx⟩ * g)) =
              chamberOf (⟨x * y, mul_mem hx hy⟩ * g) := by
            rw [chamberMulPerm_chamberOf]
            congr 1
            ext
            change x * (g : Dfull) * ((g : Dfull)⁻¹ * y * g) = x * y * g
            group
          have h2 : chamberMulPerm (g⁻¹ * ⟨y, hy⟩ * g) '' cosetCS.residue J (chamberOf g) =
              cosetCS.residue J (chamberOf (⟨y, hy⟩ * g)) := by
            rw [ChamberSystem.image_residue_of_mem_typeAut (chamberMulPerm_mem_typeAut _),
              chamberMulPerm_chamberOf, show g * (g⁻¹ * ⟨y, hy⟩ * g) = ⟨y, hy⟩ * g by group]
          have h3 : cosetCS.residue J (chamberOf (⟨y, hy⟩ * g)) =
              cosetCS.residue J (chamberOf g) := ChamberSystem.residue_eq_of_mem hyR
          rw [← h1, ← h3, ← h2]
          exact Set.mem_image_of_mem _ hxR
        inv_mem' := by
          rintro x ⟨hx, hxR⟩
          refine ⟨inv_mem hx, ?_⟩
          have hgx : chamberOf g ∈ cosetCS.residue J (chamberOf (⟨x, hx⟩ * g)) :=
            ChamberSystem.mem_residue_symm hxR
          have h2 : chamberMulPerm (g⁻¹ * ⟨x, hx⟩⁻¹ * g) ''
              cosetCS.residue J (chamberOf (⟨x, hx⟩ * g)) =
              cosetCS.residue J (chamberOf g) := by
            rw [ChamberSystem.image_residue_of_mem_typeAut (chamberMulPerm_mem_typeAut _),
              chamberMulPerm_chamberOf]
            congr 2
            group
          have h1 : chamberMulPerm (g⁻¹ * ⟨x, hx⟩⁻¹ * g) (chamberOf g) =
              chamberOf (⟨x⁻¹, inv_mem hx⟩ * g) := by
            rw [chamberMulPerm_chamberOf, show g * (g⁻¹ * ⟨x, hx⟩⁻¹ * g) = ⟨x, hx⟩⁻¹ * g by group]
            rfl
          rw [← h1, ← h2]
          exact Set.mem_image_of_mem _ hgx }
    have hle : parGroup J ≤ S := by
      refine sup_le (fun x hx => ⟨Bam_le_Eam hx, ?_⟩)
        (iSup₂_le fun j hj x hx => ⟨Qam_le_Eam j hx, ?_⟩)
      · have : chamberOf (⟨x, Bam_le_Eam hx⟩ * g) = chamberOf g := by
          refine chamberOf_eq_iff.mpr ?_
          simpa using inv_mem hx
        rw [this]
        exact cosetCS.self_mem_residue J _
      · refine cosetCS.residue_mono (Set.singleton_subset_iff.mpr hj) _
          (ChamberSystem.mem_residue_singleton.mpr ?_)
        change chamberAdj j (chamberOf g) (chamberOf (⟨x, Qam_le_Eam j hx⟩ * g))
        rw [chamberAdj_iff]
        simpa using inv_mem hx
    obtain ⟨_, hR⟩ := hle hmem
    have e : (⟨((h * g⁻¹ : Eam) : Dfull), parGroup_le_Eam J hmem⟩ * g : Eam) = h := by
      ext
      simp
    rwa [e] at hR

theorem Pc_le_iSup_Qam_of_residue
    {i : Fin 4} {J : Set (Fin 4)} {j₀ : Fin 4}
    (hj₀ : j₀ ∈ J) (h : ∀ g : Pc i, chamberOf (inclE i g) ∈ cosetCS.residue J baseChamber) :
    Pc i ≤ ⨆ (j : Fin 4) (_ : j ∈ J), Qam j := by
  intro g hg
  have := (mem_residue_chamberOf_iff J 1 (inclE i ⟨g, hg⟩)).mp (h ⟨g, hg⟩)
  rw [parGroup_eq_iSup hj₀, inv_one, mul_one] at this
  exact this

section FlagModel

variable {i : Fin 4} {F : Type*} (Y : ChamberSystem (Fin 4) F) (φ : Pc i → F)

structure IsFlagModel : Prop where
  surjective : Function.Surjective φ
  eq_iff : ∀ g h : Pc i, φ g = φ h ↔ ((g * h⁻¹ : Pc i) : Dfull) ∈ Bam
  adj_iff : ∀ (g h : Pc i) (j : Fin 4), j ≠ i →
    (Y.adj j (φ g) (φ h) ↔ ((g * h⁻¹ : Pc i) : Dfull) ∈ Qam j)

variable {Y φ}

@[expose] def flagChamber (hφ : IsFlagModel Y φ) (a : F) : Chamber :=
  chamberOf (inclE i (Function.surjInv hφ.surjective a))

variable (hφ : IsFlagModel Y φ)
include hφ

theorem flagChamber_apply (g : Pc i) : flagChamber hφ (φ g) = chamberOf (inclE i g) := by
  rw [flagChamber, chamberOf_eq_iff]
  have h := (hφ.eq_iff g (Function.surjInv hφ.surjective (φ g))).mp
    (Function.surjInv_eq hφ.surjective (φ g)).symm
  exact h

theorem flagChamber_injective : Function.Injective (flagChamber hφ) := by
  intro a b h
  obtain ⟨g, rfl⟩ := hφ.surjective a
  obtain ⟨g', rfl⟩ := hφ.surjective b
  rw [flagChamber_apply, flagChamber_apply, chamberOf_eq_iff] at h
  exact ((hφ.eq_iff g' g).mpr h).symm

theorem chamberAdj_flagChamber_iff {j : Fin 4} (hj : j ≠ i) (a b : F) :
    chamberAdj j (flagChamber hφ a) (flagChamber hφ b) ↔ Y.adj j a b := by
  obtain ⟨g, rfl⟩ := hφ.surjective a
  obtain ⟨g', rfl⟩ := hφ.surjective b
  rw [flagChamber_apply, flagChamber_apply, chamberAdj_iff, hφ.adj_iff g g' j hj]
  rfl

theorem flagChamber_one : flagChamber hφ (φ 1) = baseChamber := by
  rw [flagChamber_apply]
  rfl

theorem exists_flagChamber_of_adj {j : Fin 4} (hj : j ≠ i) (a : F) {c : Chamber}
    (h : chamberAdj j (flagChamber hφ a) c) : ∃ b, flagChamber hφ b = c := by
  obtain ⟨g, rfl⟩ := hφ.surjective a
  obtain ⟨h', rfl⟩ := chamberOf_surjective c
  rw [flagChamber_apply, chamberAdj_iff] at h
  have hq := Qam_le_Pc_self hj h
  have hh : (h' : Dfull) ∈ Pc i := by
    have := mul_mem (inv_mem hq) g.2
    simpa using this
  refine ⟨φ ⟨h', hh⟩, ?_⟩
  rw [flagChamber_apply]
  rfl

theorem image_panel_flagChamber {j : Fin 4} (hj : j ≠ i) :
    flagChamber hφ '' {b | Y.adj j (φ 1) b} = cosetCS.residue {j} baseChamber := by
  ext c
  rw [ChamberSystem.mem_residue_singleton, cosetCS_adj, ← flagChamber_one hφ]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (chamberAdj_flagChamber_iff hφ hj _ _).mpr hb
  · intro hc
    obtain ⟨b, rfl⟩ := exists_flagChamber_of_adj hφ hj (φ 1) hc
    exact ⟨b, (chamberAdj_flagChamber_iff hφ hj _ _).mp hc, rfl⟩

theorem encard_panel_of_flagModel {j : Fin 4} (hj : j ≠ i) :
    (cosetCS.residue {j} baseChamber).encard = {b | Y.adj j (φ 1) b}.encard := by
  rw [← image_panel_flagChamber hφ hj, (flagChamber_injective hφ).injOn.encard_image]

theorem isGallery_flagChamber {a : F} {γ : List (Fin 4 × F)} (hγ : Y.IsGallery a γ)
    (hJ : ∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) :
    cosetCS.IsGallery (flagChamber hφ a) (galleryMap (flagChamber hφ) γ) := by
  induction γ generalizing a with
  | nil => trivial
  | cons p γ ih =>
    have hp : p.1 ≠ i := hJ p.1 (by simp [galleryType])
    refine ⟨(chamberAdj_flagChamber_iff hφ hp a p.2).mpr hγ.1, ih hγ.2 fun j hj => hJ j ?_⟩
    simp [galleryType] at hj ⊢
    tauto

theorem flagChamber_mem_residue {J : Set (Fin 4)} (hJi : ∀ j ∈ J, j ≠ i) {a : F}
    {γ : List (Fin 4 × F)} (hγ : Y.IsGallery a γ) (hJ : ∀ j ∈ galleryType γ, j ∈ J) :
    flagChamber hφ (galleryEnd a γ) ∈ cosetCS.residue J (flagChamber hφ a) :=
  ⟨galleryMap (flagChamber hφ) γ, isGallery_flagChamber hφ hγ fun j hj => hJi j (hJ j hj),
    by simpa [galleryType, galleryMap] using hJ, galleryEnd_galleryMap _ _ _⟩

theorem bijOn_flagChamber
    (hconn : ∀ a : F, ∃ γ : List (Fin 4 × F), Y.IsGallery (φ 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) ∧ galleryEnd (φ 1) γ = a) :
    Set.BijOn (flagChamber hφ) Set.univ (cosetCS.residue {j | j ≠ i} baseChamber) := by
  have hmor : ∀ (a : F) (γ : List (Fin 4 × F)), Y.IsGallery a γ →
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) →
      cosetCS.IsGallery (flagChamber hφ a) (galleryMap (flagChamber hφ) γ) :=
    fun _ _ hγ hJ => isGallery_flagChamber hφ hγ hJ
  refine ⟨fun a _ => ?_, (flagChamber_injective hφ).injOn, fun c hc => ?_⟩
  · obtain ⟨γ, hγ, hJ, rfl⟩ := hconn a
    refine ⟨galleryMap (flagChamber hφ) γ, by rw [← flagChamber_one hφ]; exact hmor _ γ hγ hJ,
      by simpa [galleryType, galleryMap] using hJ, ?_⟩
    rw [← flagChamber_one hφ, galleryEnd_galleryMap]
  · obtain ⟨γ, hγ, hJ, rfl⟩ := hc
    suffices key : ∀ (γ : List (Fin 4 × Chamber)) (a : F),
        cosetCS.IsGallery (flagChamber hφ a) γ →
        (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) →
        ∃ b, flagChamber hφ b = galleryEnd (flagChamber hφ a) γ by
      obtain ⟨b, hb⟩ := key γ (φ 1) (by rw [flagChamber_one hφ]; exact hγ) hJ
      exact ⟨b, Set.mem_univ _, by rw [hb, flagChamber_one hφ]⟩
    intro γ
    induction γ with
    | nil => intro a _ _; exact ⟨a, rfl⟩
    | cons p γ ih =>
      intro a hγ hJ
      have hp : p.1 ≠ i := hJ p.1 (by simp [galleryType])
      obtain ⟨b, hb⟩ := exists_flagChamber_of_adj hφ hp a hγ.1
      rw [galleryEnd_cons, ← hb]
      exact ih b (hb ▸ hγ.2) fun j hj => hJ j (by simp [galleryType] at hj ⊢; tauto)

theorem Pc_le_iSup_Qam_of_flagModel
    (hconn : ∀ a : F, ∃ γ : List (Fin 4 × F), Y.IsGallery (φ 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) ∧ galleryEnd (φ 1) γ = a) :
    Pc i ≤ ⨆ (j : Fin 4) (_ : j ∈ {j : Fin 4 | j ≠ i}), Qam j := by
  have hj₀ : i + 1 ∈ {j : Fin 4 | j ≠ i} := by
    change i + 1 ≠ i
    fin_cases i <;> decide
  refine Pc_le_iSup_Qam_of_residue hj₀ fun g => ?_
  rw [← flagChamber_apply hφ]
  exact (bijOn_flagChamber hφ hconn).mapsTo (Set.mem_univ _)

theorem isResidueBuilding_of_flagModel {M : CoxeterMatrix (Fin 4)} {W : Type*}
    [Group W] {cs : CoxeterSystem M W} {δ : F → F → W}
    (hB : IsBuildingOn cs δ {j | j ≠ i} Set.univ)
    (hδ : ∀ a b, ∀ j : Fin 4, j ≠ i → (Y.adj j a b ↔ δ a b = 1 ∨ δ a b = cs.simple j))
    (hconn : ∀ a : F, ∃ γ : List (Fin 4 × F), Y.IsGallery (φ 1) γ ∧
      (∀ j ∈ galleryType γ, j ∈ {j : Fin 4 | j ≠ i}) ∧ galleryEnd (φ 1) γ = a) :
    cosetCS.IsResidueBuilding cs {j | j ≠ i} baseChamber :=
  ChamberSystem.isResidueBuilding_of_bijOn cosetCS hB (bijOn_flagChamber hφ hconn)
    fun a _ b _ j hj => (chamberAdj_flagChamber_iff hφ hj a b).trans (hδ a b j hj)

end FlagModel

theorem exists_residue_iso
    {F : Type*} {Y : ChamberSystem (Fin 4) F} {J : Set (Fin 4)}
    {ψ : F → Chamber} (hψ : Set.BijOn ψ Set.univ (cosetCS.residue J baseChamber))
    (hadj : ∀ a b, ∀ j ∈ J, (cosetCS.adj j (ψ a) (ψ b) ↔ Y.adj j a b)) (x : Chamber) :
    ∃ ψ' : F → Chamber, Set.BijOn ψ' Set.univ (cosetCS.residue J x) ∧
      ∀ a b, ∀ j ∈ J, (cosetCS.adj j (ψ' a) (ψ' b) ↔ Y.adj j a b) := by
  obtain ⟨g, rfl⟩ := chamberOf_surjective x
  refine ⟨chamberMulPerm g ∘ ψ, ?_, fun a b j hj => ?_⟩
  · rw [← image_residue_chamberMulPerm]
    exact ((chamberMulPerm g).injective.injOn.bijOn_image).comp hψ
  · rw [Function.comp_apply, Function.comp_apply, ← hadj a b j hj]
    exact chamberAdj_chamberMul j _ _ g

@[expose] def chamberCS :
    ChamberSystem (Fin Tag.F4.rank) Chamber where
  adj := chamberAdj
  equivalence := chamberAdj_equivalence

@[simp] theorem chamberCS_adj
    (i : Fin Tag.F4.rank) : chamberCS.adj i = chamberAdj i := rfl

end CFSG.Monster.B.TwoA.Amalgam
