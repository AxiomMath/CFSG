module

public import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple

public noncomputable section

namespace CFSG.RankThree.PerfectCover

open Subgroup
open scoped commutatorElement

universe u v

section Definitions

variable (S : Type u) [Group S]

abbrev hopfEval : FreeGroup S →* S := FreeGroup.lift id

abbrev hopfRelations : Subgroup (FreeGroup S) := (hopfEval S).ker

abbrev hopfCommutatorRelations : Subgroup (FreeGroup S) :=
  ⁅(⊤ : Subgroup (FreeGroup S)), hopfRelations S⁆

abbrev HopfCover : Type u :=
  commutator (FreeGroup S) ⧸ (hopfCommutatorRelations S).subgroupOf (commutator (FreeGroup S))

theorem hopfCommutatorRelations_le_relations : hopfCommutatorRelations S ≤ hopfRelations S :=
  Subgroup.commutator_le_right _ _

@[expose] def hopfCoverMap : HopfCover S →* S :=
  QuotientGroup.lift _ ((hopfEval S).comp (commutator (FreeGroup S)).subtype) fun _ hd =>
    hopfCommutatorRelations_le_relations S hd

abbrev hopfMultiplier : Subgroup (HopfCover S) := (hopfCoverMap S).ker

@[expose] def IsCentralExtension {E : Type v} [Group E] (p : E →* S) : Prop :=
  Function.Surjective p ∧ p.ker ≤ center E

@[expose] def IsPerfectCentralExtension {E : Type v} [Group E] (p : E →* S) : Prop :=
  IsCentralExtension S p ∧ commutator E = ⊤

end Definitions

section Basic

variable {S : Type u} [Group S]

@[simp]
theorem hopfCoverMap_mk (d : commutator (FreeGroup S)) :
    hopfCoverMap S (d : HopfCover S) = hopfEval S d := rfl

theorem mk_mem_hopfMultiplier_iff (d : commutator (FreeGroup S)) :
    (d : HopfCover S) ∈ hopfMultiplier S ↔ (d : FreeGroup S) ∈ hopfRelations S :=
  Iff.rfl

theorem hopfMultiplier_le_center : hopfMultiplier S ≤ center (HopfCover S) := by
  intro m hm
  rw [mem_center_iff]
  intro u
  obtain ⟨d', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective m
  have hc : ⁅(d' : FreeGroup S), (d : FreeGroup S)⁆ ∈ hopfCommutatorRelations S :=
    commutator_mem_commutator (mem_top _) hm
  have h1 : QuotientGroup.mk'
      ((hopfCommutatorRelations S).subgroupOf (commutator (FreeGroup S))) ⁅d', d⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem exists_mem_commutator_hopfEval_eq [Group.IsPerfect S] (s : S) :
    ∃ d ∈ commutator (FreeGroup S), hopfEval S d = s := by
  have hmap : (commutator (FreeGroup S)).map (hopfEval S) = commutator S := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator,
      map_top_of_surjective _ (fun s => ⟨FreeGroup.of s, by simp⟩)]
  have hs : s ∈ (commutator (FreeGroup S)).map (hopfEval S) := by
    rw [hmap, Group.IsPerfect.commutator_eq_top]
    exact mem_top s
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hs
  exact ⟨d, hd, rfl⟩

theorem hopfCoverMap_surjective [Group.IsPerfect S] : Function.Surjective (hopfCoverMap S) := by
  intro s
  obtain ⟨d, hd, hds⟩ := exists_mem_commutator_hopfEval_eq s
  exact ⟨((⟨d, hd⟩ : commutator (FreeGroup S)) : HopfCover S), hds⟩

theorem mk_mem_center_of_mem_hopfRelations {r : FreeGroup S} (hr : r ∈ hopfRelations S) :
    QuotientGroup.mk' (hopfCommutatorRelations S) r ∈
      center (FreeGroup S ⧸ hopfCommutatorRelations S) := by
  rw [mem_center_iff]
  intro f
  obtain ⟨f, rfl⟩ := QuotientGroup.mk'_surjective _ f
  have h1 : QuotientGroup.mk' (hopfCommutatorRelations S) ⁅f, r⁆ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator (mem_top f) hr)
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem hopfCover_isPerfect [Group.IsPerfect S] : Group.IsPerfect (HopfCover S) := by
  rw [Group.isPerfect_def, eq_top_iff]
  rintro u -
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective u
  set π := QuotientGroup.mk' (hopfCommutatorRelations S)
  have hS : commutator (FreeGroup S) = closure {g | ∃ g₁ ∈ (⊤ : Subgroup (FreeGroup S)),
      ∃ g₂ ∈ (⊤ : Subgroup (FreeGroup S)), ⁅g₁, g₂⁆ = g} := by
    rw [_root_.commutator_def, Subgroup.commutator_def]
  have key : ∀ (w : FreeGroup S) (hw : w ∈ closure {g | ∃ g₁ ∈ (⊤ : Subgroup (FreeGroup S)),
      ∃ g₂ ∈ (⊤ : Subgroup (FreeGroup S)), ⁅g₁, g₂⁆ = g}),
      (((⟨w, hS ▸ hw⟩ : commutator (FreeGroup S)) : HopfCover S)) ∈
        commutator (HopfCover S) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨f₁, -, f₂, -, rfl⟩ := hw
      obtain ⟨d₁, hd₁, he₁⟩ := exists_mem_commutator_hopfEval_eq (hopfEval S f₁)
      obtain ⟨d₂, hd₂, he₂⟩ := exists_mem_commutator_hopfEval_eq (hopfEval S f₂)
      have hr₁ : d₁⁻¹ * f₁ ∈ hopfRelations S := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, he₁, inv_mul_cancel]
      have hr₂ : d₂⁻¹ * f₂ ∈ hopfRelations S := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, he₂, inv_mul_cancel]
      have hf₁ : π f₁ = π d₁ * π (d₁⁻¹ * f₁) := by rw [← map_mul, mul_inv_cancel_left]
      have hf₂ : π f₂ = π d₂ * π (d₂⁻¹ * f₂) := by rw [← map_mul, mul_inv_cancel_left]
      have hπ : π ⁅f₁, f₂⁆ = π ⁅d₁, d₂⁆ := by
        rw [map_commutatorElement, map_commutatorElement, hf₁, hf₂,
          CFSG.SectionRank.commutatorElement_mul_mem_center _ _
            (mk_mem_center_of_mem_hopfRelations hr₁) (mk_mem_center_of_mem_hopfRelations hr₂)]
      have heq : (((⟨⁅f₁, f₂⁆, commutator_mem_commutator (mem_top f₁) (mem_top f₂)⟩ :
          commutator (FreeGroup S)) : HopfCover S)) =
          (((⟨⁅d₁, d₂⁆, commutator_mem_commutator (mem_top d₁) (mem_top d₂)⟩ :
            commutator (FreeGroup S)) : HopfCover S)) := by
        apply QuotientGroup.eq.mpr
        have h' : ⁅f₁, f₂⁆⁻¹ * ⁅d₁, d₂⁆ ∈ hopfCommutatorRelations S := QuotientGroup.eq.mp hπ
        exact h'
      rw [show (⟨⁅f₁, f₂⁆, hS ▸ subset_closure ⟨f₁, mem_top f₁, f₂, mem_top f₂, rfl⟩⟩ :
          commutator (FreeGroup S)) = ⟨⁅f₁, f₂⁆, commutator_mem_commutator (mem_top f₁)
            (mem_top f₂)⟩ from rfl, heq]
      have hd : ((⟨⁅d₁, d₂⁆, commutator_mem_commutator (mem_top d₁) (mem_top d₂)⟩ :
          commutator (FreeGroup S)) : HopfCover S) =
          ⁅(((⟨d₁, hd₁⟩ : commutator (FreeGroup S)) : HopfCover S)),
            (((⟨d₂, hd₂⟩ : commutator (FreeGroup S)) : HopfCover S))⁆ := by
        rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply,
          ← map_commutatorElement]
        rfl
      rw [hd]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    | one => exact one_mem _
    | mul x y hx hy ihx ihy =>
      have := mul_mem ihx ihy
      exact this
    | inv x hx ih =>
      have := inv_mem ih
      exact this
  exact key w (hS ▸ hw)

end Basic

section Lift

variable {S : Type u} [Group S] {E : Type v} [Group E]

@[expose] def freeLift (q : E →* S) (hq : Function.Surjective q) : FreeGroup S →* E :=
  FreeGroup.lift (Function.surjInv hq)

theorem comp_freeLift (q : E →* S) (hq : Function.Surjective q) :
    q.comp (freeLift q hq) = hopfEval S :=
  FreeGroup.ext_hom _ _ fun s => by
    simp [freeLift, Function.surjInv_eq hq]

theorem freeLift_map_hopfCommutatorRelations (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) : (hopfCommutatorRelations S).map (freeLift q hq) = ⊥ := by
  rw [map_commutator, eq_bot_iff]
  have hR : (hopfRelations S).map (freeLift q hq) ≤ center E := by
    rintro _ ⟨r, hr, rfl⟩
    apply hker
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, comp_freeLift]
    exact hr
  calc ⁅(⊤ : Subgroup (FreeGroup S)).map (freeLift q hq),
        (hopfRelations S).map (freeLift q hq)⁆ ≤ ⁅(⊤ : Subgroup E), center E⁆ :=
        commutator_mono le_top hR
    _ = ⊥ := by
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer, coe_top, centralizer_univ]

@[expose] def hopfLift (q : E →* S) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    HopfCover S →* E :=
  QuotientGroup.lift _ ((freeLift q hq).comp (commutator (FreeGroup S)).subtype) fun d hd => by
    have h := Subgroup.mem_map_of_mem (freeLift q hq)
      (show (d : FreeGroup S) ∈ hopfCommutatorRelations S from hd)
    rw [freeLift_map_hopfCommutatorRelations q hq hker, mem_bot] at h
    exact h

@[simp]
theorem hopfLift_mk (q : E →* S) (hq : Function.Surjective q) (hker : q.ker ≤ center E)
    (d : commutator (FreeGroup S)) :
    hopfLift q hq hker (d : HopfCover S) = freeLift q hq d := rfl

theorem comp_hopfLift (q : E →* S) (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    q.comp (hopfLift q hq hker) = hopfCoverMap S := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective u
  change q (freeLift q hq d) = hopfEval S d
  rw [← MonoidHom.comp_apply, comp_freeLift]

theorem hopfCover_hom_ext [Group.IsPerfect S] (q : E →* S) (hker : q.ker ≤ center E)
    (h₁ h₂ : HopfCover S →* E) (e₁ : q.comp h₁ = hopfCoverMap S)
    (e₂ : q.comp h₂ = hopfCoverMap S) : h₁ = h₂ := by
  have hc : ∀ u, (h₁ u)⁻¹ * h₂ u ∈ center E := by
    intro u
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
      e₁, e₂, inv_mul_cancel]
  have hcomm : commutator (HopfCover S) ≤ MonoidHom.eqLocus h₁ h₂ := by
    rw [_root_.commutator_def (HopfCover S), Subgroup.commutator_le]
    intro u _ v _
    change h₁ ⁅u, v⁆ = h₂ ⁅u, v⁆
    rw [map_commutatorElement, map_commutatorElement]
    have hu : h₂ u = h₁ u * ((h₁ u)⁻¹ * h₂ u) := by group
    have hv : h₂ v = h₁ v * ((h₁ v)⁻¹ * h₂ v) := by group
    rw [hu, hv, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hc u) (hc v)]
  have : Group.IsPerfect (HopfCover S) := hopfCover_isPerfect
  rw [Group.IsPerfect.commutator_eq_top (G := HopfCover S)] at hcomm
  refine MonoidHom.ext fun u => ?_
  exact hcomm (mem_top u)

theorem hopfLift_surjective [Group.IsPerfect E] (q : E →* S) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) : Function.Surjective (hopfLift q hq hker) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := E),
    _root_.commutator_def, Subgroup.commutator_le]
  intro e₁ _ e₂ _
  set t := freeLift q hq
  have hdec : ∀ e : E, (t (FreeGroup.of (q e)))⁻¹ * e ∈ center E := by
    intro e
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, comp_freeLift]
    simp
  have he : ∀ e : E, e = t (FreeGroup.of (q e)) * ((t (FreeGroup.of (q e)))⁻¹ * e) := by
    intro e
    group
  rw [he e₁, he e₂, CFSG.SectionRank.commutatorElement_mul_mem_center _ _ (hdec e₁) (hdec e₂),
    ← map_commutatorElement]
  exact ⟨((⟨⁅FreeGroup.of (q e₁), FreeGroup.of (q e₂)⁆,
    commutator_mem_commutator (mem_top _) (mem_top _)⟩ : commutator (FreeGroup S)) :
      HopfCover S), rfl⟩

theorem map_hopfMultiplier_hopfLift [Group.IsPerfect E] (q : E →* S)
    (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    (hopfMultiplier S).map (hopfLift q hq hker) = q.ker := by
  apply le_antisymm
  · rintro _ ⟨m, hm, rfl⟩
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, comp_hopfLift]
    exact hm
  · intro c hc
    obtain ⟨u, rfl⟩ := hopfLift_surjective q hq hker c
    refine Subgroup.mem_map.mpr ⟨u, ?_, rfl⟩
    change hopfCoverMap S u = 1
    rw [← comp_hopfLift q hq hker, MonoidHom.comp_apply]
    exact hc

end Lift

section Main

variable {S : Type u} [Group S] [Group.IsPerfect S]

theorem perfect_central_kernel_quotient_of_hopf_multiplier [Finite S] {E : Type v} [Group E]
    [Finite E] [Group.IsPerfect E] (p : E →* S) (hp : Function.Surjective p)
    (hC : p.ker ≤ center E) :
    (IsPerfectCentralExtension S (hopfCoverMap S) ∧
      ∀ (E' : Type v) [Group E'] (q : E' →* S), IsCentralExtension S q →
        ∃! h : HopfCover S →* E', q.comp h = hopfCoverMap S) ∧
    ∃ h : HopfCover S →* E, p.comp h = hopfCoverMap S ∧
      (∀ h' : HopfCover S →* E, p.comp h' = hopfCoverMap S → h' = h) ∧
      Function.Surjective h ∧ (hopfMultiplier S).map h = p.ker ∧
      ∃ e : hopfMultiplier S ⧸ (h.comp (hopfMultiplier S).subtype).ker ≃* p.ker,
        ∀ m : hopfMultiplier S, (e (m : hopfMultiplier S ⧸ (h.comp
          (hopfMultiplier S).subtype).ker) : E) = h m := by
  refine ⟨⟨⟨⟨hopfCoverMap_surjective, hopfMultiplier_le_center⟩,
    (Group.isPerfect_def.mp hopfCover_isPerfect)⟩, fun E' _ q hq => ?_⟩, ?_⟩
  · exact ⟨hopfLift q hq.1 hq.2, comp_hopfLift q hq.1 hq.2,
      fun h hh => hopfCover_hom_ext q hq.2 h _ hh (comp_hopfLift q hq.1 hq.2)⟩
  · set h := hopfLift p hp hC with hh
    have hmap := map_hopfMultiplier_hopfLift p hp hC
    refine ⟨h, comp_hopfLift p hp hC,
      fun h' hh' => hopfCover_hom_ext p hC h' h hh' (comp_hopfLift p hp hC),
      hopfLift_surjective p hp hC, hmap, ?_⟩
    have hrange : (h.comp (hopfMultiplier S).subtype).range = p.ker := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, ← hmap]
    refine ⟨(QuotientGroup.quotientKerEquivRange _).trans (MulEquiv.subgroupCongr hrange),
      fun m => rfl⟩

end Main

end CFSG.RankThree.PerfectCover
