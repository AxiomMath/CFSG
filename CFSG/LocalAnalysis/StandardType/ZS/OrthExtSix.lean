module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtLemmas
public import CFSG.LocalAnalysis.StandardType.ZS.ReflAxis
public import CFSG.LocalAnalysis.StandardType.GGSpFrameRefl
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces

public section

namespace CFSG.StandardType.ZS

open CFSG.HardMathSupport.Kantor79 (mem_movedSpace_of_apply_eq_neg)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def IsCentralizingSplit (p : ℕ) [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (G H B : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) : Prop :=
  B ≤ G ∧ ReflGen p B ∧ SplitSupport B (Module.finrank (ZMod p) U - 1) ∧
    B ≤ Subgroup.centralizer ({h} : Set (U ≃ₗ[ZMod p] U)) ∧
    reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ≤ B

@[expose] def IsCyclicRootTriple (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (r : Fin 3 → U ≃ₗ[ZMod p] U) (e : Fin 3 → U)
    (s : U ≃ₗ[ZMod p] U) : Prop :=
  (∀ i, r i ∈ H ∧ IsRefl p (r i) ∧ r i (e i) = -e i) ∧ (∀ i j, r i * r j = r j * r i) ∧
    LinearIndependent (ZMod p) e ∧ s ∈ H ∧ ∀ i, s (e i) = e (i + 1)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

section TheoremOne

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

private theorem closure_insert_le_centralizer_reflSubgroupIn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hb' : IsRefl p b)
    (hhb : h * b = b * h) :
    Subgroup.closure (insert b (reflSubgroupIn p H
      (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))) ≤
      Subgroup.centralizer ({h} : Set (U ≃ₗ[ZMod p] U)) := by
  have hHh : reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ≤
      Subgroup.centralizer ({h} : Set (U ≃ₗ[ZMod p] U)) := by
    rw [reflSubgroupIn]
    refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨hrH, hrr, hrW⟩
    have hrW' : HardMathSupport.Kantor79.movedSpace r ≤
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
      rw [HardMathSupport.Kantor79.movedSpace]
      rintro x ⟨v, rfl⟩
      exact hrW v
    change r ∈ Subgroup.centralizer ({h} : Set (U ≃ₗ[ZMod p] U))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_movedSpace_le_ker hp hG (hHG hh) (hHG hrH) hrr hrW').symm
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with rfl | hx
  · change x ∈ Subgroup.centralizer ({h} : Set (U ≃ₗ[ZMod p] U))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hhb.symm
  · exact hHh hx

private theorem commutatorSpace_closure_insert_reflSubgroupIn_le_ker (_hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U} (hh' : IsRefl p h)
    (hb' : IsRefl p b) (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H)
    (hh : h ∈ H) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  have hVb : HardMathSupport.Kantor79.movedSpace b ≤ W := by
    have hne : HardMathSupport.Kantor79.movedSpace h ≠ HardMathSupport.Kantor79.movedSpace b :=
      fun heq => hbH (heq ▸ HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh)
    intro v hv
    have hfix := IsRefl.apply_eq_self_of_commute hh' hb' hhb hne v hv
    simpa [hW, LinearMap.mem_ker, sub_eq_zero] using hfix
  let x : {g : U ≃ₗ[ZMod p] U // g = b ∨ g ∈ Hh} → U ≃ₗ[ZMod p] U := Subtype.val
  have hrange : Subgroup.closure (Set.range x) =
      Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, rfl⟩
      change (g : U ≃ₗ[ZMod p] U) ∈
        Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U)))
      rcases g.2 with hg | hg
      · have hgb : (g : U ≃ₗ[ZMod p] U) = b := hg
        rw [hgb]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      rcases hg with hgb | hg
      · exact Subgroup.subset_closure ⟨⟨g, Or.inl hgb⟩, rfl⟩
      · exact Subgroup.subset_closure ⟨⟨g, Or.inr hg⟩, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace]
  refine iSup_le ?_
  rintro ⟨g, hg⟩
  rcases hg with rfl | hg
  · exact hVb
  · exact (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hg).trans
      (commutatorSpace_reflSubgroupIn_le H W)

private theorem reflSubgroupIn_le_fixing_movedSpace (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) :
    reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ≤
      fixingSubgroup (U ≃ₗ[ZMod p] U) (HardMathSupport.Kantor79.movedSpace h : Set U) := by
  rw [reflSubgroupIn]
  refine (Subgroup.closure_le _).mpr ?_
  rintro r ⟨hrH, hrr, hrW⟩
  change r ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
    (HardMathSupport.Kantor79.movedSpace h : Set U)
  rw [mem_fixingSubgroup_iff]
  have hrW' : HardMathSupport.Kantor79.movedSpace r ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    rw [HardMathSupport.Kantor79.movedSpace]
    rintro x ⟨v, rfl⟩
    exact hrW v
  have hcomm : h * r = r * h :=
    commute_of_movedSpace_le_ker hp hG (hHG hh) (hHG hrH) hrr hrW'
  intro v hv
  have hne : HardMathSupport.Kantor79.movedSpace r ≠ HardMathSupport.Kantor79.movedSpace h :=
    fun heq => IsRefl.not_movedSpace_le_ker_sub_one hp hh' (heq ▸ hrW')
  exact IsRefl.apply_eq_self_of_commute hrr hh' hcomm.symm hne v hv

private theorem movedSpace_inf_commutatorSpace_reflSubgroupIn_eq_bot
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.movedSpace b ⊓ HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) = ⊥ := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  have hVHh_le_VH : HardMathSupport.Kantor79.commutatorSpace Hh ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [commutatorSpace_le_iff]
    intro k hk v
    exact Submodule.subset_span ⟨k, reflSubgroupIn_le H W hk, v, rfl⟩
  have hVb_not_le : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace Hh := fun hle => hbH (hle.trans hVHh_le_VH)
  have hinf : HardMathSupport.Kantor79.movedSpace b ⊓
      HardMathSupport.Kantor79.commutatorSpace Hh = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    by_contra hx0
    have hspan : HardMathSupport.Kantor79.movedSpace b = ZMod p ∙ x := by
      have hle : ZMod p ∙ x ≤ HardMathSupport.Kantor79.movedSpace b :=
        (Submodule.span_singleton_le_iff_mem x _).mpr hx.1
      have hfin : Module.finrank (ZMod p) (ZMod p ∙ x) =
          Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) := by
        rw [finrank_span_singleton hx0]
        exact (show Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1
          from hb'.2).symm
      exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
    exact hVb_not_le (hspan ▸ (Submodule.span_singleton_le_iff_mem x _).mpr hx.2)
  exact hinf

private theorem finrank_movedSpace_sup_reflSubgroupIn [Module.Finite (ZMod p) U]
    {h b : U ≃ₗ[ZMod p] U} (hb' : IsRefl p b)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hinf : HardMathSupport.Kantor79.movedSpace b ⊓ HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) = ⊥) :
    Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace b ⊔
      HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) =
      Module.finrank (ZMod p) U - 1 := by
  have hdimVb : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 := hb'.2
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  have hdimsup : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace b ⊔
      HardMathSupport.Kantor79.commutatorSpace Hh) =
      Module.finrank (ZMod p) U - 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.movedSpace b) (HardMathSupport.Kantor79.commutatorSpace Hh)
    rw [hinf, finrank_bot, hdimVb] at h
    omega
  exact hdimsup

private theorem movedSpace_sup_reflSubgroupIn_le_commutatorSpace_closure_insert
    {h b : U ≃ₗ[ZMod p] U} :
    HardMathSupport.Kantor79.movedSpace b ⊔ HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ≤
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U)))) := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVbB : HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace B :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (Set.mem_insert _ _))
  have hHhB : HardMathSupport.Kantor79.commutatorSpace Hh ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    rw [commutatorSpace_le_iff]
    intro k hk v
    exact Submodule.subset_span
      ⟨k, Subgroup.subset_closure (Set.mem_insert_of_mem _ hk), v, rfl⟩
  have hsup_le : HardMathSupport.Kantor79.movedSpace b ⊔
      HardMathSupport.Kantor79.commutatorSpace Hh ≤ HardMathSupport.Kantor79.commutatorSpace B :=
    sup_le hVbB hHhB
  exact sup_le hVbB hHhB

private theorem commutatorSpace_closure_insert_reflSubgroupIn_eq_ker (hp : p ≠ 2)
    [Module.Finite (ZMod p) U]
    {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVB_le : HardMathSupport.Kantor79.commutatorSpace B ≤ W :=
    commutatorSpace_closure_insert_reflSubgroupIn_le_ker hp hh' hb' hhb hbH hh
  have hVb : HardMathSupport.Kantor79.movedSpace b ≤ W := by
    have hne : HardMathSupport.Kantor79.movedSpace h ≠ HardMathSupport.Kantor79.movedSpace b :=
      fun heq => hbH (heq ▸ HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh)
    intro v hv
    have hfix := IsRefl.apply_eq_self_of_commute hh' hb' hhb hne v hv
    simpa [hW, LinearMap.mem_ker, sub_eq_zero] using hfix
  have hVHh : HardMathSupport.Kantor79.commutatorSpace Hh ≤ W :=
    commutatorSpace_reflSubgroupIn_le H W
  have hinf := movedSpace_inf_commutatorSpace_reflSubgroupIn_eq_bot
    (H := H) (h := h) hb' hbH
  have hsup_le := movedSpace_sup_reflSubgroupIn_le_commutatorSpace_closure_insert (H := H) (h := h)
    (b := b)
  have hdimW := IsRefl.finrank_ker_sub_one_add_one hh'
  have hdimVb : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 := hb'.2
  have hdimsup := finrank_movedSpace_sup_reflSubgroupIn (H := H) (h := h) hb' hdim hinf
  have hdimsup' : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace b ⊔
      HardMathSupport.Kantor79.commutatorSpace Hh) = Module.finrank (ZMod p) U - 1 := hdimsup
  have hdimW' : Module.finrank (ZMod p) W = Module.finrank (ZMod p) U - 1 := by
    rw [hW]
    omega
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
      Module.finrank (ZMod p) W := by
    have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) ≤
        Module.finrank (ZMod p) W := Submodule.finrank_mono hVB_le
    have h2 : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.movedSpace b ⊔
        HardMathSupport.Kantor79.commutatorSpace Hh) ≤
        Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) :=
      Submodule.finrank_mono hsup_le
    omega
  exact Submodule.eq_of_le_of_finrank_eq hVB_le hfin

private theorem movedSpace_le_centralizerSpace_closure_insert_reflSubgroupIn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    HardMathSupport.Kantor79.movedSpace h ≤
      centralizerSpace (Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U)))) := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVb : HardMathSupport.Kantor79.movedSpace b ≤ W := by
    have hne : HardMathSupport.Kantor79.movedSpace h ≠ HardMathSupport.Kantor79.movedSpace b :=
      fun heq => hbH (heq ▸ HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh)
    intro v hv
    have hfix := IsRefl.apply_eq_self_of_commute hh' hb' hhb hne v hv
    simpa [hW, LinearMap.mem_ker, sub_eq_zero] using hfix
  have hb_fix : b ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace h : Set U) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hne : HardMathSupport.Kantor79.movedSpace b ≠ HardMathSupport.Kantor79.movedSpace h :=
      fun heq => IsRefl.not_movedSpace_le_ker_sub_one hp hh' (heq ▸ hVb)
    exact IsRefl.apply_eq_self_of_commute hb' hh' hhb.symm hne v hv
  have hHh_fix : Hh ≤ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace h : Set U) :=
    reflSubgroupIn_le_fixing_movedSpace hp hG hHG hh hh'
  have hB_fix : B ≤ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace h : Set U) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rcases hg with rfl | hg
    · exact hb_fix
    · exact hHh_fix hg
  intro v hv
  rw [mem_centralizerSpace]
  intro g hg
  have hgfix : g ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace h : Set U) := hB_fix hg
  exact (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp hgfix v hv

private theorem splitSupport_closure_insert_reflSubgroupIn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hirr : IrredOnSection (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) ⊥ (HardMathSupport.Kantor79.commutatorSpace
          (Subgroup.closure (insert b (reflSubgroupIn p H
            (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
              Set (U ≃ₗ[ZMod p] U)))))) :
    SplitSupport (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) (Module.finrank (ZMod p) U - 1) := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set B := Subgroup.closure (insert b
    (reflSubgroupIn p H W : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVBeq : HardMathSupport.Kantor79.commutatorSpace B = W :=
    commutatorSpace_closure_insert_reflSubgroupIn_eq_ker hp hh hh' hb' hhb hbH hdim
  have hBgen : ReflGen p B := ReflGen.closure_insert_reflSubgroupIn hb' W
  have hVBfix : HardMathSupport.Kantor79.movedSpace h ≤ centralizerSpace B :=
    movedSpace_le_centralizerSpace_closure_insert_reflSubgroupIn hp hG hHG hh hh' hb' hhb hbH
  have hsupW : W ⊔ HardMathSupport.Kantor79.movedSpace h = ⊤ := by
    rw [hW, IsRefl.movedSpace_eq_ker_add_one hp hh']
    exact (IsRefl.isCompl_ker_sub_one_ker_add_one hp hh').sup_eq_top
  have hinf : HardMathSupport.Kantor79.commutatorSpace B ⊓ centralizerSpace B = ⊥ :=
    commutatorSpace_inf_centralizerSpace_eq_bot hp hBgen hirr
  have hsup : HardMathSupport.Kantor79.commutatorSpace B ⊔ centralizerSpace B = ⊤ := by
    refine le_antisymm le_top ?_
    calc (⊤ : Submodule (ZMod p) U) = W ⊔ HardMathSupport.Kantor79.movedSpace h := hsupW.symm
      _ = HardMathSupport.Kantor79.commutatorSpace B ⊔ HardMathSupport.Kantor79.movedSpace h := by
        rw [hVBeq]
      _ ≤ HardMathSupport.Kantor79.commutatorSpace B ⊔ centralizerSpace B :=
        sup_le_sup_left hVBfix _
  have hdimW := IsRefl.finrank_ker_sub_one_add_one hh'
  have hdimB : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
      Module.finrank (ZMod p) U - 1 := by
    rw [hVBeq, hW]
    omega
  exact ⟨IsCompl.of_eq hinf hsup, hdimB, hirr⟩

end TheoremOne
theorem isCentralizingSplit_of_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1)) {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H)
    (hh' : IsRefl p h) (hb : b ∈ G) (hb' : IsRefl p b) (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hirr : IrredOnSection (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))))
      ⊥ (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U)))))) :
    IsCentralizingSplit p G H (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))))
      h := by
  have hdimH := hH.2.1
  have hBG : Subgroup.closure (insert b (reflSubgroupIn p H
      (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))) ≤ G := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | hx
    · exact hb
    · exact hHG (reflSubgroupIn_le H _ hx)
  have hBgen : ReflGen p (Subgroup.closure (insert b (reflSubgroupIn p H
      (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U)))) :=
    ReflGen.closure_insert_reflSubgroupIn hb' _
  have hsplit := splitSupport_closure_insert_reflSubgroupIn hp hG hHG hh hh' hb' hhb hbH
    hdim hirr
  have hcent := closure_insert_le_centralizer_reflSubgroupIn hp hG hHG hh hb' hhb
  exact ⟨hBG, hBgen, hsplit, hcent,
    fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)⟩

private theorem invariants_of_isCentralizingSplit (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hB : IsCentralizingSplit p G H B h) (hh : IsRefl p h) :
    (∀ w ∈ HardMathSupport.Kantor79.commutatorSpace B,
        (h : U →ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace B) ∧
      (∀ b ∈ B, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace B,
        (b : U →ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace B) ∧
      (∀ b ∈ B, ∀ x ∈ HardMathSupport.Kantor79.movedSpace h,
        (b : U →ₗ[ZMod p] U) x ∈ HardMathSupport.Kantor79.movedSpace h) := by
  obtain ⟨-, -, -, hBcent, -⟩ := hB
  have hhNormal : h ∈ Subgroup.normalizer (B : Set (U ≃ₗ[ZMod p] U)) :=
    Subgroup.centralizer_le_normalizer (B : Set (U ≃ₗ[ZMod p] U)) (by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBcent hb))
  have hVhInv : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace B,
      (h : U →ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace B := by
    intro w hw
    have hmap := map_commutatorSpace_of_mem_normalizer (H := B) hhNormal
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := (h : U →ₗ[ZMod p] U)) hw
  have hBV : ∀ b ∈ B, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace B,
      (b : U →ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace B := by
    intro b hb w hw
    have hmap := map_commutatorSpace_of_mem_normalizer (H := B) (Subgroup.le_normalizer hb)
    rw [← hmap]
    exact Submodule.mem_map_of_mem (f := (b : U →ₗ[ZMod p] U)) hw
  have hBmoved : ∀ b ∈ B, ∀ x ∈ HardMathSupport.Kantor79.movedSpace h,
      (b : U →ₗ[ZMod p] U) x ∈ HardMathSupport.Kantor79.movedSpace h := by
    intro b hb x hx
    have hcomm : b * h = h * b := Subgroup.mem_centralizer_singleton_iff.mp (hBcent hb)
    have hcomm' : ∀ y, (h : U →ₗ[ZMod p] U) ((b : U →ₗ[ZMod p] U) y) =
        (b : U →ₗ[ZMod p] U) ((h : U →ₗ[ZMod p] U) y) := by
      intro y
      have h : (h * b) y = (b * h) y := by rw [hcomm]
      simpa [LinearEquiv.mul_apply] using h
    rw [IsRefl.movedSpace_eq_ker_add_one hp hh] at hx ⊢
    refine LinearMap.mem_ker.mpr ?_
    rw [LinearMap.add_apply, Module.End.one_apply]
    have hx' : (h : U →ₗ[ZMod p] U) x + x = 0 := by
      simpa [LinearMap.add_apply, Module.End.one_apply] using hx
    rw [hcomm', ← map_add, hx', map_zero]
  exact ⟨hVhInv, hBV, hBmoved⟩

private theorem movedSpace_inf_commutatorSpace_eq_bot (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (h3 : 3 ≤ Module.finrank (ZMod p) U)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hB : IsCentralizingSplit p G H B h) (hh : IsRefl p h) :
    HardMathSupport.Kantor79.commutatorSpace B ⊓
      HardMathSupport.Kantor79.movedSpace h = ⊥ := by
  have hB' := hB
  obtain ⟨-, -, hsplit, -, -⟩ := hB'
  obtain ⟨-, hdimB, hbirr⟩ := hsplit
  obtain ⟨hVhInv, hBV, hBmoved⟩ := invariants_of_isCentralizingSplit hp hB hh
  let V : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace B
  let X : Submodule (ZMod p) U := V ⊓ HardMathSupport.Kantor79.movedSpace h
  have hXinv : ∀ b ∈ B, ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X := by
    intro b hb x hx
    exact ⟨hBV b hb x hx.1, hBmoved b hb x hx.2⟩
  have hXbot : X = ⊥ := by
    rcases hbirr X bot_le inf_le_left hXinv with hX | hX
    · exact hX
    · exfalso
      have hle : V ≤ HardMathSupport.Kantor79.movedSpace h := by
        intro v hv
        have hvX : v ∈ X := by rw [hX]; exact hv
        exact hvX.2
      have hfinle : Module.finrank (ZMod p) V ≤
          Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) :=
        Submodule.finrank_mono hle
      have hdimV : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 := by
        simpa [V] using hdimB
      rw [show Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 from hh.2]
        at hfinle
      omega
  simpa [X, V] using hXbot

private theorem commutatorSpace_eq_ker_of_isCentralizingSplit_ker (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (h3 : 3 ≤ Module.finrank (ZMod p) U)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hB : IsCentralizingSplit p G H B h) (hh : IsRefl p h) :
    HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  have hB' := hB
  obtain ⟨-, -, hsplit, -, -⟩ := hB'
  obtain ⟨-, hdimB, -⟩ := hsplit
  obtain ⟨hVhInv, -, -⟩ := invariants_of_isCentralizingSplit hp hB hh
  have hXbot := movedSpace_inf_commutatorSpace_eq_bot hp h3 hB hh
  let V : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace B
  have hbot : V ⊓ HardMathSupport.Kantor79.movedSpace h = ⊥ := by
    simpa [V] using hXbot
  have hdecomp : V = (V ⊓ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) ⊔
      (V ⊓ HardMathSupport.Kantor79.movedSpace h) := by
    have h := eq_sup_inf_ker_sub_one_ker_add_one (ZMod.prime_ne_zero p 2 hp) hh.1 hVhInv
    rw [← IsRefl.movedSpace_eq_ker_add_one hp hh] at h
    simpa [V] using h
  have hVeq : V = V ⊓ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    simpa [hbot] using hdecomp
  have hle : V ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    hVeq.le.trans inf_le_right
  have hdim : Module.finrank (ZMod p) V =
      Module.finrank (ZMod p) (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) := by
    have hdimV : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 := by
      simpa [V] using hdimB
    have hk := IsRefl.finrank_ker_sub_one_add_one hh
    omega
  simpa [V] using Submodule.eq_of_le_of_finrank_eq hle hdim

private theorem centralizerSpace_eq_movedSpace (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (h3 : 3 ≤ Module.finrank (ZMod p) U)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hB : IsCentralizingSplit p G H B h) (hh : IsRefl p h)
    (hVeq : HardMathSupport.Kantor79.commutatorSpace B =
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
    centralizerSpace B = HardMathSupport.Kantor79.movedSpace h := by
  have hB' := hB
  obtain ⟨-, -, hsplit, hBcent, -⟩ := hB'
  obtain ⟨hcompl, hdimB, -⟩ := hsplit
  obtain ⟨-, -, hBmoved⟩ := invariants_of_isCentralizingSplit hp hB hh
  let V : Submodule (ZMod p) U := HardMathSupport.Kantor79.commutatorSpace B
  let C : Submodule (ZMod p) U := centralizerSpace B
  have hcompl' : IsCompl V C := hcompl
  have hdimV : Module.finrank (ZMod p) V = Module.finrank (ZMod p) U - 1 := hdimB
  have hdisj : V ⊓ HardMathSupport.Kantor79.movedSpace h = ⊥ := by
    rw [show V = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) from by simpa [V] using hVeq,
      IsRefl.movedSpace_eq_ker_add_one hp hh]
    exact (IsRefl.isCompl_ker_sub_one_ker_add_one hp hh).inf_eq_bot
  have hmoved_le_C : HardMathSupport.Kantor79.movedSpace h ≤ C := by
    intro x hx
    rw [mem_centralizerSpace]
    intro b hb
    have hbx : (b : U →ₗ[ZMod p] U) x ∈ HardMathSupport.Kantor79.movedSpace h :=
      hBmoved b hb x hx
    have hdiffV : (b : U →ₗ[ZMod p] U) x - x ∈ V := by
      simpa [V] using (commutatorSpace_le_iff (H := B) (W :=
        HardMathSupport.Kantor79.commutatorSpace B)).mp le_rfl b hb x
    have hdiffMoved : (b : U →ₗ[ZMod p] U) x - x ∈
        HardMathSupport.Kantor79.movedSpace h :=
      (HardMathSupport.Kantor79.movedSpace h).sub_mem hbx hx
    have hzero : (b : U →ₗ[ZMod p] U) x - x = 0 := by
      have hmem : (b : U →ₗ[ZMod p] U) x - x ∈
          V ⊓ HardMathSupport.Kantor79.movedSpace h := ⟨hdiffV, hdiffMoved⟩
      rw [hdisj] at hmem
      exact hmem
    exact sub_eq_zero.mp hzero
  have hCdim : Module.finrank (ZMod p) C = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl'
    omega
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) =
      Module.finrank (ZMod p) C := by
    rw [show Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 from hh.2,
      hCdim]
  simpa [C] using (Submodule.eq_of_le_of_finrank_eq hmoved_le_C hfin).symm

theorem commutatorSpace_eq_ker_of_isCentralizingSplit (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}
    (hB : IsCentralizingSplit p G H B h) (hh : IsRefl p h) :
    HardMathSupport.Kantor79.commutatorSpace B = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ∧
      centralizerSpace B = HardMathSupport.Kantor79.movedSpace h := by
  have hVeq := commutatorSpace_eq_ker_of_isCentralizingSplit_ker hp h3 hB hh
  exact ⟨hVeq, centralizerSpace_eq_movedSpace hp h3 hB hh hVeq⟩

private theorem map_commutatorSpace_closure_insert_eq_self_of_le
    [Module.Finite (ZMod p) U] {b : U ≃ₗ[ZMod p] U}
    (hle : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H := by
  set V := HardMathSupport.Kantor79.commutatorSpace H with hV
  intro g hg
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
  · rintro x (hxb | hx)
    · rw [hxb]
      have hmaple : V.map (b : U →ₗ[ZMod p] U) ≤ V := by
        rintro w ⟨v, hv, rfl⟩
        have hsub : (b : U →ₗ[ZMod p] U) v - v ∈ V := hle ⟨v, rfl⟩
        have hsum : (b : U →ₗ[ZMod p] U) v = ((b : U →ₗ[ZMod p] U) v - v) + v := by abel
        rw [hsum]
        exact V.add_mem hsub hv
      exact Submodule.eq_of_le_of_finrank_eq hmaple (LinearEquiv.finrank_map_eq b V)
    · exact map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hx)
  · simp
  · intro x y hx hy ihx ihy
    rw [show ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
      (x : U →ₗ[ZMod p] U).comp (y : U →ₗ[ZMod p] U) from rfl,
      Submodule.map_comp, ihy, ihx]
  · intro x hx ih
    have hle' : V.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤ V := by
      rw [Submodule.map_le_iff_le_comap]
      intro w hw
      have hw' : w ∈ V.map (x : U →ₗ[ZMod p] U) := by rw [ih]; exact hw
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hw'
      rw [← hvx]
      simpa using hv
    exact Submodule.eq_of_le_of_finrank_eq hle' (LinearEquiv.finrank_map_eq x⁻¹ V)

private theorem false_of_invariant_commutatorSpace
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U}
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b)
    (hinv : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
        g w ∈ HardMathSupport.Kantor79.commutatorSpace H) : False := by
  obtain ⟨hh, hh', hb, hb', hhb, hirr⟩ := hpair
  obtain ⟨-, hdimH, -⟩ := hH
  have hVne : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro hbot
    have hVh : HardMathSupport.Kantor79.movedSpace h ≤
        HardMathSupport.Kantor79.commutatorSpace H :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
    have hzero : HardMathSupport.Kantor79.movedSpace h ≤ ⊥ := hbot ▸ hVh
    have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 0 := by
      rw [le_bot_iff.mp hzero, finrank_bot]
    have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    omega
  have hUpos : 0 < Module.finrank (ZMod p) U := by
    have hle : HardMathSupport.Kantor79.movedSpace h ≤ (⊤ : Submodule (ZMod p) U) := le_top
    have hfin := Submodule.finrank_mono hle
    rw [finrank_top] at hfin
    have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    omega
  rcases hirr (HardMathSupport.Kantor79.commutatorSpace H) bot_le le_top hinv with hbot | htop
  · exact hVne hbot
  · have h1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U := by rw [htop, finrank_top]
    omega

private theorem not_movedSpace_le_commutatorSpace_of_isCommIrredPair
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U}
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b) :
    ¬ HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  intro hle
  have hmap := map_commutatorSpace_closure_insert_eq_self_of_le (H := H) (b := b) hle
  have hVHinv : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
        g w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro g hg w hw
    have hmem : (g : U →ₗ[ZMod p] U) w ∈
        (HardMathSupport.Kantor79.commutatorSpace H).map (g : U →ₗ[ZMod p] U) :=
      Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hw
    rwa [hmap g hg] at hmem
  exact false_of_invariant_commutatorSpace hH hpair hVHinv

private theorem commutatorSpace_reflSubgroupIn_eq_inf_ker (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U) :
    HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) =
      HardMathSupport.Kantor79.commutatorSpace H ⊓
        LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  obtain ⟨-, hdimH, -⟩ := hH
  have hVHh_le_W : HardMathSupport.Kantor79.commutatorSpace Hh ≤ W :=
    commutatorSpace_reflSubgroupIn_le H W
  have hVHh_le_VH : HardMathSupport.Kantor79.commutatorSpace Hh ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [commutatorSpace_le_iff]
    intro k hk v
    exact Submodule.subset_span ⟨k, reflSubgroupIn_le H W hk, v, rfl⟩
  have hsup : HardMathSupport.Kantor79.commutatorSpace H ⊔ W = ⊤ := by
    have hcompl := IsRefl.isCompl_ker_sub_one_ker_add_one hp hh'
    have htop : HardMathSupport.Kantor79.movedSpace h ⊔ W = ⊤ := by
      rw [hW, IsRefl.movedSpace_eq_ker_add_one hp hh', sup_comm]
      exact hcompl.sup_eq_top
    exact top_le_iff.mp (htop ▸ sup_le_sup_right
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh) W)
  have hdimInf : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H ⊓ W) =
      Module.finrank (ZMod p) U - 2 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace H) W
    rw [hsup, finrank_top] at h
    have hWfin : Module.finrank (ZMod p) W + 1 = Module.finrank (ZMod p) U :=
      IsRefl.finrank_ker_sub_one_add_one hh'
    omega
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Hh) =
      Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace H ⊓ W) := by
    omega
  exact Submodule.eq_of_le_of_finrank_eq (le_inf hVHh_le_VH hVHh_le_W) hfin

private theorem commutatorSpace_eq_reflSubgroupIn_sup_movedSpace (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U) :
    HardMathSupport.Kantor79.commutatorSpace H =
      HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊔
        HardMathSupport.Kantor79.movedSpace h := by
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  have hVHh_eq := commutatorSpace_reflSubgroupIn_eq_inf_ker hp hh hh' hH hdim
  have hVHh_le_W : HardMathSupport.Kantor79.commutatorSpace Hh ≤ W :=
    commutatorSpace_reflSubgroupIn_le H W
  have hVHh_le_VH : HardMathSupport.Kantor79.commutatorSpace Hh ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [hVHh_eq]
    exact inf_le_left
  have hVh_le_VH : HardMathSupport.Kantor79.movedSpace h ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh
  have hinf : HardMathSupport.Kantor79.commutatorSpace Hh ⊓
      HardMathSupport.Kantor79.movedSpace h = ⊥ := by
    rw [hVHh_eq]
    have hdisj := (IsRefl.isCompl_ker_sub_one_ker_add_one hp hh').inf_eq_bot
    rw [← hW, ← IsRefl.movedSpace_eq_ker_add_one hp hh'] at hdisj
    calc HardMathSupport.Kantor79.commutatorSpace H ⊓ W ⊓ HardMathSupport.Kantor79.movedSpace h
        = HardMathSupport.Kantor79.commutatorSpace H ⊓
            (W ⊓ HardMathSupport.Kantor79.movedSpace h) := by rw [inf_assoc]
      _ = ⊥ := by rw [hdisj, inf_bot_eq]
  have hdimH := hH.2.1
  have hdimHh : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Hh) + 2 =
      Module.finrank (ZMod p) U := hdim
  have hdimv : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
  have hfin : Module.finrank (ZMod p) ↥(HardMathSupport.Kantor79.commutatorSpace Hh ⊔
      HardMathSupport.Kantor79.movedSpace h) =
      Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (HardMathSupport.Kantor79.commutatorSpace Hh) (HardMathSupport.Kantor79.movedSpace h)
    rw [hinf, finrank_bot, hdimv] at h
    omega
  exact (Submodule.eq_of_le_of_finrank_eq (sup_le hVHh_le_VH hVh_le_VH) hfin).symm

private theorem centralizerSpace_inf_movedSpace_eq_bot (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) :
    centralizerSpace H ⊓ HardMathSupport.Kantor79.movedSpace h = ⊥ := by
  have hW : centralizerSpace H ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    intro v hv
    rw [mem_centralizerSpace] at hv
    rw [LinearMap.mem_ker]
    change (h : U →ₗ[ZMod p] U) v - v = 0
    have hfixv : (h : U →ₗ[ZMod p] U) v = v := hv h hh
    rw [hfixv]
    abel
  have hdisj := (IsRefl.isCompl_ker_sub_one_ker_add_one hp hh').symm.inf_eq_bot
  rw [← IsRefl.movedSpace_eq_ker_add_one hp hh', inf_comm] at hdisj
  have hle : centralizerSpace H ⊓ HardMathSupport.Kantor79.movedSpace h ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ⊓
        HardMathSupport.Kantor79.movedSpace h :=
    le_inf (inf_le_left.trans hW) inf_le_right
  exact le_bot_iff.mp (hle.trans (le_of_eq hdisj))

private theorem sup_commutatorSpace_centralizerSpace_reflSubgroupIn_eq_top (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h : U ≃ₗ[ZMod p] U}
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hh : h ∈ H) (hh' : IsRefl p h)
    (hVh_cent : HardMathSupport.Kantor79.movedSpace h ≤ centralizerSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))))
    (hVH_cent_le : centralizerSpace H ≤ centralizerSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) :
    HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊔
      centralizerSpace (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) = ⊤ := by
  have hVH_eq := commutatorSpace_eq_reflSubgroupIn_sup_movedSpace hp hh hh' hH hdim
  have htop : HardMathSupport.Kantor79.commutatorSpace H ⊔ centralizerSpace H = ⊤ :=
    hH.1.sup_eq_top
  refine le_antisymm le_top ?_
  rw [← htop]
  refine sup_le ?_ ?_
  · rw [hVH_eq]
    exact sup_le le_sup_left (hVh_cent.trans le_sup_right)
  · exact hVH_cent_le.trans le_sup_right

private theorem centralizerSpace_reflSubgroupIn_eq_sup_movedSpace (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hirr₁ : IrredOnSection (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))))) :
    centralizerSpace (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) =
      centralizerSpace H ⊔ HardMathSupport.Kantor79.movedSpace h := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  have hfix : Hh ≤ fixingSubgroup (U ≃ₗ[ZMod p] U)
      (HardMathSupport.Kantor79.movedSpace h : Set U) :=
    reflSubgroupIn_le_fixing_movedSpace hp hG hHG hh hh'
  have hVH_cent_le : centralizerSpace H ≤ centralizerSpace Hh := by
    intro v hv
    rw [mem_centralizerSpace] at hv ⊢
    intro g hg
    exact hv g (reflSubgroupIn_le H _ hg)
  have hVh_cent : HardMathSupport.Kantor79.movedSpace h ≤ centralizerSpace Hh := by
    intro v hv
    rw [mem_centralizerSpace]
    intro g hg
    exact (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)).mp (hfix hg) v hv
  have hinfVH := centralizerSpace_inf_movedSpace_eq_bot hp hh hh'
  have hdimSum : Module.finrank (ZMod p) ↥(centralizerSpace H ⊔
      HardMathSupport.Kantor79.movedSpace h) = 2 := by
    have hsupdim := Submodule.finrank_sup_add_finrank_inf_eq (centralizerSpace H)
      (HardMathSupport.Kantor79.movedSpace h)
    rw [hinfVH, finrank_bot] at hsupdim
    have hsum := Submodule.finrank_add_eq_of_isCompl hH.1
    have hdimVH : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U - 1 := hH.2.1
    have hdimCent : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by omega
    have hdimVh : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := by
      show Module.finrank (ZMod p) (LinearMap.range ((h : U →ₗ[ZMod p] U) - 1)) = 1
      exact hh'.2
    omega
  have hinfHh : HardMathSupport.Kantor79.commutatorSpace Hh ⊓ centralizerSpace Hh = ⊥ :=
    commutatorSpace_inf_centralizerSpace_eq_bot hp (reflGen_reflSubgroupIn H _) hirr₁
  have hsupHh := sup_commutatorSpace_centralizerSpace_reflSubgroupIn_eq_top hp hH hdim hh hh'
    hVh_cent hVH_cent_le
  have hdimCentHh : Module.finrank (ZMod p) (centralizerSpace Hh) = 2 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl (IsCompl.of_eq hinfHh hsupHh)
    omega
  have hle : centralizerSpace H ⊔ HardMathSupport.Kantor79.movedSpace h ≤
      centralizerSpace Hh := sup_le hVH_cent_le hVh_cent
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private theorem mapsTo_closure_insert_of_mapsTo [Module.Finite (ZMod p) U]
    {b : U ≃ₗ[ZMod p] U} {W : Submodule (ZMod p) U}
    (hb : ∀ w ∈ W, (b : U →ₗ[ZMod p] U) w ∈ W)
    (hH : ∀ h ∈ H, ∀ w ∈ W, (h : U →ₗ[ZMod p] U) w ∈ W) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ W, (g : U →ₗ[ZMod p] U) w ∈ W := by
  intro g hg
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
  · rintro x (hxb | hx)
    · rw [hxb]
      exact hb
    · exact hH x hx
  · intro w hw
    simpa using hw
  · intro x y hx hy ihx ihy w hw
    exact ihx _ (ihy w hw)
  · intro x hx ih w hw
    have hmaple : W.map (x : U →ₗ[ZMod p] U) ≤ W := by
      rw [Submodule.map_le_iff_le_comap]
      intro z hz
      exact ih z hz
    have heq : W.map (x : U →ₗ[ZMod p] U) = W :=
      Submodule.eq_of_le_of_finrank_eq hmaple (LinearEquiv.finrank_map_eq x W)
    have hw' : w ∈ W.map (x : U →ₗ[ZMod p] U) := by rw [heq]; exact hw
    obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp hw'
    rw [← hvx]
    simpa using hv

private theorem mapsTo_commutatorSpace_of_eq_reflSubgroupIn (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h)
    (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    {X : Submodule (ZMod p) U}
    (hXeq : X = HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))))
    (hXinv : ∀ g ∈ Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U))), ∀ x ∈ X, g x ∈ X) :
    ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
        g w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  have hVH_eq := commutatorSpace_eq_reflSubgroupIn_sup_movedSpace hp hh hh' hH hdim
  have hVb : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) :=
    IsRefl.movedSpace_le_ker_of_commute hh' hb' hhb
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh) hbH
  have hbVh : ∀ v ∈ HardMathSupport.Kantor79.movedSpace h, (b : U →ₗ[ZMod p] U) v = v := by
    have hne : HardMathSupport.Kantor79.movedSpace b ≠ HardMathSupport.Kantor79.movedSpace h :=
      fun heq => IsRefl.not_movedSpace_le_ker_sub_one hp hh' (heq ▸ hVb)
    intro v hv
    exact IsRefl.apply_eq_self_of_commute hb' hh' hhb.symm hne v hv
  have hbB : b ∈ Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hbVHh : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace Hh,
      (b : U →ₗ[ZMod p] U) u ∈ HardMathSupport.Kantor79.commutatorSpace Hh := by
    intro u hu
    have hmem : (b : U →ₗ[ZMod p] U) u ∈ X := hXinv b hbB u (hXeq ▸ hu)
    exact hXeq ▸ hmem
  have hHh_le_VH : HardMathSupport.Kantor79.commutatorSpace Hh ≤
      HardMathSupport.Kantor79.commutatorSpace H := hVH_eq ▸ le_sup_left
  have hbVH : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace H,
      (b : U →ₗ[ZMod p] U) w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro w hw
    rw [hVH_eq] at hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hw
    rw [map_add, hbVh v hv]
    exact (HardMathSupport.Kantor79.commutatorSpace H).add_mem (hHh_le_VH (hbVHh u hu))
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh hv)
  exact mapsTo_closure_insert_of_mapsTo hbVH
    (fun h' hh' w hw => apply_mem_commutatorSpace hh' hw)

private theorem false_of_invariant_centralizerSpace
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U}
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b)
    (hpres : ∀ w ∈ centralizerSpace H, (b : U →ₗ[ZMod p] U) w ∈ centralizerSpace H) : False := by
  obtain ⟨hh, hh', hb, hb', hhb, hirr⟩ := hpair
  have hinv : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ centralizerSpace H, (g : U →ₗ[ZMod p] U) w ∈ centralizerSpace H :=
    mapsTo_closure_insert_of_mapsTo hpres (fun h' hh' w hw => by
      rw [show (h' : U →ₗ[ZMod p] U) w = w from mem_centralizerSpace.mp hw h' hh']
      exact hw)
  have hdimH := hH.2.1
  have hUpos : 0 < Module.finrank (ZMod p) U := by
    have hle := Submodule.finrank_mono
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh)
    have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    omega
  have hdimCent : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hH.1
    omega
  have hne : centralizerSpace H ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdimCent
    omega
  have hVHpos : 0 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) := by
    have hle := Submodule.finrank_mono
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hh)
    have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 := hh'.2
    omega
  have hUge2 : 2 ≤ Module.finrank (ZMod p) U := by omega
  rcases hirr (centralizerSpace H) bot_le le_top hinv with hbot | htop
  · exact hne hbot
  · have h1 : Module.finrank (ZMod p) (centralizerSpace H) =
        Module.finrank (ZMod p) U := by rw [htop, finrank_top]
    omega

private theorem eq_commutatorSpace_of_reflSubgroupIn_le (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h)
    (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b)
    {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U))), ∀ x ∈ X, g x ∈ X)
    (hXle : X ≤ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))))
    (hVHh_le : HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ≤ X) :
    X = HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVB_eq := commutatorSpace_closure_insert_reflSubgroupIn_eq_ker hp hh hh' hb' hhb hbH hdim
  by_cases hX : X = HardMathSupport.Kantor79.commutatorSpace Hh
  · exfalso
    have hmap := mapsTo_commutatorSpace_of_eq_reflSubgroupIn hp hh hh' hb' hhb hbH
      hdim hH hX hXinv
    exact false_of_invariant_commutatorSpace hH hpair hmap
  · have hlt : HardMathSupport.Kantor79.commutatorSpace Hh < X := lt_of_le_of_ne hVHh_le
      (Ne.symm hX)
    have hdim_lt := Submodule.finrank_lt_finrank_of_lt hlt
    have hdimVHh : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace Hh) =
        Module.finrank (ZMod p) U - 2 := by omega
    have hdimVB : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
        Module.finrank (ZMod p) U - 1 := by
      rw [hVB_eq]
      have h := IsRefl.finrank_ker_sub_one_add_one hh'
      omega
    have hdimX : Module.finrank (ZMod p) X =
        Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) := by
      have hle := Submodule.finrank_mono hXle
      omega
    exact Submodule.eq_of_le_of_finrank_eq hXle hdimX

private theorem le_centralizerSpace_of_le_sup_movedSpace [Module.Finite (ZMod p) U]
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H) {X : Submodule (ZMod p) U}
    (hXW : X ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hdisj : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ⊓
      HardMathSupport.Kantor79.movedSpace h = ⊥)
    (hXsup : X ≤ centralizerSpace H ⊔ HardMathSupport.Kantor79.movedSpace h) :
    X ≤ centralizerSpace H := by
  intro x hx
  obtain ⟨a, ha, v, hv, hsum⟩ := Submodule.mem_sup.mp (hXsup hx)
  have hxW : x ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := hXW hx
  have haW : a ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    rw [LinearMap.mem_ker]
    change (h : U →ₗ[ZMod p] U) a - a = 0
    have hfixa : (h : U →ₗ[ZMod p] U) a = a := (mem_centralizerSpace.mp ha) h hh
    rw [hfixa]
    abel
  have hvW : v ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := by
    have hv_eq : v = x - a := by rw [← hsum]; abel
    rw [hv_eq]
    exact (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)).sub_mem hxW haW
  have hv0 : v = 0 := by
    have hmem : v ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ⊓
        HardMathSupport.Kantor79.movedSpace h := ⟨hvW, hv⟩
    rw [hdisj] at hmem
    simpa using hmem
  rw [← hsum, hv0, add_zero]
  exact ha

private theorem false_of_le_centralizerSpace_of_invariant
    [Module.Finite (ZMod p) U] {h b : U ≃ₗ[ZMod p] U}
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b) {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U))), ∀ x ∈ X, g x ∈ X)
    (hXbot : X ≠ ⊥) (hXleVH : X ≤ centralizerSpace H) : False := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hdimCent : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have hsum := Submodule.finrank_add_eq_of_isCompl hH.1
    have hdimVH : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) =
        Module.finrank (ZMod p) U - 1 := hH.2.1
    have hUpos : 0 < Module.finrank (ZMod p) U := by
      have hle := Submodule.finrank_mono
        (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hpair.1)
      have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace h) = 1 :=
        hpair.2.1.2
      omega
    omega
  have hXeq : X = centralizerSpace H := by
    refine Submodule.eq_of_le_of_finrank_eq hXleVH ?_
    have hpos : 1 ≤ Module.finrank (ZMod p) X := Submodule.one_le_finrank_iff.mpr hXbot
    have hle := Submodule.finrank_mono hXleVH
    omega
  have hbB : b ∈ B := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbCent : ∀ w ∈ centralizerSpace H, (b : U →ₗ[ZMod p] U) w ∈ centralizerSpace H := by
    intro w hw
    have hmem : (b : U →ₗ[ZMod p] U) w ∈ X := hXinv b hbB w (hXeq ▸ hw)
    exact hXeq ▸ hmem
  exact false_of_invariant_centralizerSpace hH hpair hbCent

private theorem eq_bot_of_le_centralizerSpace_of_invariant (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {h b : U ≃ₗ[ZMod p] U} (hh : h ∈ H) (hh' : IsRefl p h) (hb' : IsRefl p b)
    (hhb : h * b = b * h)
    (hbH : ¬ HardMathSupport.Kantor79.movedSpace b ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (hpair : IsCommIrredPair p G H h b)
    (hirr₁ : IrredOnSection (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))))
    {X : Submodule (ZMod p) U}
    (hXinv : ∀ g ∈ Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U))), ∀ x ∈ X, g x ∈ X)
    (hXle : X ≤ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))))
    (hXcent : X ≤ centralizerSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) :
    X = ⊥ := by
  set Hh := reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVB_eq := commutatorSpace_closure_insert_reflSubgroupIn_eq_ker hp hh hh' hb' hhb hbH hdim
  have hcent_eq := centralizerSpace_reflSubgroupIn_eq_sup_movedSpace hp hG hHG hh hh' hH hdim hirr₁
  have hdisj : LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) ⊓
      HardMathSupport.Kantor79.movedSpace h = ⊥ := by
    have h := (IsRefl.isCompl_ker_sub_one_ker_add_one hp hh').symm.inf_eq_bot
    rw [← IsRefl.movedSpace_eq_ker_add_one hp hh', inf_comm] at h
    exact h
  have hXW : X ≤ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) := hXle.trans (le_of_eq hVB_eq)
  have hXsup : X ≤ centralizerSpace H ⊔ HardMathSupport.Kantor79.movedSpace h := by
    rw [← hcent_eq]
    exact hXcent
  have hXleVH : X ≤ centralizerSpace H :=
    le_centralizerSpace_of_le_sup_movedSpace hh hXW hdisj hXsup
  by_cases hXbot : X = ⊥
  · exact hXbot
  · exact (false_of_le_centralizerSpace_of_invariant hH hpair hXinv hXbot hXleVH).elim

theorem irredOnSection_closure_insert_reflSubgroupIn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1)) {h b : U ≃ₗ[ZMod p] U}
    (hpair : IsCommIrredPair p G H h b)
    (hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
        Module.finrank (ZMod p) U)
    (hirr₁ : IrredOnSection (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊥
      (HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))))) :
    IrredOnSection (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U))))
      ⊥ (HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U))))) := by
  have hpair' := hpair
  obtain ⟨hh, hh', hb, hb', hhb, hirr⟩ := hpair'
  set W := LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1) with hW
  set Hh := reflSubgroupIn p H W with hHh
  set B := Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) with hB
  have hVB_eq := commutatorSpace_closure_insert_reflSubgroupIn_eq_ker hp hh hh' hb' hhb
    (not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH hpair) hdim
  have hgen : ReflGen p Hh := reflGen_reflSubgroupIn H W
  have hinfHh : HardMathSupport.Kantor79.commutatorSpace Hh ⊓ centralizerSpace Hh = ⊥ :=
    commutatorSpace_inf_centralizerSpace_eq_bot hp hgen hirr₁
  have hirrHh : IrredOnSection Hh (HardMathSupport.Kantor79.commutatorSpace Hh ⊓
      centralizerSpace Hh) (HardMathSupport.Kantor79.commutatorSpace Hh) := by
    rw [hinfHh]
    exact hirr₁
  have hbH := not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH hpair
  intro X _ hXle hXinv
  have hHh_le_B : Hh ≤ B := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have hXinvHh : ∀ g ∈ Hh, ∀ x ∈ X, g x ∈ X :=
    fun g hg x hx => hXinv g (hHh_le_B hg) x hx
  rcases commutatorSpace_le_or_le_centralizerSpace hp hgen hirrHh hXinvHh with hle | hcent
  · exact Or.inr (eq_commutatorSpace_of_reflSubgroupIn_le hp hh hh' hb' hhb hbH hdim
      hH hpair hXinv hXle hle)
  · exact Or.inl (eq_bot_of_le_centralizerSpace_of_invariant hp hG hHG hh hh' hb' hhb hbH hdim
      hH hpair hirr₁ hXinv hXle hcent)

private theorem refl_apply_eq_self_of_ne (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {m : ℕ} {r : Fin m → U ≃ₗ[ZMod p] U} {e : Fin m → U}
    (hcomm : ∀ i j, r i * r j = r j * r i) (hrefl : ∀ i, IsRefl p (r i))
    (hact : ∀ i, r i (e i) = -e i) (hli : LinearIndependent (ZMod p) e)
    {i k : Fin m} (hik : i ≠ k) : r i (e k) = e k := by
  have hM : HardMathSupport.Kantor79.movedSpace (r k) =
      Submodule.span (ZMod p) {e k} :=
    IsRefl.movedSpace_eq_span hp (hrefl k) (hact k) (hli.ne_zero k)
  have hmem : r i (e k) ∈ HardMathSupport.Kantor79.movedSpace (r k) := by
    rw [IsRefl.movedSpace_eq_ker_add_one hp (hrefl k)]
    refine LinearMap.mem_ker.mpr ?_
    rw [LinearMap.add_apply, Module.End.one_apply]
    change (r k : U →ₗ[ZMod p] U) ((r i : U →ₗ[ZMod p] U) (e k)) +
      (r i : U →ₗ[ZMod p] U) (e k) = 0
    have hcomm' : (r k : U →ₗ[ZMod p] U) ((r i : U →ₗ[ZMod p] U) (e k)) =
        (r i : U →ₗ[ZMod p] U) ((r k : U →ₗ[ZMod p] U) (e k)) := by
      have h := congrArg (fun f : U ≃ₗ[ZMod p] U => f (e k)) (hcomm k i)
      simpa [LinearEquiv.mul_apply] using h
    have hactk : (r k : U →ₗ[ZMod p] U) (e k) = -e k := by simpa using hact k
    rw [hcomm', hactk, map_neg]
    abel
  rw [hM] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hriri : r i (r i (e k)) = e k := by
    have h := congrArg (fun f : U ≃ₗ[ZMod p] U => f (e k)) (hrefl i).1
    simpa [LinearEquiv.mul_apply] using h
  have h1 : c • r i (e k) = e k := by
    rw [← map_smul, hc, hriri]
  have h2 : c • (c • e k) = e k := by
    rw [← hc] at h1
    exact h1
  rw [← mul_smul] at h2
  have hcc : c * c = 1 := by
    have h3 : (c * c - 1) • e k = 0 := by
      rw [sub_smul, one_smul, h2, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right (hli.ne_zero k))
  rcases mul_self_eq_one_iff.mp hcc with h4 | h4
  · rw [← hc, h4, one_smul]
  · exfalso
    have hmem2 : e k ∈ HardMathSupport.Kantor79.movedSpace (r i) := by
      rw [IsRefl.movedSpace_eq_ker_add_one hp (hrefl i)]
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.add_apply, Module.End.one_apply]
      have hc' : c • e k = (r i : U →ₗ[ZMod p] U) (e k) := by simpa using hc
      rw [← hc', h4, neg_one_smul]
      abel
    rw [IsRefl.movedSpace_eq_span hp (hrefl i) (hact i) (hli.ne_zero i)] at hmem2
    exact (hli.notMem_span_image (s := {i})
      (by simp only [Set.mem_singleton_iff]; exact fun h => hik h.symm)) (by simpa using hmem2)

private theorem apply_root_eq_smul_of_commute (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {t b : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) (hcomm : t * b = b * t) {a : U}
    (hM : HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {a}) :
    ∃ c : ZMod p, c • a = b a := by
  have hamem : a ∈ HardMathSupport.Kantor79.movedSpace t :=
    hM ▸ Submodule.mem_span_singleton_self a
  rw [IsRefl.movedSpace_eq_ker_add_one hp ht] at hamem
  rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply] at hamem
  have hta : (t : U →ₗ[ZMod p] U) a = -a := by
    rw [eq_neg_iff_add_eq_zero]
    exact hamem
  have hcomm' : (t : U →ₗ[ZMod p] U) ((b : U →ₗ[ZMod p] U) a) =
      (b : U →ₗ[ZMod p] U) ((t : U →ₗ[ZMod p] U) a) := by
    have h := congrArg (fun f : U ≃ₗ[ZMod p] U => f a) hcomm
    simpa [LinearEquiv.mul_apply] using h
  have hmem : b a ∈ HardMathSupport.Kantor79.movedSpace t := by
    rw [IsRefl.movedSpace_eq_ker_add_one hp ht]
    refine LinearMap.mem_ker.mpr ?_
    rw [LinearMap.add_apply, Module.End.one_apply]
    change (t : U →ₗ[ZMod p] U) ((b : U →ₗ[ZMod p] U) a) +
      (b : U →ₗ[ZMod p] U) a = 0
    rw [hcomm', hta, map_neg]
    abel
  rw [hM] at hmem
  exact Submodule.mem_span_singleton.mp hmem

private theorem finrank_span_singleton_pair [Module.Finite (ZMod p) U] {a c : U}
    (ha : a ≠ 0) (hc : c ≠ 0) (hac : c ∉ Submodule.span (ZMod p) {a}) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({a, c} : Set U)) = 2 := by
  have heq : Submodule.span (ZMod p) ({a, c} : Set U) =
      Submodule.span (ZMod p) {a} ⊔ Submodule.span (ZMod p) {c} := by
    rw [show ({a, c} : Set U) = insert a {c} from rfl, Submodule.span_insert]
  have hinf : Submodule.span (ZMod p) {a} ⊓ Submodule.span (ZMod p) {c} = ⊥ := by
    by_contra hne
    have hatom : IsAtom (Submodule.span (ZMod p) {c}) :=
      Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton hc)
    have hEq : Submodule.span (ZMod p) {a} ⊓ Submodule.span (ZMod p) {c} =
        Submodule.span (ZMod p) {c} := (hatom.le_iff.mp inf_le_right).resolve_left hne
    exact hac ((hEq ▸ inf_le_left) (Submodule.mem_span_singleton_self c))
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod p) {a}) (Submodule.span (ZMod p) {c})
  rw [hinf, finrank_bot, finrank_span_singleton ha, finrank_span_singleton hc] at h
  rw [heq]
  omega

private theorem span_triple_eq_sup (a c f : U) :
    Submodule.span (ZMod p) ({a, c, f} : Set U) =
      Submodule.span (ZMod p) ({a, c} : Set U) ⊔ Submodule.span (ZMod p) {f} := by
  rw [show ({a, c, f} : Set U) = ({a, c} : Set U) ∪ {f} by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto]
  exact Submodule.span_union _ _

private theorem finrank_span_pair_sup_singleton [Module.Finite (ZMod p) U] {a c f : U}
    (h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({a, c} : Set U)) = 2)
    (hf : f ∉ Submodule.span (ZMod p) ({a, c} : Set U)) (hf0 : f ≠ 0) :
    Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({a, c} : Set U) ⊔
      Submodule.span (ZMod p) {f}) = 3 := by
  have hinf : Submodule.span (ZMod p) ({a, c} : Set U) ⊓ Submodule.span (ZMod p) {f} = ⊥ := by
    by_contra hne
    have hfatom : IsAtom (Submodule.span (ZMod p) {f}) :=
      Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton hf0)
    have hEq : Submodule.span (ZMod p) ({a, c} : Set U) ⊓ Submodule.span (ZMod p) {f} =
        Submodule.span (ZMod p) {f} := (hfatom.le_iff.mp inf_le_right).resolve_left hne
    exact hf ((hEq ▸ inf_le_left) (Submodule.mem_span_singleton_self f))
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span (ZMod p) ({a, c} : Set U)) (Submodule.span (ZMod p) {f})
  rw [hinf, finrank_bot, h2, finrank_span_singleton hf0] at h
  omega

private theorem finrank_span_triple [Module.Finite (ZMod p) U] {a c f : U}
    (h2 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({a, c} : Set U)) = 2)
    (hf : f ∉ Submodule.span (ZMod p) ({a, c} : Set U)) (hf0 : f ≠ 0) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({a, c, f} : Set U)) = 3 := by
  rw [span_triple_eq_sup]
  exact finrank_span_pair_sup_singleton h2 hf hf0

private theorem ker_sub_one_eq_span_of_pair (_hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) {r0 : U ≃ₗ[ZMod p] U} (hr0H : r0 ∈ H)
    (hr0' : IsRefl p r0) {e1 e2 f : U} (he1 : r0 e1 = e1) (he2 : r0 e2 = e2)
    (he1' : e1 ≠ 0) (he2' : e2 ≠ 0) (hf0 : f ≠ 0) (hfC : f ∈ centralizerSpace H)
    (he12 : e2 ∉ Submodule.span (ZMod p) {e1})
    (hf : f ∉ Submodule.span (ZMod p) ({e1, e2} : Set U)) :
    LinearMap.ker ((r0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e1, e2, f} : Set U) := by
  have hfin12 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e1, e2} : Set U)) = 2 :=
    finrank_span_singleton_pair he1' he2' he12
  have hfinE : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e1, e2, f} : Set U)) = 3 :=
    finrank_span_triple hfin12 hf hf0
  have hdimK : Module.finrank (ZMod p) (LinearMap.ker ((r0 : U →ₗ[ZMod p] U) - 1)) = 3 := by
    have h := IsRefl.finrank_ker_sub_one_add_one hr0'
    rw [h4] at h
    omega
  have hle : Submodule.span (ZMod p) ({e1, e2, f} : Set U) ≤
      LinearMap.ker ((r0 : U →ₗ[ZMod p] U) - 1) := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      have h' : (r0 : U →ₗ[ZMod p] U) x = x := by simpa using he1
      rw [h', sub_self]
    · refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      have h' : (r0 : U →ₗ[ZMod p] U) x = x := by simpa using he2
      rw [h', sub_self]
    · refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      have h' : (r0 : U →ₗ[ZMod p] U) x = x := by
        simpa using (mem_centralizerSpace.mp hfC) r0 hr0H
      rw [h', sub_self]
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinE, hdimK])).symm

private theorem commutatorSpace_closure_insert_le_ker [Module.Finite (ZMod p) U]
    {W : Submodule (ZMod p) U} {h b : U ≃ₗ[ZMod p] U}
    (_hW : W = LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))
    (hbW : HardMathSupport.Kantor79.movedSpace b ≤ W) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H W : Set (U ≃ₗ[ZMod p] U)))) ≤ W := by
  set Hh := reflSubgroupIn p H W with hHh
  let x : {g : U ≃ₗ[ZMod p] U // g = b ∨ g ∈ Hh} → U ≃ₗ[ZMod p] U := Subtype.val
  have hrange : Subgroup.closure (Set.range x) =
      Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U))) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨g, rfl⟩
      change (g : U ≃ₗ[ZMod p] U) ∈
        Subgroup.closure (insert b (Hh : Set (U ≃ₗ[ZMod p] U)))
      rcases g.2 with hg | hg
      · rw [hg]
        exact Subgroup.subset_closure (Set.mem_insert _ _)
      · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ hg)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      rcases hg with hgb | hg
      · exact Subgroup.subset_closure ⟨⟨g, Or.inl hgb⟩, rfl⟩
      · exact Subgroup.subset_closure ⟨⟨g, Or.inr hg⟩, rfl⟩
  rw [← hrange, HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace]
  refine iSup_le ?_
  rintro ⟨g, hg⟩
  rcases hg with rfl | hg
  · exact hbW
  · exact (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hg).trans
      (commutatorSpace_reflSubgroupIn_le H W)

private theorem refl_mem_reflSubgroupIn_of_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {W : Submodule (ZMod p) U} {i : Fin 3}
    (hW : e i ∈ W) : r i ∈ reflSubgroupIn p H W := by
  have hM : HardMathSupport.Kantor79.movedSpace (r i) = Submodule.span (ZMod p) {e i} :=
    IsRefl.movedSpace_eq_span hp (hT.1 i).2.1 (hT.1 i).2.2 (hT.2.2.1.ne_zero i)
  refine Subgroup.subset_closure ⟨(hT.1 i).1, (hT.1 i).2.1, ?_⟩
  intro v
  have hmem : (r i : U →ₗ[ZMod p] U) v - v ∈ HardMathSupport.Kantor79.movedSpace (r i) :=
    ⟨v, rfl⟩
  rw [hM] at hmem
  exact (Submodule.span_singleton_le_iff_mem (e i) W).mpr hW hmem

private theorem root_mem_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (i : Fin 3) :
    e i ∈ HardMathSupport.Kantor79.commutatorSpace H :=
  HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 i).1
    (by rw [IsRefl.movedSpace_eq_span hp (hT.1 i).2.1 (hT.1 i).2.2
        (hT.2.2.1.ne_zero i)]
        exact Submodule.mem_span_singleton_self (e i))

private theorem span_e1e2_le_commutatorSpace_closure (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U} {f : U}
    (hT : IsCyclicRootTriple p H r e s)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    Submodule.span (ZMod p) ({e 1, e 2} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U)))) := by
  have hli := hT.2.2.1
  have hM1 : HardMathSupport.Kantor79.movedSpace (r 1) = Submodule.span (ZMod p) {e 1} :=
    IsRefl.movedSpace_eq_span hp (hT.1 1).2.1 (hT.1 1).2.2 (hli.ne_zero 1)
  have hM2 : HardMathSupport.Kantor79.movedSpace (r 2) = Submodule.span (ZMod p) {e 2} :=
    IsRefl.movedSpace_eq_span hp (hT.1 2).2.1 (hT.1 2).2.2 (hli.ne_zero 2)
  have he1K0 : e 1 ∈ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    rw [hK0]; exact Submodule.subset_span (by simp)
  have he2K0 : e 2 ∈ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    rw [hK0]; exact Submodule.subset_span (by simp)
  have he1moved : e 1 ∈ HardMathSupport.Kantor79.movedSpace (r 1) := by
    rw [hM1]
    exact Submodule.mem_span_singleton_self (e 1)
  have he2moved : e 2 ∈ HardMathSupport.Kantor79.movedSpace (r 2) := by
    rw [hM2]
    exact Submodule.mem_span_singleton_self (e 2)
  refine Submodule.span_le.mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (Set.mem_insert_of_mem _
        (refl_mem_reflSubgroupIn_of_mem hp hT he1K0))) he1moved
  · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (Set.mem_insert_of_mem _
        (refl_mem_reflSubgroupIn_of_mem hp hT he2K0))) he2moved

private theorem sup_span_e1e2_movedSpace_eq (_hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} {f : U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))
    (hVbNotSpan : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, e 2} : Set U)) :
    Submodule.span (ZMod p) ({e 1, e 2} : Set U) ⊔
      HardMathSupport.Kantor79.movedSpace b = LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
  have hli := hT.2.2.1
  have hK0dim : Module.finrank (ZMod p) (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) = 3 := by
    have h := IsRefl.finrank_ker_sub_one_add_one (hT.1 0).2.1
    rw [h4] at h
    omega
  have hVbne : HardMathSupport.Kantor79.movedSpace b ≠ ⊥ := by
    intro hbot
    have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace b) = 1 :=
      hpair.2.2.2.1.2
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨w, hwmem, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbne
  have hVbspan : HardMathSupport.Kantor79.movedSpace b = Submodule.span (ZMod p) {w} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hpair.2.2.2.1.2 hwmem hw0
  have hwNot : w ∉ Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
    intro h
    apply hVbNotSpan
    rw [hVbspan]
    exact (Submodule.span_singleton_le_iff_mem w _).mpr h
  have hfin12 : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, e 2} : Set U)) = 2 :=
    finrank_span_singleton_pair (hli.ne_zero 1) (hli.ne_zero 2)
      (by simpa using hli.notMem_span_image (s := {1})
            (by simp : (2 : Fin 3) ∉ ({1} : Set (Fin 3))))
  have hdimSup : Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) ({e 1, e 2} : Set U) ⊔
      HardMathSupport.Kantor79.movedSpace b) = 3 := by
    rw [hVbspan]
    exact finrank_span_pair_sup_singleton hfin12 hwNot hw0
  have hle : Submodule.span (ZMod p) ({e 1, e 2} : Set U) ⊔
      HardMathSupport.Kantor79.movedSpace b ≤ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    refine sup_le ?_ hbK0
    rw [hK0]
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimSup, hK0dim])

private theorem commutatorSpace_closure_insert_eq_ker (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {f : U} (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) = LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  set B := Subgroup.closure (insert b
    (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
      Set (U ≃ₗ[ZMod p] U))) with hBdef
  have hVbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) :=
    IsRefl.movedSpace_le_ker_of_commute (hT.1 0).2.1 hpair.2.2.2.1 hpair.2.2.2.2.1
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 0).1)
      (not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair)
  have hVble : HardMathSupport.Kantor79.commutatorSpace B ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) :=
    commutatorSpace_closure_insert_le_ker (h := r 0)
      (W := LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) rfl hVbK0
  have hVbNotSpan : ¬ HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
    intro h
    exact not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair
      (h.trans (Submodule.span_le.mpr (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact root_mem_commutatorSpace hp hT 1
        · exact root_mem_commutatorSpace hp hT 2)))
  have hsupEq := sup_span_e1e2_movedSpace_eq hp h4 hT hpair hK0 hVbK0 hVbNotSpan
  have hspan12le := span_e1e2_le_commutatorSpace_closure (b := b) (f := f) hp hT hK0
  have hVbB : HardMathSupport.Kantor79.movedSpace b ≤
      HardMathSupport.Kantor79.commutatorSpace B :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (Set.mem_insert _ _))
  refine le_antisymm hVble ?_
  rw [← hsupEq]
  exact sup_le hspan12le hVbB

private theorem inf_ker_sub_one_eq_span_of_neg_fix (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (_h4 : Module.finrank (ZMod p) U = 4) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    {A : Submodule (ZMod p) U} {a b c : U}
    (hA : A = Submodule.span (ZMod p) ({a, b, c} : Set U))
    (hAfin : Module.finrank (ZMod p) A = 3)
    (hnega : t a = -a) (hfixb : t b = b) (hfixc : t c = c) (ha' : a ≠ 0)
    (hspanbc : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({b, c} : Set U)) = 2) :
    A ⊓ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({b, c} : Set U) := by
  have hbc_le : Submodule.span (ZMod p) ({b, c} : Set U) ≤
      A ⊓ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨hA ▸ Submodule.subset_span (by simp), ?_⟩
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      have h' : (t : U →ₗ[ZMod p] U) x = x := by simpa using hfixb
      rw [h', sub_self]
    · refine ⟨hA ▸ Submodule.subset_span (by simp), ?_⟩
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      have h' : (t : U →ₗ[ZMod p] U) x = x := by simpa using hfixc
      rw [h', sub_self]
  have hdimInf : Module.finrank (ZMod p) ↥(A ⊓
      LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)) = 2 := by
    have haK : a ∉ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
      intro hmem
      have h1 : (t : U →ₗ[ZMod p] U) a = a := by
        simpa [LinearMap.mem_ker, sub_eq_zero] using hmem
      have h2 : (t : U →ₗ[ZMod p] U) a = -a := by simpa using hnega
      exact ha' (eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp) (h1.symm.trans h2))
    have h := IsRefl.finrank_inf_ker_sub_one_add_one hp ht
      (A := A) (a := a) (hA ▸ Submodule.subset_span (by simp)) haK
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hbc_le (by rw [hdimInf, hspanbc])).symm

private theorem inf_span_pair_ker_eq_span_of_neg (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {t : U ≃ₗ[ZMod p] U} (_ht : IsRefl p t) {b c : U}
    (hnegb : t b = -b) (hb' : b ≠ 0) (hfixc : t c = c) (hc' : c ≠ 0)
    (hspanbc : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({b, c} : Set U)) = 2) :
    Submodule.span (ZMod p) ({b, c} : Set U) ⊓ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) {c} := by
  set K := LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) with hK
  set A := Submodule.span (ZMod p) ({b, c} : Set U) with hA
  have hA2 : Module.finrank (ZMod p) A = 2 := by rw [hA]; exact hspanbc
  have hc_le : Submodule.span (ZMod p) {c} ≤ A ⊓ K := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine ⟨Submodule.subset_span (by simp), ?_⟩
    rw [hK]
    refine LinearMap.mem_ker.mpr ?_
    rw [LinearMap.sub_apply, Module.End.one_apply]
    have h' : (t : U →ₗ[ZMod p] U) c = c := by simpa using hfixc
    rw [h', sub_self]
  have hne : A ⊓ K ≠ A := by
    intro heq
    have hbK : b ∈ K := by
      have hle : A ≤ K := by rw [← heq]; exact inf_le_right
      exact hle (Submodule.subset_span (by simp))
    rw [hK, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hbK
    have h3 : (t : U →ₗ[ZMod p] U) b = -b := by simpa using hnegb
    have h4' : b = -b := hbK.symm.trans h3
    have h2 : (2 : ZMod p) • b = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h4'
    exact hb' ((smul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp))
  have hlt : Module.finrank (ZMod p) ↥(A ⊓ K) < 2 := by
    have hle := Submodule.finrank_mono (inf_le_left : A ⊓ K ≤ A)
    rw [hA2] at hle
    have hne2 : Module.finrank (ZMod p) ↥(A ⊓ K) ≠ 2 := by
      intro h2
      exact hne (Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h2, hA2]))
    omega
  have hge : 1 ≤ Module.finrank (ZMod p) ↥(A ⊓ K) := by
    have hle := Submodule.finrank_mono hc_le
    rwa [finrank_span_singleton hc'] at hle
  exact (Submodule.eq_of_le_of_finrank_eq hc_le (by
    rw [finrank_span_singleton hc']
    omega)).symm

private theorem exists_centralizerSpace_eq_span (_hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3) :
    ∃ f : U, f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} := by
  have hdim : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := Submodule.finrank_add_eq_of_isCompl hH.1
    have hV := hH.2.1
    omega
  have hne : centralizerSpace H ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hdim
    omega
  obtain ⟨f, hfC, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨f, hf0, eq_span_singleton_of_mem_of_finrank_eq_one hdim hfC hf0⟩

private theorem not_mem_span_pair_of_centralizer (_hp : p ≠ 2) (hH : SplitSupport H 3)
    {a b f : U} (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hbV : b ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hfC : f ∈ centralizerSpace H) (hab : b ∉ Submodule.span (ZMod p) {a}) :
    b ∉ Submodule.span (ZMod p) ({a, f} : Set U) := by
  intro hmem
  rw [show ({a, f} : Set U) = insert a {f} from rfl, Submodule.span_insert] at hmem
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
  have huV : u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    (Submodule.span_singleton_le_iff_mem a _).mpr haV hu
  have hwV : w ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    have h2 : b - u ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.sub_mem _ hbV huV
    simpa [show w = b - u from by rw [← huw]; abel] using h2
  have hwC : w ∈ centralizerSpace H :=
    (Submodule.span_singleton_le_iff_mem f _).mpr hfC hw
  have hw0 : w = 0 := by
    have hmem' : w ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H :=
      ⟨hwV, hwC⟩
    rw [hH.1.inf_eq_bot] at hmem'
    simpa using hmem'
  have hueq : u = b := by rw [← huw, hw0, add_zero]
  exact hab (by rw [← hueq]; exact hu)

private theorem exists_axis_decomposition (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r1 r2 : U ≃ₗ[ZMod p] U} (hr1 : IsRefl p r1) (hr2 : IsRefl p r2)
    {e1 e2 f : U} {X : Submodule (ZMod p) U}
    (hXle : X ≤ Submodule.span (ZMod p) ({e1, e2, f} : Set U))
    (hXinv1 : ∀ x ∈ X, (r1 : U →ₗ[ZMod p] U) x ∈ X)
    (hXinv2 : ∀ x ∈ X, (r2 : U →ₗ[ZMod p] U) x ∈ X)
    (hK1 : Submodule.span (ZMod p) ({e1, e2, f} : Set U) ⊓
        LinearMap.ker ((r1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e2, f} : Set U))
    (hK2 : Submodule.span (ZMod p) ({e2, f} : Set U) ⊓
        LinearMap.ker ((r2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f})
    (hM1 : HardMathSupport.Kantor79.movedSpace r1 = Submodule.span (ZMod p) {e1})
    (hM2 : HardMathSupport.Kantor79.movedSpace r2 = Submodule.span (ZMod p) {e2})
    (hcomm : r1 * r2 = r2 * r1) :
    ∃ Xa Xb Xc : Submodule (ZMod p) U, Xa ≤ Submodule.span (ZMod p) {e1} ∧
      Xb ≤ Submodule.span (ZMod p) {e2} ∧ Xc ≤ Submodule.span (ZMod p) {f} ∧
      X = Xa ⊔ (Xb ⊔ Xc) := by
  have hK1' : LinearMap.ker ((r1 : U →ₗ[ZMod p] U) + 1) = Submodule.span (ZMod p) {e1} := by
    rw [← IsRefl.movedSpace_eq_ker_add_one hp hr1]; exact hM1
  have hK2' : LinearMap.ker ((r2 : U →ₗ[ZMod p] U) + 1) = Submodule.span (ZMod p) {e2} := by
    rw [← IsRefl.movedSpace_eq_ker_add_one hp hr2]; exact hM2
  set Xa := X ⊓ LinearMap.ker ((r1 : U →ₗ[ZMod p] U) + 1) with hXa
  set X1 := X ⊓ LinearMap.ker ((r1 : U →ₗ[ZMod p] U) - 1) with hX1
  have hdecomp1 : X = X1 ⊔ Xa :=
    eq_sup_inf_ker_sub_one_ker_add_one (ZMod.prime_ne_zero p 2 hp) hr1.1 hXinv1
  have hX1le : X1 ≤ Submodule.span (ZMod p) ({e2, f} : Set U) := by
    have h : X1 ≤ Submodule.span (ZMod p) ({e1, e2, f} : Set U) ⊓
        LinearMap.ker ((r1 : U →ₗ[ZMod p] U) - 1) :=
      le_inf (inf_le_left.trans hXle) inf_le_right
    rwa [hK1] at h
  have hX1inv : ∀ w ∈ X1, (r2 : U →ₗ[ZMod p] U) w ∈ X1 :=
    apply_mem_ker_sub_one_of_commute hcomm hXinv2
  set Xb := X1 ⊓ LinearMap.ker ((r2 : U →ₗ[ZMod p] U) + 1) with hXb
  set Xc := X1 ⊓ LinearMap.ker ((r2 : U →ₗ[ZMod p] U) - 1) with hXc
  have hdecomp2 : X1 = Xc ⊔ Xb :=
    eq_sup_inf_ker_sub_one_ker_add_one (ZMod.prime_ne_zero p 2 hp) hr2.1 hX1inv
  have hXa_le : Xa ≤ Submodule.span (ZMod p) {e1} := hK1' ▸ inf_le_right
  have hXb_le : Xb ≤ Submodule.span (ZMod p) {e2} := hK2' ▸ inf_le_right
  have hXc_le : Xc ≤ Submodule.span (ZMod p) {f} := by
    have h : Xc ≤ Submodule.span (ZMod p) ({e2, f} : Set U) ⊓
        LinearMap.ker ((r2 : U →ₗ[ZMod p] U) - 1) :=
      le_inf (inf_le_left.trans hX1le) inf_le_right
    rwa [hK2] at h
  refine ⟨Xa, Xb, Xc, hXa_le, hXb_le, hXc_le, ?_⟩
  rw [hdecomp1, hdecomp2]
  ac_rfl

private theorem commute_of_apply_eq_self (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {b : U ≃ₗ[ZMod p] U} (hbG : b ∈ G)
    (_hbrefl : IsRefl p b) {i : Fin 3} (hfix : b (e i) = e i) : r i * b = b * r i := by
  have hli := hT.2.2.1
  have hM : HardMathSupport.Kantor79.movedSpace (r i) = Submodule.span (ZMod p) {e i} :=
    IsRefl.movedSpace_eq_span hp (hT.1 i).2.1 (hT.1 i).2.2 (hli.ne_zero i)
  have hle : HardMathSupport.Kantor79.movedSpace (r i) ≤
      LinearMap.ker ((b : U →ₗ[ZMod p] U) - 1) := by
    rw [hM]
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine LinearMap.mem_ker.mpr ?_
    rw [LinearMap.sub_apply, Module.End.one_apply]
    have hfix' : (b : U →ₗ[ZMod p] U) (e i) = e i := by simpa using hfix
    rw [hfix', sub_self]
  exact (commute_of_movedSpace_le_ker hp hG hbG (hHG (hT.1 i).1) (hT.1 i).2.1 hle).symm

private theorem exists_kernel_data (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (_hG : QTwoLin.TransvectionFree G)
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) :
    ∃ f : U, f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} ∧
      Module.finrank (ZMod p) (centralizerSpace H) = 1 ∧
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
        Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  have hli := hT.2.2.1
  have hfix01 : r 0 (e 1) = e 1 :=
    refl_apply_eq_self_of_ne hp hT.2.1 (fun i => (hT.1 i).2.1) (fun i => (hT.1 i).2.2) hli
      (by decide : (0 : Fin 3) ≠ 1)
  have hfix02 : r 0 (e 2) = e 2 :=
    refl_apply_eq_self_of_ne hp hT.2.1 (fun i => (hT.1 i).2.1) (fun i => (hT.1 i).2.2) hli
      (by decide : (0 : Fin 3) ≠ 2)
  obtain ⟨f, hf0, hCeq⟩ := exists_centralizerSpace_eq_span hp h4 hH
  have hfC : f ∈ centralizerSpace H := hCeq ▸ Submodule.mem_span_singleton_self f
  have hCdim : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    rw [hCeq]
    exact finrank_span_singleton hf0
  have he1V : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    root_mem_commutatorSpace hp hT 1
  have he2V : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    root_mem_commutatorSpace hp hT 2
  have he12 : e 2 ∉ Submodule.span (ZMod p) {e 1} :=
    (by simpa using hli.notMem_span_image (s := {1}) (by simp : (2 : Fin 3) ∉ ({1} : Set (Fin 3))))
  have hfV : f ∉ HardMathSupport.Kantor79.commutatorSpace H := by
    intro h
    have hmem : f ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H := ⟨h, hfC⟩
    rw [hH.1.inf_eq_bot] at hmem
    exact hf0 (by simpa using hmem)
  have hfspan : f ∉ Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
    intro h
    exact hfV (Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact he1V
      · exact he2V) h)
  refine ⟨f, hf0, hCeq, hCdim, ?_, ?_⟩
  · exact ker_sub_one_eq_span_of_pair hp h4 (hT.1 0).1 (hT.1 0).2.1 hfix01 hfix02
      (hli.ne_zero 1) (hli.ne_zero 2) hf0 hfC he12 hfspan
  · exact IsRefl.movedSpace_le_ker_of_commute (hT.1 0).2.1 hpair.2.2.2.1 hpair.2.2.2.2.1
      (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 0).1)
      (not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair)

private theorem kernel_intersection_dims (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {f : U} (hfC : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, f} : Set U)) = 2 ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 2, f} : Set U)) = 2 ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) = 3 ∧
      Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 2, e 1, f} : Set U)) = 3 := by
  have hli := hT.2.2.1
  have he1V : e 1 ∈ HardMathSupport.Kantor79.commutatorSpace H := root_mem_commutatorSpace hp hT 1
  have he2V : e 2 ∈ HardMathSupport.Kantor79.commutatorSpace H := root_mem_commutatorSpace hp hT 2
  have hfV : f ∉ HardMathSupport.Kantor79.commutatorSpace H := by
    intro h
    have hmem : f ∈ HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H := ⟨h, hfC⟩
    rw [hH.1.inf_eq_bot] at hmem
    exact hf0 (by simpa using hmem)
  have he1f : f ∉ Submodule.span (ZMod p) {e 1} := fun h =>
    hfV ((Submodule.span_singleton_le_iff_mem (e 1) _).mpr he1V h)
  have he2f : f ∉ Submodule.span (ZMod p) {e 2} := fun h =>
    hfV ((Submodule.span_singleton_le_iff_mem (e 2) _).mpr he2V h)
  have hfin1f : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, f} : Set U)) = 2 :=
    finrank_span_singleton_pair (hli.ne_zero 1) hf0 he1f
  have hfin2f : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 2, f} : Set U)) = 2 :=
    finrank_span_singleton_pair (hli.ne_zero 2) hf0 he2f
  have hAfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) = 3 := by
    have hK0dim : Module.finrank (ZMod p) (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) = 3 := by
      have h := IsRefl.finrank_ker_sub_one_add_one (hT.1 0).2.1
      rw [h4] at h
      omega
    rw [← hK0]
    exact hK0dim
  have hswap : Submodule.span (ZMod p) ({e 2, e 1, f} : Set U) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hAfin' : Module.finrank (ZMod p) (Submodule.span (ZMod p) ({e 2, e 1, f} : Set U)) = 3 := by
    rw [hswap]
    exact hAfin
  exact ⟨hfin1f, hfin2f, hAfin, hAfin'⟩

private theorem exists_kernel_intersections (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {f : U} (hfC : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    (Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
        LinearMap.ker ((r 1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 2, f} : Set U)) ∧
      (Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
        LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 1, f} : Set U)) ∧
      (Submodule.span (ZMod p) ({e 2, f} : Set U) ⊓
        LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f}) ∧
      (Submodule.span (ZMod p) ({e 2, f} : Set U) ⊓
        LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) + 1) = Submodule.span (ZMod p) {e 2}) := by
  have hli := hT.2.2.1
  have hfix12 : r 1 (e 2) = e 2 :=
    refl_apply_eq_self_of_ne hp hT.2.1 (fun i => (hT.1 i).2.1) (fun i => (hT.1 i).2.2) hli
      (by decide : (1 : Fin 3) ≠ 2)
  have hfix21 : r 2 (e 1) = e 1 :=
    refl_apply_eq_self_of_ne hp hT.2.1 (fun i => (hT.1 i).2.1) (fun i => (hT.1 i).2.2) hli
      (by decide : (2 : Fin 3) ≠ 1)
  have hfixf1 : r 1 f = f := (mem_centralizerSpace.mp hfC) (r 1) (hT.1 1).1
  have hfixf2 : r 2 f = f := (mem_centralizerSpace.mp hfC) (r 2) (hT.1 2).1
  obtain ⟨hfin1f, hfin2f, hAfin, hAfin'⟩ := kernel_intersection_dims hp h4 hH hT hfC hf0 hK0
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact inf_ker_sub_one_eq_span_of_neg_fix hp h4 (hT.1 1).2.1 rfl hAfin
      (hT.1 1).2.2 hfix12 hfixf1 (hli.ne_zero 1) hfin2f
  · have h := inf_ker_sub_one_eq_span_of_neg_fix (a := e 2) (b := e 1) (c := f) hp h4
      (hT.1 2).2.1 rfl hAfin' (hT.1 2).2.2 hfix21 hfixf2 (hli.ne_zero 2) hfin1f
    rw [show Submodule.span (ZMod p) ({e 2, e 1, f} : Set U) =
        Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) from by
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      tauto] at h
    exact h
  · exact inf_span_pair_ker_eq_span_of_neg hp (hT.1 2).2.1 (hT.1 2).2.2 (hli.ne_zero 2)
      hfixf2 hf0 hfin2f
  · rw [← IsRefl.movedSpace_eq_ker_add_one hp (hT.1 2).2.1]
    rw [IsRefl.movedSpace_eq_span hp (hT.1 2).2.1 (hT.1 2).2.2 (hli.ne_zero 2)]
    have hle : Submodule.span (ZMod p) {e 2} ≤
        Submodule.span (ZMod p) ({e 2, f} : Set U) := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact Submodule.subset_span (s := ({e 2, f} : Set U)) (Or.inl rfl)
    rw [inf_comm]
    exact inf_eq_left.mpr hle

private theorem span_e1e2_le_commutatorSpace (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) :
    Submodule.span (ZMod p) ({e 1, e 2} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
  refine Submodule.span_le.mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact root_mem_commutatorSpace hp hT 1
  · exact root_mem_commutatorSpace hp hT 2

private theorem span_pair_le_sup_centralizer {a f : U} (hfC : f ∈ centralizerSpace H) :
    Submodule.span (ZMod p) ({a, f} : Set U) ≤
      Submodule.span (ZMod p) {a} ⊔ centralizerSpace H := by
  rw [show ({a, f} : Set U) = insert a {f} from rfl, Submodule.span_insert]
  exact sup_le_sup le_rfl (Submodule.span_le.mpr (by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hfC))

private theorem movedSpace_le_ker_of_fixes_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {i : Fin 3} (hfix : b (e i) = e i) :
    HardMathSupport.Kantor79.movedSpace b ≤ LinearMap.ker ((r i : U →ₗ[ZMod p] U) - 1) := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  exact IsRefl.movedSpace_le_ker_of_commute (hT.1 i).2.1 hpair.2.2.2.1
    (commute_of_apply_eq_self hp hG hHG hT hpair.2.2.1 hpair.2.2.2.1 hfix)
    (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 i).1)
    (not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair)

private theorem b_fix_of_invariant_line (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {b : U ≃ₗ[ZMod p] U}
    (hpair : IsCommIrredPair p G H (r 0) b)
    {a : U} {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) {a})
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X) (ha0 : a ≠ 0)
    (haV : a ∈ HardMathSupport.Kantor79.commutatorSpace H) : b a = a := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  have hb' : IsRefl p b := hpair.2.2.2.1
  have haX : a ∈ X := by rw [hX]; exact Submodule.mem_span_singleton_self a
  have hmem : (b : U →ₗ[ZMod p] U) a ∈ Submodule.span (ZMod p) {a} := by
    rw [← hX]; exact hinv a haX
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hcc : c * c = 1 :=
    coeff_mul_self_of_mul_self hb'.1 (by simpa using hc.symm) ha0
  have hc'' : b a = c • a := by simpa using hc.symm
  rcases mul_self_eq_one_iff.mp hcc with h | h
  · rw [hc'', h, one_smul]
  · exfalso
    have hmem2 : a ∈ HardMathSupport.Kantor79.movedSpace b := by
      rw [IsRefl.movedSpace_eq_ker_add_one hp hb']
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.add_apply, Module.End.one_apply]
      change (b : U →ₗ[ZMod p] U) a + a = 0
      have hc' : c • a = (b : U →ₗ[ZMod p] U) a := hc
      rw [← hc', h, neg_one_smul]
      abel
    have hspan : HardMathSupport.Kantor79.movedSpace b = Submodule.span (ZMod p) {a} :=
      eq_span_singleton_of_mem_of_finrank_eq_one hb'.2 hmem2 ha0
    exact not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair (by
      rw [hspan]
      exact (Submodule.span_singleton_le_iff_mem a _).mpr haV)

private theorem b_fix_of_span_pair (_hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {b : U ≃ₗ[ZMod p] U}
    (hpair : IsCommIrredPair p G H (r 0) b) {a c : U}
    {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) ({a, c} : Set U))
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (hXleV : X ≤ HardMathSupport.Kantor79.commutatorSpace H) : b a = a ∧ b c = c := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  have hb' : IsRefl p b := hpair.2.2.2.1
  have hnot : ¬ HardMathSupport.Kantor79.movedSpace b ≤ X := fun h =>
    not_movedSpace_le_commutatorSpace_of_isCommIrredPair hH' hpair (h.trans hXleV)
  have hfix : ∀ w ∈ X, (b : U →ₗ[ZMod p] U) w = w := fun w hw =>
    apply_eq_self_of_not_movedSpace_le hb'.2 (fun x hx => hinv x hx) hnot hw
  exact ⟨by simpa using hfix a (by rw [hX]; exact Submodule.subset_span (by simp)),
    by simpa using hfix c (by rw [hX]; exact Submodule.subset_span (by simp))⟩

private theorem exists_fix_case_e1 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {f : U} (hfC : f ∈ centralizerSpace H)
    {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) {e 1})
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA1 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 2, f} : Set U))
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  have hb_e1 : b (e 1) = e 1 :=
    b_fix_of_invariant_line hp h4 hH hpair hX hinv (hT.2.2.1.ne_zero 1)
      (root_mem_commutatorSpace hp hT 1)
  have hble := movedSpace_le_ker_of_fixes_root hp h4 hG hHG hH hT hpair hb_e1
  have hVbA : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    rw [← hK0]
    exact hbK0
  have hle : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 2, f} : Set U) := by
    have h := le_inf hVbA hble
    rwa [hA1] at h
  exact ⟨2, 1, by decide, by decide, by decide, hb_e1,
    hle.trans (span_pair_le_sup_centralizer hfC)⟩

private theorem exists_fix_case_e2 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {f : U} (hfC : f ∈ centralizerSpace H)
    {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) {e 2})
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA2 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 1, f} : Set U))
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  have hb_e2 : b (e 2) = e 2 :=
    b_fix_of_invariant_line hp h4 hH hpair hX hinv (hT.2.2.1.ne_zero 2)
      (root_mem_commutatorSpace hp hT 2)
  have hble := movedSpace_le_ker_of_fixes_root hp h4 hG hHG hH hT hpair hb_e2
  have hVbA : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    rw [← hK0]
    exact hbK0
  have hle : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, f} : Set U) := by
    have h := le_inf hVbA hble
    rwa [hA2] at h
  exact ⟨1, 2, by decide, by decide, by decide, hb_e2,
    hle.trans (span_pair_le_sup_centralizer hfC)⟩

private theorem exists_fix_case_e12 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {f : U} (hfC : f ∈ centralizerSpace H)
    {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) ({e 1, e 2} : Set U))
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (hXleV : X ≤ HardMathSupport.Kantor79.commutatorSpace H)
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA1 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 2, f} : Set U))
    (hA12 : Submodule.span (ZMod p) ({e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f})
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  obtain ⟨he1, he2⟩ := b_fix_of_span_pair hp h4 hH hpair hX hinv hXleV
  have hle1 := movedSpace_le_ker_of_fixes_root hp h4 hG hHG hH hT hpair he1
  have hle2 := movedSpace_le_ker_of_fixes_root hp h4 hG hHG hH hT hpair he2
  have hVbA : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    rw [← hK0]
    exact hbK0
  have h1 : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) ({e 2, f} : Set U) := by
    have h := le_inf hVbA hle1
    rwa [hA1] at h
  have h2 : HardMathSupport.Kantor79.movedSpace b ≤ Submodule.span (ZMod p) {f} := by
    have h := le_inf h1 hle2
    rwa [hA12] at h
  refine ⟨1, 2, by decide, by decide, by decide, he2, h2.trans ?_⟩
  refine Submodule.span_le.mpr ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact Submodule.mem_sup_right hfC

private theorem plane_le_ker (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {f : U} (hfC : f ∈ centralizerSpace H)
    {i j : Fin 3} (hij : i ≠ j) {X : Submodule (ZMod p) U}
    (hX : X = Submodule.span (ZMod p) ({e i, f} : Set U)) :
    X ≤ LinearMap.ker ((r j : U →ₗ[ZMod p] U) - 1) := by
  have hfj : (r j : U →ₗ[ZMod p] U) f = f := by
    simpa using (mem_centralizerSpace.mp hfC) (r j) (hT.1 j).1
  have hei : (r j : U →ₗ[ZMod p] U) (e i) = e i := by
    simpa using refl_apply_eq_self_of_ne hp hT.2.1 (fun k => (hT.1 k).2.1)
      (fun k => (hT.1 k).2.2) hT.2.2.1 hij.symm
  intro x hx
  rw [hX] at hx
  refine LinearMap.mem_ker.mpr ?_
  rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  rw [show ({e i, f} : Set U) = insert (e i) {f} from rfl, Submodule.span_insert] at hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_add, map_smul, map_smul, hei, hfj]

private theorem plane_case_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (_h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (_hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {f : U} (hfC : f ∈ centralizerSpace H)
    {i j : Fin 3} (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j) {X : Submodule (ZMod p) U}
    (hX : X = Submodule.span (ZMod p) ({e i, f} : Set U))
    (hsub : HardMathSupport.Kantor79.movedSpace b ≤ X) (hnotmem : e j ∉ X) :
    ∃ i' j' : Fin 3, i' ≠ 0 ∧ j' ≠ 0 ∧ i' ≠ j' ∧ b (e j') = e j' ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i'} ⊔ centralizerSpace H := by
  have hli := hT.2.2.1
  have hb' : IsRefl p b := hpair.2.2.2.1
  have hble : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r j : U →ₗ[ZMod p] U) - 1) :=
    hsub.trans (plane_le_ker hp hT hfC hij hX)
  have hcomm : r j * b = b * r j :=
    commute_of_movedSpace_le_ker hp hG (hHG (hT.1 j).1) hpair.2.2.1 hb' hble
  have hM : HardMathSupport.Kantor79.movedSpace (r j) = Submodule.span (ZMod p) {e j} :=
    IsRefl.movedSpace_eq_span hp (hT.1 j).2.1 (hT.1 j).2.2 (hli.ne_zero j)
  obtain ⟨c, hc⟩ := apply_root_eq_smul_of_commute hp (hT.1 j).2.1 hcomm hM
  have hcc : c * c = 1 :=
    coeff_mul_self_of_mul_self hb'.1 (by simpa using hc.symm) (hli.ne_zero j)
  have hb_ej : b (e j) = e j := by
    have hc'' : b (e j) = c • e j := by simpa using hc.symm
    rcases mul_self_eq_one_iff.mp hcc with h | h
    · rw [hc'', h, one_smul]
    · exfalso
      apply hnotmem
      apply hsub
      rw [IsRefl.movedSpace_eq_ker_add_one hp hb']
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.add_apply, Module.End.one_apply]
      change (b : U →ₗ[ZMod p] U) (e j) + e j = 0
      have hc' : c • e j = (b : U →ₗ[ZMod p] U) (e j) := hc
      rw [← hc', h, neg_one_smul]
      abel
  exact ⟨i, j, hi0, hj0, hij, hb_ej,
    hsub.trans (by rw [hX]; exact span_pair_le_sup_centralizer hfC)⟩

private theorem exists_fix_case_plane (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {f : U} (hfC : f ∈ centralizerSpace H)
    (hCeq : centralizerSpace H = Submodule.span (ZMod p) {f})
    {i j : Fin 3} (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hij : i ≠ j)
    {X : Submodule (ZMod p) U} (hX : X = Submodule.span (ZMod p) ({e i, f} : Set U))
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X) (hnotmem : e j ∉ X) :
    ∃ i' j' : Fin 3, i' ≠ 0 ∧ j' ≠ 0 ∧ i' ≠ j' ∧ b (e j') = e j' ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i'} ⊔ centralizerSpace H := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  by_cases hsub : HardMathSupport.Kantor79.movedSpace b ≤ X
  · exact plane_case_le hp h4 hG hHG hH hT hpair hfC hi0 hj0 hij hX hsub hnotmem
  · have hb' : IsRefl p b := hpair.2.2.2.1
    have hfix : ∀ w ∈ X, (b : U →ₗ[ZMod p] U) w = w := fun w hw =>
      apply_eq_self_of_not_movedSpace_le hb'.2 (fun x hx => hinv x hx) hsub hw
    have hfX : f ∈ X := by rw [hX]; exact Submodule.subset_span (by simp)
    have hbf : (b : U →ₗ[ZMod p] U) f = f := hfix f hfX
    have hpres : ∀ x ∈ centralizerSpace H, (b : U →ₗ[ZMod p] U) x ∈ centralizerSpace H := by
      intro x hx
      rw [hCeq] at hx ⊢
      rw [Submodule.mem_span_singleton] at hx ⊢
      obtain ⟨a, rfl⟩ := hx
      exact ⟨a, by rw [map_smul, hbf]⟩
    exact (false_of_invariant_centralizerSpace hH' hpair hpres).elim

private theorem finish_cases_low (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {f : U} (hfC : f ∈ centralizerSpace H) (_hf0 : f ≠ 0)
    (hCeq : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA2 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 1, f} : Set U))
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))
    {X Xa Xb Xc : Submodule (ZMod p) U}
    (hXeq : X = Xa ⊔ (Xb ⊔ Xc)) (hXa0 : Xa = ⊥)
    (hXb_le : Xb ≤ Submodule.span (ZMod p) {e 2}) (hatom2 : IsAtom (Submodule.span (ZMod p) {e 2}))
    (hXc_le : Xc ≤ Submodule.span (ZMod p) {f}) (hatomf : IsAtom (Submodule.span (ZMod p) {f}))
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (he1not : e 1 ∉ Submodule.span (ZMod p) ({e 2, f} : Set U))
    (hXne : X ≠ ⊥) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  have hH' : SplitSupport H (Module.finrank (ZMod p) U - 1) := by rw [h4]; exact hH
  rcases hatom2.le_iff.mp hXb_le with hXb0 | hXb1 <;>
    rcases hatomf.le_iff.mp hXc_le with hXc0 | hXcf
  · have h0 : X = ⊥ := by simpa [hXa0, hXb0, hXc0] using hXeq
    exact absurd h0 hXne
  · have hXf : X = Submodule.span (ZMod p) {f} := by
      simpa [hXa0, hXb0, hXcf] using hXeq
    have hpres : ∀ x ∈ centralizerSpace H, (b : U →ₗ[ZMod p] U) x ∈ centralizerSpace H := by
      intro x hx
      rw [hCeq] at hx ⊢
      have hxX : x ∈ X := by rw [hXf]; exact hx
      have h := hinv x hxX
      rwa [hXf] at h
    exact (false_of_invariant_centralizerSpace hH' hpair hpres).elim
  · have hX2 : X = Submodule.span (ZMod p) {e 2} := by simpa [hXa0, hXb1, hXc0] using hXeq
    exact exists_fix_case_e2 hp h4 hG hHG hH hT hpair hfC hX2 hinv hK0 hA2 hbK0
  · have hX2f : X = Submodule.span (ZMod p) ({e 2, f} : Set U) := by
      simpa [hXa0, hXb1, hXcf, Submodule.span_insert] using hXeq
    exact exists_fix_case_plane hp h4 hG hHG hH hT hpair hfC hCeq
      (by decide : (2 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 1)
      hX2f hinv (by rw [hX2f]; exact he1not)

private theorem finish_cases_high (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {f : U} (hfC : f ∈ centralizerSpace H)
    (hCeq : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA1 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 2, f} : Set U))
    (hA12 : Submodule.span (ZMod p) ({e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f})
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))
    {X Xa Xb Xc : Submodule (ZMod p) U}
    (hXeq : X = Xa ⊔ (Xb ⊔ Xc)) (hXa1 : Xa = Submodule.span (ZMod p) {e 1})
    (hXb_le : Xb ≤ Submodule.span (ZMod p) {e 2}) (hatom2 : IsAtom (Submodule.span (ZMod p) {e 2}))
    (hXc_le : Xc ≤ Submodule.span (ZMod p) {f}) (hatomf : IsAtom (Submodule.span (ZMod p) {f}))
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (he2not : e 2 ∉ Submodule.span (ZMod p) ({e 1, f} : Set U))
    (hXneA : X ≠ Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  rcases hatom2.le_iff.mp hXb_le with hXb0 | hXb1 <;>
    rcases hatomf.le_iff.mp hXc_le with hXc0 | hXcf
  · have hX1 : X = Submodule.span (ZMod p) {e 1} := by simpa [hXa1, hXb0, hXc0] using hXeq
    exact exists_fix_case_e1 hp h4 hG hHG hH hT hpair hfC hX1 hinv hK0 hA1 hbK0
  · have hX1f : X = Submodule.span (ZMod p) ({e 1, f} : Set U) := by
      simpa [hXa1, hXb0, hXcf, Submodule.span_insert] using hXeq
    exact exists_fix_case_plane hp h4 hG hHG hH hT hpair hfC hCeq
      (by decide : (1 : Fin 3) ≠ 0) (by decide : (2 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)
      hX1f hinv (by rw [hX1f]; exact he2not)
  · have hX12 : X = Submodule.span (ZMod p) ({e 1, e 2} : Set U) := by
      simpa [hXa1, hXb1, hXc0, Submodule.span_insert] using hXeq
    have hXleV : X ≤ HardMathSupport.Kantor79.commutatorSpace H := by
      rw [hX12]
      exact span_e1e2_le_commutatorSpace hp hT
    exact exists_fix_case_e12 hp h4 hG hHG hH hT hpair hfC hX12 hinv hXleV hK0 hA1 hA12 hbK0
  · have hXA : X = Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
      have h := hXeq
      rw [hXa1, hXb1, hXcf] at h
      rw [h, span_triple_eq_sup, show ({e 1, e 2} : Set U) = insert (e 1) {e 2} from rfl,
        Submodule.span_insert]
      ac_rfl
    exact absurd hXA hXneA

private theorem finish_cases (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G)
    (hHG : H ≤ G) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {f : U} (hfC : f ∈ centralizerSpace H) (hf0 : f ≠ 0)
    (hCeq : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hK0 : LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) =
      Submodule.span (ZMod p) ({e 1, e 2, f} : Set U))
    (hA1 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 1 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 2, f} : Set U))
    (hA2 : Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) ({e 1, f} : Set U))
    (hA12 : Submodule.span (ZMod p) ({e 2, f} : Set U) ⊓
      LinearMap.ker ((r 2 : U →ₗ[ZMod p] U) - 1) = Submodule.span (ZMod p) {f})
    (hbK0 : HardMathSupport.Kantor79.movedSpace b ≤
      LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))
    {X : Submodule (ZMod p) U}
    (hinv : ∀ x ∈ X, (b : U →ₗ[ZMod p] U) x ∈ X)
    (hdec : ∃ Xa Xb Xc : Submodule (ZMod p) U, Xa ≤ Submodule.span (ZMod p) {e 1} ∧
      Xb ≤ Submodule.span (ZMod p) {e 2} ∧ Xc ≤ Submodule.span (ZMod p) {f} ∧
      X = Xa ⊔ (Xb ⊔ Xc))
    (hXne : X ≠ ⊥) (hXneA : X ≠ Submodule.span (ZMod p) ({e 1, e 2, f} : Set U)) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  obtain ⟨Xa, Xb, Xc, hXa, hXb, hXc, hXeq⟩ := hdec
  have hatom1 : IsAtom (Submodule.span (ZMod p) {e 1}) :=
    Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton (hT.2.2.1.ne_zero 1))
  have hatom2 : IsAtom (Submodule.span (ZMod p) {e 2}) :=
    Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton (hT.2.2.1.ne_zero 2))
  have hatomf : IsAtom (Submodule.span (ZMod p) {f}) :=
    Submodule.isAtom_iff_finrank_eq_one.mpr (finrank_span_singleton hf0)
  have he2not : e 2 ∉ Submodule.span (ZMod p) ({e 1, f} : Set U) :=
    not_mem_span_pair_of_centralizer hp hH (root_mem_commutatorSpace hp hT 1)
      (root_mem_commutatorSpace hp hT 2) hfC
      (by simpa using hT.2.2.1.notMem_span_image (s := {1})
            (by simp : (2 : Fin 3) ∉ ({1} : Set (Fin 3))))
  have he1not : e 1 ∉ Submodule.span (ZMod p) ({e 2, f} : Set U) :=
    not_mem_span_pair_of_centralizer hp hH (root_mem_commutatorSpace hp hT 2)
      (root_mem_commutatorSpace hp hT 1) hfC
      (by simpa using hT.2.2.1.notMem_span_image (s := {2})
            (by simp : (1 : Fin 3) ∉ ({2} : Set (Fin 3))))
  rcases hatom1.le_iff.mp hXa with hXa0 | hXa1
  · exact finish_cases_low hp h4 hG hHG hH hT hpair hfC hf0 hCeq hK0 hA2 hbK0 hXeq
      hXa0 hXb hatom2 hXc hatomf hinv he1not hXne
  · exact finish_cases_high hp h4 hG hHG hH hT hpair hfC hCeq hK0 hA1 hA12 hbK0 hXeq
      hXa1 hXb hatom2 hXc hatomf hinv he2not hXneA

private theorem exists_fix_of_not_irredOnSection_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    (hred : ¬ IrredOnSection (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) ⊥ (HardMathSupport.Kantor79.commutatorSpace
          (Subgroup.closure (insert b (reflSubgroupIn p H
            (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U)))))) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  obtain ⟨f, hf0, hCeq, -, hK0, hbK0⟩ := exists_kernel_data hp h4 hG hH hT hpair
  have hfC : f ∈ centralizerSpace H := hCeq ▸ Submodule.mem_span_singleton_self f
  obtain ⟨hA1, hA2, hA12, -⟩ := exists_kernel_intersections hp h4 hH hT hfC hf0 hK0
  have hli := hT.2.2.1
  have hM1 : HardMathSupport.Kantor79.movedSpace (r 1) = Submodule.span (ZMod p) {e 1} :=
    IsRefl.movedSpace_eq_span hp (hT.1 1).2.1 (hT.1 1).2.2 (hli.ne_zero 1)
  have hM2 : HardMathSupport.Kantor79.movedSpace (r 2) = Submodule.span (ZMod p) {e 2} :=
    IsRefl.movedSpace_eq_span hp (hT.1 2).2.1 (hT.1 2).2.2 (hli.ne_zero 2)
  have hVB := commutatorSpace_closure_insert_eq_ker hp h4 hH hT hpair hK0
  rw [IrredOnSection] at hred
  push Not at hred
  obtain ⟨X, -, hXleVB, hXinvB, hXne, hXneVB⟩ := hred
  have hXleA : X ≤ Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    rw [← hK0, ← hVB]
    exact hXleVB
  have he1K0 : e 1 ∈ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    rw [hK0]; exact Submodule.subset_span (by simp)
  have he2K0 : e 2 ∈ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    rw [hK0]; exact Submodule.subset_span (by simp)
  have hinvX1 : ∀ x ∈ X, (r 1 : U →ₗ[ZMod p] U) x ∈ X := fun x hx =>
    hXinvB (r 1) (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (refl_mem_reflSubgroupIn_of_mem hp hT he1K0))) x hx
  have hinvX2 : ∀ x ∈ X, (r 2 : U →ₗ[ZMod p] U) x ∈ X := fun x hx =>
    hXinvB (r 2) (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (refl_mem_reflSubgroupIn_of_mem hp hT he2K0))) x hx
  obtain ⟨Xa, Xb, Xc, hXa, hXb, hXc, hXeq⟩ := exists_axis_decomposition hp
    (hT.1 1).2.1 (hT.1 2).2.1 hXleA hinvX1 hinvX2 hA1 hA12 hM1 hM2 (hT.2.1 1 2)
  have hXneA : X ≠ Submodule.span (ZMod p) ({e 1, e 2, f} : Set U) := by
    intro hXA
    apply hXneVB
    rw [hVB, hK0]
    exact hXA
  exact finish_cases hp h4 hG hHG hH hT hpair hfC hf0 hCeq hK0 hA1 hA2 hA12 hbK0
    (fun x hx => hXinvB b (Subgroup.subset_closure (Set.mem_insert _ _)) x hx)
    ⟨Xa, Xb, Xc, hXa, hXb, hXc, hXeq⟩ hXne hXneA

theorem exists_fix_of_not_irredOnSection (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    (hred : ¬ IrredOnSection (Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) ⊥ (HardMathSupport.Kantor79.commutatorSpace
          (Subgroup.closure (insert b (reflSubgroupIn p H
            (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) : Set (U ≃ₗ[ZMod p] U)))))) :
    ∃ i j : Fin 3, i ≠ 0 ∧ j ≠ 0 ∧ i ≠ j ∧ b (e j) = e j ∧
      HardMathSupport.Kantor79.movedSpace b ≤
        Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
  exact exists_fix_of_not_irredOnSection_aux hp h4 hG hHG hH hT hpair hred

private theorem movedSpace_eq_span_of_apply_neg (h2 : (2 : ZMod p) ≠ 0)
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) {v : U} (hv : v ≠ 0) (htv : t v = -v) :
    HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {v} :=
  eq_span_singleton_of_mem_of_finrank_eq_one ht.2
    (mem_movedSpace_of_apply_eq_neg h2 htv) hv

private theorem not_mem_span_singleton_of_ne {e : Fin 3 → U}
    (hlin : LinearIndependent (ZMod p) e) {k l : Fin 3} (hkl : k ≠ l) :
    e l ∉ Submodule.span (ZMod p) {e k} := by
  intro hmem
  have hsub : Submodule.span (ZMod p) {e k} ≤
      Submodule.span (ZMod p) (e '' ({l}ᶜ : Set (Fin 3))) := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact Submodule.mem_span_of_mem (Set.mem_image_of_mem e (by simpa using hkl))
  exact (LinearIndependent.notMem_span hlin l) (hsub hmem)

private theorem apply_e_of_ne (h2 : (2 : ZMod p) ≠ 0) {r : Fin 3 → U ≃ₗ[ZMod p] U}
    {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    {k l : Fin 3} (hkl : k ≠ l) :
    r k (e l) = e l := by
  have hroot : HardMathSupport.Kantor79.movedSpace (r l) =
      Submodule.span (ZMod p) {e l} :=
    movedSpace_eq_span_of_apply_neg h2 (hT.1 l).2.1 (hT.2.2.1.ne_zero l) (hT.1 l).2.2
  have hconj : r k * r l * (r k)⁻¹ = r l := by
    rw [hT.2.1 k l]
    group
  have hmap := movedSpace_conj (r k) (r l)
  rw [hconj] at hmap
  have hmem : r k (e l) ∈ HardMathSupport.Kantor79.movedSpace (r l) := by
    rw [hmap]
    refine Submodule.mem_map_of_mem (f := (r k : U →ₗ[ZMod p] U)) ?_
    rw [hroot]
    exact Submodule.subset_span (Set.mem_singleton (e l))
  rw [hroot] at hmem
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c • e l = r k (e l) :=
    Submodule.mem_span_singleton.mp hmem
  have hc' : r k (e l) = c • e l := hc.symm
  have hsq : c * c = 1 := by
    have h1 : r k (r k (e l)) = e l := by
      have := congrArg (fun f : U ≃ₗ[ZMod p] U => f (e l)) (hT.1 k).2.1.1
      simpa [LinearEquiv.mul_apply] using this
    rw [hc', map_smul, hc', smul_smul] at h1
    exact LinearIndependent.smul_left_injective (R := ZMod p) (v := e) hT.2.2.1 l
      (by simpa using h1)
  rcases (sq_eq_one_iff (a := c)).mp (by rw [pow_two]; exact hsq) with hc1 | hcneg
  · rw [hc', hc1, one_smul]
  · exfalso
    have hneg : r k (e l) = -e l := by rw [hc', hcneg, neg_one_smul]
    have hmemneg : e l ∈ HardMathSupport.Kantor79.movedSpace (r k) :=
      mem_movedSpace_of_apply_eq_neg h2 hneg
    have hrootk : HardMathSupport.Kantor79.movedSpace (r k) =
        Submodule.span (ZMod p) {e k} :=
      movedSpace_eq_span_of_apply_neg h2 (hT.1 k).2.1 (hT.2.2.1.ne_zero k) (hT.1 k).2.2
    rw [hrootk] at hmemneg
    exact not_mem_span_singleton_of_ne hT.2.2.1 hkl hmemneg

private theorem span_range_e_eq_commutatorSpace [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hp : p ≠ 2)
    (hH : SplitSupport H 3) (hT : IsCyclicRootTriple p H r e s) :
    HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range e) := by
  have hle : Submodule.span (ZMod p) (Set.range e) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [Submodule.span_le]
    rintro v ⟨k, rfl⟩
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 k).1
      (mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) (hT.1 k).2.2)
  have hfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range e)) = 3 := by
    rw [finrank_span_eq_card hT.2.2.1]
    simp
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hH.2.1])).symm

private theorem span_range_eq_compl_sup {e : Fin 3 → U} (k : Fin 3) :
    Submodule.span (ZMod p) (Set.range e) =
      Submodule.span (ZMod p) (e '' ({k}ᶜ : Set (Fin 3))) ⊔
        Submodule.span (ZMod p) {e k} := by
  have hset : (e '' ({k}ᶜ : Set (Fin 3))) ∪ ({e k} : Set U) = Set.range e := by
    ext l
    simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff, Set.mem_range,
      Set.mem_compl_iff]
    constructor
    · rintro (⟨x, hx, rfl⟩ | rfl)
      · exact ⟨x, rfl⟩
      · exact ⟨k, rfl⟩
    · rintro ⟨y, rfl⟩
      by_cases hyk : y = k
      · exact Or.inr (congrArg e hyk)
      · exact Or.inl ⟨y, hyk, rfl⟩
  rw [← hset, Submodule.span_union]

private theorem r_ker_spans_compl (h2 : (2 : ZMod p) ≠ 0)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (k : Fin 3) :
    Submodule.span (ZMod p) (e '' ({k}ᶜ : Set (Fin 3))) ≤
        LinearMap.ker ((r k : U →ₗ[ZMod p] U) - 1) ∧
      Submodule.span (ZMod p) {e k} ≤ LinearMap.ker ((r k : U →ₗ[ZMod p] U) + 1) := by
  constructor
  · rw [Submodule.span_le]
    rintro w ⟨l, hl, rfl⟩
    change ((r k : U →ₗ[ZMod p] U) - 1) (e l) = 0
    change (r k) (e l) - e l = 0
    rw [apply_e_of_ne h2 hT (by simpa [eq_comm] using hl), sub_self]
  · rw [Submodule.span_le]
    rintro w hw
    rw [Set.mem_singleton_iff] at hw
    subst w
    change ((r k : U →ₗ[ZMod p] U) + 1) (e k) = 0
    change (r k) (e k) + e k = 0
    rw [(hT.1 k).2.2]
    simp

private theorem mem_span_compl_of_fixed [Module.Finite (ZMod p) U] (h2 : (2 : ZMod p) ≠ 0)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hVH : HardMathSupport.Kantor79.commutatorSpace H =
      Submodule.span (ZMod p) (Set.range e)) (hT : IsCyclicRootTriple p H r e s)
    {k : Fin 3} {v : U} (hvH : v ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hfix : r k v = v) :
    v ∈ Submodule.span (ZMod p) (e '' ({k}ᶜ : Set (Fin 3))) := by
  rw [hVH, span_range_eq_compl_sup (e := e) k] at hvH
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hvH
  obtain ⟨hxker, hyker⟩ := r_ker_spans_compl h2 hT k
  have hxfix : r k x = x := by
    have h := LinearMap.mem_ker.mp (hxker hx)
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using h)
  have hyfix : r k y = -y := by
    have h := LinearMap.mem_ker.mp (hyker hy)
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [LinearMap.add_apply] using h)
  have h_eq : x - y = x + y := by
    calc x - y = r k x + r k y := by rw [hxfix, hyfix]; abel
      _ = r k (x + y) := by rw [map_add]
      _ = r k v := by rw [hxy]
      _ = v := hfix
      _ = x + y := hxy.symm
  have hneg : -y = y := by
    have h' : x + (-y) = x + y := by simpa [sub_eq_add_neg] using h_eq
    exact (add_left_cancel_iff).mp h'
  have hy0 : y = 0 := by
    have h2y : (2 : ZMod p) • y = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← hneg]
      exact neg_add_cancel y
    exact (smul_eq_zero.mp h2y).resolve_left h2
  rw [hy0, add_zero] at hxy
  exact hxy ▸ hx

private theorem false_of_preserves_of_irred [Module.Finite (ZMod p) U]
    {b : U ≃ₗ[ZMod p] U} {W : Submodule (ZMod p) U}
    (hbW : ∀ v ∈ W, b v ∈ W) (hHgen : ∀ h ∈ H, W.map (h : U →ₗ[ZMod p] U) = W)
    (hWbot : W ≠ ⊥) (hWtop : W ≠ ⊤)
    (hirr : IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤) :
    False := by
  have : FiniteDimensional (ZMod p) U := ‹Module.Finite (ZMod p) U›
  have hbmap : W.map (b : U →ₗ[ZMod p] U) = W := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [LinearEquiv.finrank_map_eq])
    rintro _ ⟨v, hv, rfl⟩
    exact hbW v hv
  have hP : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      W.map (g : U →ₗ[ZMod p] U) = W := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hxH
      · exact hbmap
      · exact hHgen x hxH
    | one => simp
    | mul x y hx hy ihx ihy =>
      rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp,
        ihy, ihx]
    | inv x hx ih =>
      have hle : W.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤ W := by
        rintro _ ⟨v, hv, rfl⟩
        have hv' : v ∈ W.map (x : U →ₗ[ZMod p] U) := by rw [ih]; exact hv
        obtain ⟨y, hy, hyv⟩ := Submodule.mem_map.mp hv'
        rw [← hyv]
        simpa using hy
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [LinearEquiv.finrank_map_eq])
  have hWin : ∀ g ∈ Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))),
      ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    have hm := Submodule.mem_map_of_mem (f := (g : U →ₗ[ZMod p] U)) hw
    rwa [hP g hg] at hm
  rcases hirr W bot_le le_top hWin with hW | hW
  · exact hWbot hW
  · exact hWtop hW

private theorem false_of_b_apply_e0_neg (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    (hneg : b (e 0) = -e 0) : False := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hbroot : HardMathSupport.Kantor79.movedSpace b =
      Submodule.span (ZMod p) {e 0} :=
    movedSpace_eq_span_of_apply_neg h2 hpair.2.2.2.1 (hT.2.2.1.ne_zero 0) hneg
  have he0V : e 0 ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 0).1
      (mem_movedSpace_of_apply_eq_neg h2 (hT.1 0).2.2)
  have hspanle : Submodule.span (ZMod p) {e 0} ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.span_le.mpr (by rintro x rfl; exact he0V)
  have hbV : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b v ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    intro v hv
    have hdiff : b v - v ∈ Submodule.span (ZMod p) {e 0} := by
      rw [← hbroot]
      exact ⟨v, rfl⟩
    have hsum := (HardMathSupport.Kantor79.commutatorSpace H).add_mem
      (hspanle hdiff) hv
    simpa [sub_eq_add_neg, add_assoc] using hsum
  have hHgen : ∀ h ∈ H,
      (HardMathSupport.Kantor79.commutatorSpace H).map (h : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H :=
    fun h hh => map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hh)
  have hfinV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3 :=
    hH.2.1
  have hbot : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfinV
    omega
  have htop : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊤ := by
    intro h
    rw [h, finrank_top, h4] at hfinV
    omega
  exact false_of_preserves_of_irred hbV hHgen hbot htop hpair.2.2.2.2.2

private theorem b_apply_e0 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b) :
    b (e 0) = e 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hb2 : b * b = 1 := hpair.2.2.2.1.1
  have hbinv : b⁻¹ = b := by
    calc b⁻¹ = b⁻¹ * (b * b) := by rw [hb2]; group
      _ = b := by group
  have hcomm : r 0 * b = b * r 0 := hpair.2.2.2.2.1
  have hconj : b * r 0 * b⁻¹ = r 0 := by
    rw [hbinv]
    calc b * r 0 * b = r 0 * b * b := by rw [← hcomm]
      _ = r 0 * (b * b) := by group
      _ = r 0 := by rw [hb2]; group
  have hroot : HardMathSupport.Kantor79.movedSpace (r 0) =
      Submodule.span (ZMod p) {e 0} :=
    movedSpace_eq_span_of_apply_neg h2 (hT.1 0).2.1 (hT.2.2.1.ne_zero 0) (hT.1 0).2.2
  have hmap := movedSpace_conj b (r 0)
  rw [hconj] at hmap
  have hmem : b (e 0) ∈ HardMathSupport.Kantor79.movedSpace (r 0) := by
    rw [hmap]
    refine Submodule.mem_map_of_mem (f := (b : U →ₗ[ZMod p] U)) ?_
    rw [hroot]
    exact Submodule.subset_span (Set.mem_singleton (e 0))
  rw [hroot] at hmem
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c • e 0 = b (e 0) :=
    Submodule.mem_span_singleton.mp hmem
  have hc' : b (e 0) = c • e 0 := hc.symm
  have hsq : c * c = 1 := by
    have h1 : b (b (e 0)) = e 0 := by
      have := congrArg (fun f : U ≃ₗ[ZMod p] U => f (e 0)) hb2
      simpa [LinearEquiv.mul_apply] using this
    rw [hc', map_smul, hc', smul_smul] at h1
    exact LinearIndependent.smul_left_injective (R := ZMod p) (v := e) hT.2.2.1 0
      (by simpa using h1)
  rcases (sq_eq_one_iff (a := c)).mp (by rw [pow_two]; exact hsq) with hc1 | hcneg
  · rw [hc', hc1, one_smul]
  · exfalso
    exact false_of_b_apply_e0_neg hp h4 hH hT hpair (by rw [hc', hcneg, neg_one_smul])

private theorem exists_centralizerSpace_span [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3) :
    ∃ f : U, f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} := by
  have hfin : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := hH.finrank_centralizerSpace
    rw [h4] at h
    omega
  have hne : centralizerSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfin
    omega
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨f, hf0, eq_span_singleton_of_mem_of_finrank_eq_one hfin hfmem hf0⟩

private theorem false_of_preserves_commutatorSpace [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3) {b : U ≃ₗ[ZMod p] U}
    (hbV : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b v ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hirr : IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤) :
    False := by
  have hHgen : ∀ h ∈ H,
      (HardMathSupport.Kantor79.commutatorSpace H).map (h : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H :=
    fun h hh => map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hh)
  have hfinV : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 3 :=
    hH.2.1
  have hbot : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfinV
    omega
  have htop : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊤ := by
    intro h
    rw [h, finrank_top, h4] at hfinV
    omega
  exact false_of_preserves_of_irred hbV hHgen hbot htop hirr

private theorem false_of_preserves_centralizerSpace [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3) {b : U ≃ₗ[ZMod p] U}
    (hbC : ∀ v ∈ centralizerSpace H, b v ∈ centralizerSpace H)
    (hirr : IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤) :
    False := by
  have hHgen : ∀ h ∈ H, (centralizerSpace H).map (h : U →ₗ[ZMod p] U) = centralizerSpace H :=
    fun h hh => map_centralizerSpace_of_mem_normalizer (Subgroup.le_normalizer hh)
  have hfinC : Module.finrank (ZMod p) (centralizerSpace H) = 1 := by
    have h := hH.finrank_centralizerSpace
    rw [h4] at h
    omega
  have hbot : centralizerSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfinC
    omega
  have htop : centralizerSpace H ≠ ⊤ := by
    intro h
    rw [h, finrank_top, h4] at hfinC
    omega
  exact false_of_preserves_of_irred hbC hHgen hbot htop hirr

private theorem false_of_preserves_commutatorSpace_split [Module.Finite (ZMod p) U]
    (hH : SplitSupport H (Module.finrank (ZMod p) U - 1))
    (h4 : 4 ≤ Module.finrank (ZMod p) U) {b : U ≃ₗ[ZMod p] U}
    (hbV : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      b v ∈ HardMathSupport.Kantor79.commutatorSpace H)
    (hirr : IrredOnSection (Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))) ⊥ ⊤) :
    False := by
  have hHgen : ∀ h ∈ H,
      (HardMathSupport.Kantor79.commutatorSpace H).map (h : U →ₗ[ZMod p] U) =
        HardMathSupport.Kantor79.commutatorSpace H :=
    fun h hh => map_commutatorSpace_of_mem_normalizer (Subgroup.le_normalizer hh)
  have hfinV := hH.2.1
  have hbot : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hfinV
    omega
  have htop : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hfinV
    omega
  exact false_of_preserves_of_irred hbV hHgen hbot htop hirr

private theorem map_conj_le_G {b : U ≃ₗ[ZMod p] U} (hb : b ∈ G) (hHG : H ≤ G) :
    H.map (MulAut.conj b).toMonoidHom ≤ G := by
  rintro x ⟨h, hh, rfl⟩
  change b * h * b⁻¹ ∈ G
  exact G.mul_mem (G.mul_mem hb (hHG hh)) (G.inv_mem hb)

private theorem commute_of_root_mem_centralizer (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {t : U ≃ₗ[ZMod p] U} (htG : t ∈ G) (htRefl : IsRefl p t) {w : U}
    (hw : w ∈ centralizerSpace H)
    (hroot : HardMathSupport.Kantor79.movedSpace t = Submodule.span (ZMod p) {w}) :
    ∀ h ∈ H, h * t = t * h := by
  intro h hh
  refine commute_of_movedSpace_le_ker hp hG (hHG hh) htG htRefl ?_
  rw [hroot, Submodule.span_singleton_le_iff_mem]
  change h w - w = 0
  rw [(mem_centralizerSpace.mp hw) h hh, sub_self]

private theorem map_conj_le_centralizer (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {i : Fin 3} (hb : b ∈ G) (hb' : IsRefl p b)
    (hα : b (e i) ∈ centralizerSpace H) :
    H.map (MulAut.conj b).toMonoidHom ≤
      Subgroup.centralizer ({r i} : Set (U ≃ₗ[ZMod p] U)) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hbinv : b⁻¹ = b := by
    calc b⁻¹ = b⁻¹ * (b * b) := by rw [hb'.1]; group
      _ = b := by group
  have htG : b * r i * b⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem hb (hHG (hT.1 i).1)) (G.inv_mem hb)
  have htRefl : IsRefl p (b * r i * b⁻¹) := IsRefl.conj (hT.1 i).2.1 b
  have hroot : HardMathSupport.Kantor79.movedSpace (b * r i * b⁻¹) =
      Submodule.span (ZMod p) {b (e i)} := by
    rw [movedSpace_conj,
      movedSpace_eq_span_of_apply_neg h2 (hT.1 i).2.1 (hT.2.2.1.ne_zero i) (hT.1 i).2.2,
      Submodule.map_span, Set.image_singleton]
    rfl
  have hcommH := commute_of_root_mem_centralizer hp hG hHG htG htRefl hα hroot
  intro x hx
  obtain ⟨h, hh, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (b * h * b⁻¹) * r i = r i * (b * h * b⁻¹)
  have hbt : b * (b * r i * b⁻¹) * b⁻¹ = r i := by
    rw [hbinv]
    calc b * (b * r i * b) * b = (b * b) * r i * (b * b) := by group
      _ = r i := by rw [hb'.1]; group
  have hconj := congrArg (fun y => b * y * b⁻¹) (hcommH h hh)
  calc (b * h * b⁻¹) * r i
      = (b * h * b⁻¹) * (b * (b * r i * b⁻¹) * b⁻¹) := by rw [hbt]
    _ = b * (h * (b * r i * b⁻¹)) * b⁻¹ := by group
    _ = b * ((b * r i * b⁻¹) * h) * b⁻¹ := hconj
    _ = (b * (b * r i * b⁻¹) * b⁻¹) * (b * h * b⁻¹) := by group
    _ = r i * (b * h * b⁻¹) := by rw [hbt]

private theorem reflSubgroupIn_le_map_conj (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3)
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hb : b ∈ G) {i j : Fin 3} (hi : i ≠ 0)
    (hj : j ≠ 0) (hij : i ≠ j) (hbj : b (e j) = e j) (hbe0 : b (e 0) = e 0) :
    reflSubgroupIn p H (LinearMap.ker ((r i : U →ₗ[ZMod p] U) - 1)) ≤
      H.map (MulAut.conj b).toMonoidHom := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVH := span_range_e_eq_commutatorSpace hp hH hT
  have hbfix : ∀ l : Fin 3, l ≠ i → b (e l) = e l := by
    intro l hli
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
  have hbspan : Submodule.span (ZMod p) (e '' ({i}ᶜ : Set (Fin 3))) ≤
      LinearMap.ker ((b : U →ₗ[ZMod p] U) - 1) := by
    rw [Submodule.span_le]
    rintro w ⟨l, hl, rfl⟩
    change ((b : U →ₗ[ZMod p] U) - 1) (e l) = 0
    change b (e l) - e l = 0
    rw [hbfix l (by simpa [eq_comm] using hl), sub_self]
  rw [reflSubgroupIn]
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨htH, htRefl, htW⟩
  have htVH : HardMathSupport.Kantor79.movedSpace t ≤
      HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace htH
  have htSpan : HardMathSupport.Kantor79.movedSpace t ≤
      Submodule.span (ZMod p) (e '' ({i}ᶜ : Set (Fin 3))) := by
    intro v hv
    have hvW : v ∈ LinearMap.ker ((r i : U →ₗ[ZMod p] U) - 1) := by
      obtain ⟨w, rfl⟩ := hv
      exact htW w
    have hvfix : r i v = v := by
      have h := LinearMap.mem_ker.mp hvW
      exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply] using h)
    exact mem_span_compl_of_fixed h2 hVH hT (htVH hv) hvfix
  have hbt : b * t = t * b :=
    commute_of_movedSpace_le_ker hp hG hb (hHG htH) htRefl (le_trans htSpan hbspan)
  refine ⟨t, htH, ?_⟩
  change b * t * b⁻¹ = t
  calc b * t * b⁻¹ = (t * b) * b⁻¹ := by rw [hbt]
    _ = t := by group

private theorem coeff_eq_of_smul_add_eq {a b c d : ZMod p} {v w : U} (hv : v ≠ 0)
    (hw : w ∉ Submodule.span (ZMod p) {v})
    (h : a • v + b • w = c • v + d • w) : a = c ∧ b = d := by
  have hlin : LinearIndependent (ZMod p) ![v, w] :=
    (LinearIndependent.pair_iff' hv).mpr fun a ha =>
      hw (ha ▸ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v)))
  exact LinearIndependent.eq_of_pair hlin h

private theorem f_not_mem_span_e (hp : p ≠ 2) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {f : U} (hfne : f ≠ 0)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f}) (i : Fin 3) :
    f ∉ Submodule.span (ZMod p) {e i} := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have heiV : e i ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 i).1
      (mem_movedSpace_of_apply_eq_neg h2 (hT.1 i).2.2)
  have hspanle : Submodule.span (ZMod p) {e i} ≤ HardMathSupport.Kantor79.commutatorSpace H :=
    Submodule.span_le.mpr (by rintro x rfl; exact heiV)
  intro hfmem
  have hfV : f ∈ HardMathSupport.Kantor79.commutatorSpace H := hspanle hfmem
  have hfC : f ∈ centralizerSpace H := by rw [hfspan]; exact Submodule.mem_span_singleton_self f
  have hbot : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
    hH.1.disjoint.eq_bot
  have hfbot : f ∈ (⊥ : Submodule (ZMod p) U) := by
    rw [← hbot]
    exact ⟨hfV, hfC⟩
  exact hfne (by simpa using hfbot)

private theorem b_apply_block_first (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U} {f : U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {i j : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) (hbj : b (e j) = e j)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    (hα : b (e i) ∉ centralizerSpace H) :
    ∃ α γ : ZMod p, α ≠ 0 ∧ γ ≠ 0 ∧ b (e i) = α • e i + γ • f := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hbe0 := b_apply_e0 hp h4 hH hT hpair
  have hmem : b (e i) ∈ Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
    have h1 : b (e i) - e i ∈ Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H :=
      hbi ⟨e i, rfl⟩
    have h2' : e i ∈ Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H :=
      Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton (e i)))
    have hsum := Submodule.add_mem
      (Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H) h1 h2'
    simpa [sub_eq_add_neg, add_assoc] using hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨a, ha⟩ : ∃ a : ZMod p, a • e i = x :=
    Submodule.mem_span_singleton.mp hx
  have hyC : y ∈ centralizerSpace H := hy
  rw [hfspan] at hy
  obtain ⟨c, hc⟩ : ∃ c : ZMod p, c • f = y :=
    Submodule.mem_span_singleton.mp hy
  have hformula : b (e i) = a • e i + c • f := by rw [← hxy, ha, hc]
  refine ⟨a, c, ?_, ?_, hformula⟩
  · intro ha0; apply hα
    rw [hformula, ha0, zero_smul, zero_add]
    simpa [hc] using hyC
  · intro hc0
    have hformula' : b (e i) = a • e i := by rw [hformula, hc0, zero_smul, add_zero]
    apply false_of_preserves_commutatorSpace h4 hH ?_ hpair.2.2.2.2.2
    have hVH := span_range_e_eq_commutatorSpace hp hH hT
    have heV : ∀ l : Fin 3, e l ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      fun l => HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 l).1
        (mem_movedSpace_of_apply_eq_neg h2 (hT.1 l).2.2)
    intro v hv
    have hv' : v ∈ Submodule.span (ZMod p) (Set.range e) := by rwa [← hVH]
    have hmaple : (Submodule.span (ZMod p) (Set.range e)).map (b : U →ₗ[ZMod p] U) ≤
        HardMathSupport.Kantor79.commutatorSpace H := by
      rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      have hae : a • e i ∈ HardMathSupport.Kantor79.commutatorSpace H :=
        Submodule.smul_mem _ _ (heV i)
      fin_cases i <;> fin_cases j <;> fin_cases l <;>
        simp_all
    exact hmaple (Submodule.mem_map_of_mem (f := (b : U →ₗ[ZMod p] U)) hv')

private theorem b_apply_block_second_data (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {b : U ≃ₗ[ZMod p] U}
    {f : U} {i : Fin 3} (hfne : f ≠ 0)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    {α γ : ZMod p} (hformula : b (e i) = α • e i + γ • f) (hb2 : b * b = 1) :
    ∃ β δ : ZMod p, b f = β • e i + δ • f ∧ α * γ + γ * δ = 0 ∧
      α * α + γ * β = 1 := by
  have hbfmem : b f ∈ Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H := by
    have h1 : b f - f ∈ HardMathSupport.Kantor79.movedSpace b := ⟨f, rfl⟩
    have hs := hbi h1
    have hfC : f ∈ centralizerSpace H := by
      rw [hfspan]
      exact Submodule.subset_span (Set.mem_singleton f)
    have hsum := Submodule.add_mem
      (Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H) hs
      (Submodule.mem_sup_right hfC)
    simpa [sub_eq_add_neg, add_assoc] using hsum
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hbfmem
  obtain ⟨β, hβ⟩ : ∃ β : ZMod p, β • e i = x :=
    Submodule.mem_span_singleton.mp hx
  rw [hfspan] at hy
  obtain ⟨δ, hδ⟩ : ∃ δ : ZMod p, δ • f = y :=
    Submodule.mem_span_singleton.mp hy
  have hformula_f : b f = β • e i + δ • f := by rw [← hxy, hβ, hδ]
  have hb_apply : b (b (e i)) = e i := by
    have := congrArg (fun g : U ≃ₗ[ZMod p] U => g (e i)) hb2
    simpa [LinearEquiv.mul_apply] using this
  have hexp : b (b (e i)) = (α * α + γ * β) • e i + (α * γ + γ * δ) • f := by
    rw [hformula, map_add, map_smul, map_smul, hformula, hformula_f]
    module
  have hcoeff : (α * α + γ * β) • e i + (α * γ + γ * δ) • f =
      (1 : ZMod p) • e i + (0 : ZMod p) • f := by
    rw [one_smul, zero_smul, add_zero]
    exact hexp.symm.trans hb_apply
  exact ⟨β, δ, hformula_f, (coeff_eq_of_smul_add_eq (a := α * α + γ * β)
    (b := α * γ + γ * δ) (c := 1) (d := 0) (v := e i) (w := f)
    (hT.2.2.1.ne_zero i) (f_not_mem_span_e hp hH hT hfne hfspan i) hcoeff).2,
    (coeff_eq_of_smul_add_eq (a := α * α + γ * β) (b := α * γ + γ * δ) (c := 1)
      (d := 0) (v := e i) (w := f) (hT.2.2.1.ne_zero i)
      (f_not_mem_span_e hp hH hT hfne hfspan i) hcoeff).1⟩

private theorem b_apply_block_second (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {f : U} {i : Fin 3} (hfne : f ≠ 0)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f})
    {α γ : ZMod p} (hγ0 : γ ≠ 0) (hformula : b (e i) = α • e i + γ • f) :
    ∃ β : ZMod p, β ≠ 0 ∧ b f = β • e i + (-α) • f ∧ α * α + β * γ = 1 ∧
      α ≠ 1 ∧ α ≠ -1 := by
  have hb2 : b * b = 1 := hpair.2.2.2.1.1
  obtain ⟨β, δ, hbf, hcγ, hcα⟩ :=
    b_apply_block_second_data hp hH hT hfne hbi hfspan hformula hb2
  have hfac : γ * (α + δ) = 0 := by
    rw [mul_add]
    linear_combination hcγ
  have hsum0 : α + δ = 0 := (mul_eq_zero.mp hfac).resolve_left hγ0
  have hδ : δ = -α := by
    rw [eq_neg_iff_add_eq_zero]
    rw [add_comm] at hsum0
    exact hsum0
  have hbf' : b f = β • e i + (-α) • f := by rw [hbf, hδ]
  have hβ0 : β ≠ 0 := by
    intro hβ
    apply false_of_preserves_centralizerSpace h4 hH ?_ hpair.2.2.2.2.2
    intro v hv
    rw [hfspan] at hv ⊢
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    rw [← hc, map_smul, hbf', hβ, zero_smul, zero_add, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton f))
  have hβγ : β * γ ≠ 0 := mul_ne_zero hβ0 hγ0
  have hcα' : α * α + β * γ = 1 := by simpa [mul_comm] using hcα
  have hαsq_ne : α ^ 2 ≠ 1 := by
    intro h
    apply hβγ
    have hαα : α * α = 1 := by simpa [pow_two] using h
    have h1 : (1 : ZMod p) + β * γ = 1 + 0 := by
      rw [hαα] at hcα'
      simpa using hcα'
    exact add_left_cancel h1
  exact ⟨β, hβ0, hbf', hcα', (sq_ne_one_iff.mp hαsq_ne).1,
    (sq_ne_one_iff.mp hαsq_ne).2⟩

private theorem b_conj_apply {b c : U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {i j : Fin 3}
    {f : U} {α γ β : ZMod p}
    (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0) (hc0 : c (e 0) = e i)
    (hfC : f ∈ centralizerSpace H) (hbe0 : b (e 0) = e 0) (hbj : b (e j) = e j)
    (hbei : b (e i) = α • e i + γ • f) (hbf : b f = β • e i + (-α) • f) :
    (c * b * c⁻¹) (e 0) = e 0 ∧ (c * b * c⁻¹) (e i) = e i ∧
      (c * b * c⁻¹) (e j) = α • e j + γ • f ∧
      (c * b * c⁻¹) f = β • e j + (-α) • f := by
  have hcf : c f = f := (mem_centralizerSpace.mp hfC) c hc
  have hcinv0 : c⁻¹ (e 0) = e j := by rw [← hcj]; simp
  have hcinvi : c⁻¹ (e i) = e 0 := by rw [← hc0]; simp
  have hcinvj : c⁻¹ (e j) = e i := by rw [← hci]; simp
  have hcinvf : c⁻¹ f = f := by
    simpa using congrArg (fun x => c⁻¹ x) hcf.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc (c * b * c⁻¹) (e 0) = c (b (c⁻¹ (e 0))) := by simp [LinearEquiv.mul_apply]
      _ = c (b (e j)) := by rw [hcinv0]
      _ = c (e j) := by rw [hbj]
      _ = e 0 := hcj
  · calc (c * b * c⁻¹) (e i) = c (b (c⁻¹ (e i))) := by simp [LinearEquiv.mul_apply]
      _ = c (b (e 0)) := by rw [hcinvi]
      _ = c (e 0) := by rw [hbe0]
      _ = e i := hc0
  · calc (c * b * c⁻¹) (e j) = c (b (c⁻¹ (e j))) := by simp [LinearEquiv.mul_apply]
      _ = c (b (e i)) := by rw [hcinvj]
      _ = c (α • e i + γ • f) := by rw [hbei]
      _ = α • e j + γ • f := by rw [map_add, map_smul, map_smul, hci, hcf]
  · calc (c * b * c⁻¹) f = c (b (c⁻¹ f)) := by simp [LinearEquiv.mul_apply]
      _ = c (b f) := by rw [hcinvf]
      _ = c (β • e i + (-α) • f) := by rw [hbf]
      _ = β • e j + (-α) • f := by rw [map_add, map_smul, map_smul, hci, hcf]

private theorem b_conj_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b c : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    {i j : Fin 3} {f : U} {α γ β : ZMod p}
    (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0) (hc0 : c (e 0) = e i)
    (hfC : f ∈ centralizerSpace H) (hbe0 : b (e 0) = e 0) (hbj : b (e j) = e j)
    (hbei : b (e i) = α • e i + γ • f) (hbf : b f = β • e i + (-α) • f)
    (hbrefl : IsRefl p b) (hβ0 : β ≠ 0)
    (hsum : α * α + β * γ = 1) :
    IsRefl p (c * b * c⁻¹) ∧
      HardMathSupport.Kantor79.movedSpace (c * b * c⁻¹) =
        Submodule.span (ZMod p) {β • e j + (-(α + 1)) • f} ∧
      β • e j + (-(α + 1)) • f ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hbap := b_conj_apply hc hci hcj hc0 hfC hbe0 hbj hbei hbf
  have htRefl : IsRefl p (c * b * c⁻¹) := IsRefl.conj hbrefl c
  have hw : (c * b * c⁻¹) (β • e j + (-(α + 1)) • f) =
      -(β • e j + (-(α + 1)) • f) := by
    rw [map_add, map_smul, map_smul, hbap.2.2.1, hbap.2.2.2]
    simp only [smul_add, smul_smul, add_smul, neg_smul]
    have hβγ : β * γ = 1 - α * α := by linear_combination hsum
    rw [hβγ]
    module
  have hwne : β • e j + (-(α + 1)) • f ≠ 0 := by
    intro hzero
    have hejV : e j ∈ HardMathSupport.Kantor79.commutatorSpace H :=
      HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 j).1
        (mem_movedSpace_of_apply_eq_neg h2 (hT.1 j).2.2)
    have hA : β • e j = -(-(α + 1) • f) := eq_neg_of_add_eq_zero_left hzero
    have hβVC : β • e j ∈ centralizerSpace H := by
      rw [hA]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ (-(α + 1)) hfC)
    have hejC : e j ∈ centralizerSpace H := by
      have hm := Submodule.smul_mem _ (β⁻¹) hβVC
      rwa [smul_smul, inv_mul_cancel₀ hβ0, one_smul] at hm
    have hbot : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
      hH.1.disjoint.eq_bot
    have : e j ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hbot]
      exact ⟨hejV, hejC⟩
    exact (hT.2.2.1.ne_zero j) (by simpa using this)
  refine ⟨htRefl, ?_, hwne⟩
  exact movedSpace_eq_span_of_apply_neg h2 htRefl hwne hw

private theorem b1_root (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b c : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U}
    {α γ β : ZMod p} (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0)
    (hc0 : c (e 0) = e i) (hfC : f ∈ centralizerSpace H) (hbe0 : b (e 0) = e 0)
    (hbj : b (e j) = e j) (hbei : b (e i) = α • e i + γ • f)
    (hbf : b f = β • e i + (-α) • f) (hbrefl : IsRefl p b) (hβ0 : β ≠ 0)
    (hsum : α * α + β * γ = 1) :
    IsRefl p (b * (c * b * c⁻¹) * b) ∧
      HardMathSupport.Kantor79.movedSpace (b * (c * b * c⁻¹) * b) =
        Submodule.span (ZMod p) {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f} ∧
      β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let bp : U ≃ₗ[ZMod p] U := c * b * c⁻¹
  let w' : U := β • e j + (-(α + 1)) • f
  have hconj := b_conj_root hp hH hT hc hci hcj hc0 hfC hbe0 hbj hbei hbf hbrefl hβ0 hsum
  have hconj' : IsRefl p bp ∧ HardMathSupport.Kantor79.movedSpace bp =
      Submodule.span (ZMod p) {w'} ∧ w' ≠ 0 := by
    simpa [bp, w'] using hconj
  have hbinv : b⁻¹ = b := by
    calc b⁻¹ = b⁻¹ * (b * b) := by rw [hbrefl.1]; group
      _ = b := by group
  have hb1eq : b * bp * b = b * bp * b⁻¹ := by rw [hbinv]
  have hrefl1 : IsRefl p (b * bp * b) := by
    rw [hb1eq]
    exact IsRefl.conj hconj'.1 b
  have hw : b w' = β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f := by
    simp only [w', map_add, map_smul, hbj, hbf]
    module
  have hb1moved : HardMathSupport.Kantor79.movedSpace (b * bp * b) =
      Submodule.span (ZMod p) {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f} := by
    rw [hb1eq, movedSpace_conj, hconj'.2.1, Submodule.map_span, Set.image_singleton,
      show (b : U →ₗ[ZMod p] U) w' =
        β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f from hw]
  have hwne : β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ≠ 0 := by
    intro hzero
    have hfin : Module.finrank (ZMod p)
        (Submodule.span (ZMod p) {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f}) = 1 := by
      rw [← hb1moved]
      exact hrefl1.2
    rw [hzero, Submodule.span_zero_singleton, finrank_bot] at hfin
    omega
  refine ⟨?_, ?_, hwne⟩
  · simpa [bp] using hrefl1
  · simpa [bp] using hb1moved

private theorem smul_add_ne_zero_of_notMem {a b : ZMod p} {v w : U}
    (hw : w ∉ Submodule.span (ZMod p) {v}) (hb : b ≠ 0) : a • v + b • w ≠ 0 := by
  intro hzero
  have hbw : b • w = -(a • v) := by
    rw [add_comm] at hzero
    exact eq_neg_of_add_eq_zero_left hzero
  have hwspan : w = (-(b⁻¹ * a)) • v := by
    calc w = b⁻¹ • (b • w) := by rw [smul_smul, inv_mul_cancel₀ hb, one_smul]
      _ = b⁻¹ • (-(a • v)) := by rw [hbw]
      _ = (-(b⁻¹ * a)) • v := by
          rw [smul_neg, smul_smul]
          module
  exact hw (by rw [hwspan]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))

private theorem b1_apply_moves_e0_ei (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b c : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U}
    {α γ β : ZMod p} (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0)
    (hc0 : c (e 0) = e i) (hfC : f ∈ centralizerSpace H) (hfne : f ≠ 0)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f}) (hbe0 : b (e 0) = e 0)
    (hbj : b (e j) = e j) (hbei : b (e i) = α • e i + γ • f)
    (hbf : b f = β • e i + (-α) • f) (hbrefl : IsRefl p b)
    (hγ0 : γ ≠ 0) (hα1 : α ≠ -1) :
    (b * (c * b * c⁻¹) * b) (e 0) = e 0 ∧
      (b * (c * b * c⁻¹) * b) (e i) ≠ e i := by
  have hbinv : b⁻¹ = b := by
    calc b⁻¹ = b⁻¹ * (b * b) := by rw [hbrefl.1]; group
      _ = b := by group
  have hbap := b_conj_apply hc hci hcj hc0 hfC hbe0 hbj hbei hbf
  let bp : U ≃ₗ[ZMod p] U := c * b * c⁻¹
  have hbpap : bp (e 0) = e 0 ∧ bp (e i) = e i ∧ bp (e j) = α • e j + γ • f ∧
      bp f = β • e j + (-α) • f := by simpa [bp] using hbap
  have hαp1 : α + 1 ≠ 0 := by intro h; apply hα1; linear_combination h
  have hfspanj := f_not_mem_span_e hp hH hT hfne hfspan j
  refine ⟨?_, ?_⟩
  · calc (b * bp * b) (e 0) = b (bp (b (e 0))) := by simp [LinearEquiv.mul_apply]
      _ = b (bp (e 0)) := by rw [hbe0]
      _ = b (e 0) := by rw [hbpap.1]
      _ = e 0 := hbe0
  · intro heq
    have hbp : bp (b (e i)) = b (e i) := by
      calc bp (b (e i)) = b⁻¹ (b (bp (b (e i)))) := by simp
        _ = b⁻¹ ((b * bp * b) (e i)) := by simp [bp, LinearEquiv.mul_apply]
        _ = b⁻¹ (e i) := by rw [heq]
        _ = b (e i) := by rw [hbinv]
    rw [hbei, map_add, map_smul, map_smul, hbpap.2.1, hbpap.2.2.2] at hbp
    have hγeq : γ • (β • e j + (-α) • f) = γ • f := add_left_cancel hbp
    have hXsub : (β • e j + (-α) • f) - f = 0 := by
      have hsub : γ • ((β • e j + (-α) • f) - f) = 0 := by
        rw [smul_sub, hγeq, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left hγ0
    have hX : β • e j + (-α) • f = f := sub_eq_zero.mp hXsub
    have hzero : β • e j + (-(α + 1)) • f = 0 := by
      rw [show β • e j + (-(α + 1)) • f = (β • e j + (-α) • f) - f by module, hX, sub_self]
    exact (smul_add_ne_zero_of_notMem hfspanj (neg_ne_zero.mpr hαp1)) hzero

private theorem b1_apply_moves_ej_f (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b c : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U}
    {α γ β : ZMod p} (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0)
    (hc0 : c (e 0) = e i) (hfC : f ∈ centralizerSpace H) (hfne : f ≠ 0)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f}) (hbe0 : b (e 0) = e 0)
    (hbj : b (e j) = e j) (hbei : b (e i) = α • e i + γ • f)
    (hbf : b f = β • e i + (-α) • f) (hbrefl : IsRefl p b)
    (hα0 : α ≠ 0) (hγ0 : γ ≠ 0) (hα1 : α ≠ -1) :
    (b * (c * b * c⁻¹) * b) (e j) ≠ e j ∧
      (b * (c * b * c⁻¹) * b) f ≠ f := by
  have hbinv : b⁻¹ = b := by
    calc b⁻¹ = b⁻¹ * (b * b) := by rw [hbrefl.1]; group
      _ = b := by group
  have hbap := b_conj_apply hc hci hcj hc0 hfC hbe0 hbj hbei hbf
  let bp : U ≃ₗ[ZMod p] U := c * b * c⁻¹
  have hbpap : bp (e 0) = e 0 ∧ bp (e i) = e i ∧ bp (e j) = α • e j + γ • f ∧
      bp f = β • e j + (-α) • f := by simpa [bp] using hbap
  have hαp1 : α + 1 ≠ 0 := by intro h; apply hα1; linear_combination h
  have hfspanj := f_not_mem_span_e hp hH hT hfne hfspan j
  refine ⟨?_, ?_⟩
  · intro heq
    have hbp : bp (e j) = e j := by
      calc bp (e j) = b⁻¹ (b (bp (e j))) := by simp
        _ = b⁻¹ ((b * bp * b) (e j)) := by simp [bp, LinearEquiv.mul_apply, hbj]
        _ = b⁻¹ (e j) := by rw [heq]
        _ = e j := by rw [hbinv, hbj]
    rw [hbpap.2.2.1] at hbp
    have hzero : (α - 1) • e j + γ • f = 0 := by
      rw [show (α - 1) • e j + γ • f = α • e j + γ • f - e j by module, hbp, sub_self]
    exact (smul_add_ne_zero_of_notMem hfspanj hγ0) hzero
  · intro heq
    have hbp : bp (b f) = b f := by
      calc bp (b f) = b⁻¹ (b (bp (b f))) := by simp
        _ = b⁻¹ ((b * bp * b) f) := by simp [bp, LinearEquiv.mul_apply]
        _ = b⁻¹ f := by rw [heq]
        _ = b f := by rw [hbinv]
    rw [hbf, map_add, map_smul, map_smul, hbpap.2.1, hbpap.2.2.2] at hbp
    have hαeq : (-α) • (β • e j + (-α) • f) = (-α) • f := add_left_cancel hbp
    have hXsub : (β • e j + (-α) • f) - f = 0 := by
      have hsub : (-α) • ((β • e j + (-α) • f) - f) = 0 := by
        rw [smul_sub, hαeq, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left (neg_ne_zero.mpr hα0)
    have hX : β • e j + (-α) • f = f := sub_eq_zero.mp hXsub
    have hzero : (-α * β) • e j + (α * (α + 1)) • f = 0 := by
      rw [show (-α * β) • e j + (α * (α + 1)) • f =
        (-α) • (β • e j + (-α) • f) + α • f by module, hX, ← add_smul]
      rw [show -α + α = (0 : ZMod p) by abel, zero_smul]
    exact (smul_add_ne_zero_of_notMem hfspanj (mul_ne_zero hα0 hαp1)) hzero

private theorem b1_commute_r0 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {b1 : U ≃ₗ[ZMod p] U} (hb1G : b1 ∈ G)
    (hb1e0 : b1 (e 0) = e 0) :
    r 0 * b1 = b1 * r 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hroot : HardMathSupport.Kantor79.movedSpace (r 0) =
      Submodule.span (ZMod p) {e 0} :=
    movedSpace_eq_span_of_apply_neg h2 (hT.1 0).2.1 (hT.2.2.1.ne_zero 0) (hT.1 0).2.2
  have hcomm := commute_of_movedSpace_le_ker hp hG hb1G (hHG (hT.1 0).1) (hT.1 0).2.1 ?_
  · exact hcomm.symm
  · rw [hroot, Submodule.span_singleton_le_iff_mem]
    change b1 (e 0) - e 0 = 0
    rw [hb1e0, sub_self]

private theorem b1_root_not_mem (hp : p ≠ 2) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U}
    {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    {i j : Fin 3} {f : U} {α β : ZMod p} (hfC : f ∈ centralizerSpace H) (hfne : f ≠ 0)
    (hα0 : α ≠ 0) (hα1 : α ≠ -1) :
    β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ∉
      HardMathSupport.Kantor79.commutatorSpace H := by
  have hαp1 : α + 1 ≠ 0 := by intro h; apply hα1; linear_combination h
  have hcoef : α * (α + 1) ≠ 0 := mul_ne_zero hα0 hαp1
  intro hwV
  have heiV : e i ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 i).1
      (mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) (hT.1 i).2.2)
  have hejV : e j ∈ HardMathSupport.Kantor79.commutatorSpace H :=
    HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hT.1 j).1
      (mem_movedSpace_of_apply_eq_neg (ZMod.prime_ne_zero p 2 hp) (hT.1 j).2.2)
  have hfV : f ∈ HardMathSupport.Kantor79.commutatorSpace H := by
    have h1 : (α * (α + 1)) • f =
        (β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f) -
          β • e j - (-(α + 1) * β) • e i := by module
    have hmem : (α * (α + 1)) • f ∈ HardMathSupport.Kantor79.commutatorSpace H := by
      rw [h1]
      exact (HardMathSupport.Kantor79.commutatorSpace H).sub_mem
        ((HardMathSupport.Kantor79.commutatorSpace H).sub_mem hwV
          (Submodule.smul_mem _ _ hejV))
        (Submodule.smul_mem _ _ heiV)
    have hm := Submodule.smul_mem (HardMathSupport.Kantor79.commutatorSpace H)
      ((α * (α + 1))⁻¹) hmem
    rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at hm
  have hfC' : f ∈ centralizerSpace H := hfC
  have hbot : HardMathSupport.Kantor79.commutatorSpace H ⊓ centralizerSpace H = ⊥ :=
    hH.1.disjoint.eq_bot
  have : f ∈ (⊥ : Submodule (ZMod p) U) := by
    rw [← hbot]
    exact ⟨hfV, hfC'⟩
  exact hfne (by simpa using this)

private theorem r_mem_reflSubgroupIn (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {k : Fin 3} (hk : k ≠ 0) :
    r k ∈ reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hroot : HardMathSupport.Kantor79.movedSpace (r k) =
      Submodule.span (ZMod p) {e k} :=
    movedSpace_eq_span_of_apply_neg h2 (hT.1 k).2.1 (hT.2.2.1.ne_zero k) (hT.1 k).2.2
  have hekW : e k ∈ LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1) := by
    change r 0 (e k) - e k = 0
    rw [apply_e_of_ne h2 hT (by simpa [eq_comm] using hk), sub_self]
  refine Subgroup.subset_closure ⟨(hT.1 k).1, (hT.1 k).2.1, ?_⟩
  intro v
  exact (Submodule.span_singleton_le_iff_mem (e k) _).mpr hekW (by
    rw [← hroot]; exact ⟨v, rfl⟩)

private theorem commutatorSpace_reflSubgroupIn_eq_span (hp : p ≠ 2)
    [Module.Finite (ZMod p) U] (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3}
    (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) =
      Submodule.span (ZMod p) ({e i, e j} : Set U) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hVH := span_range_e_eq_commutatorSpace hp hH hT
  set W : Submodule (ZMod p) U := LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)
  have hmem : ∀ k : Fin 3, k ≠ 0 → r k ∈ reflSubgroupIn p H W :=
    fun k hk => r_mem_reflSubgroupIn hp hT hk
  have hle : Submodule.span (ZMod p) ({e i, e j} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W) := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hmem i hi)
        (mem_movedSpace_of_apply_eq_neg h2 (hT.1 i).2.2)
    · exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace (hmem j hj)
        (mem_movedSpace_of_apply_eq_neg h2 (hT.1 j).2.2)
  refine le_antisymm ?_ hle
  have hVH0le : HardMathSupport.Kantor79.commutatorSpace (reflSubgroupIn p H W) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro x ⟨g, hg, v, rfl⟩
    exact Submodule.subset_span ⟨g, reflSubgroupIn_le H W hg, v, rfl⟩
  have hset : (e '' ({0}ᶜ : Set (Fin 3))) = ({e i, e j} : Set U) := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro ⟨l, hl, rfl⟩
      fin_cases i <;> fin_cases j <;> fin_cases l <;> simp_all
    · rintro (rfl | rfl)
      · exact ⟨i, by simpa using hi, rfl⟩
      · exact ⟨j, by simpa using hj, rfl⟩
  intro v hv
  have hvW : v ∈ W := commutatorSpace_reflSubgroupIn_le H W hv
  have hvfix : r 0 v = v := by
    have h := LinearMap.mem_ker.mp hvW
    exact sub_eq_zero.mp (by simpa [W, LinearMap.sub_apply] using h)
  have hmem' := mem_span_compl_of_fixed h2 hVH hT (hVH0le hv) hvfix
  rwa [hset] at hmem'

private theorem commutatorSpace_closure_insert_le {S : Submodule (ZMod p) U}
    {b : U ≃ₗ[ZMod p] U} {K : Subgroup (U ≃ₗ[ZMod p] U)}
    (hK : HardMathSupport.Kantor79.commutatorSpace K ≤ S)
    (hb : HardMathSupport.Kantor79.movedSpace b ≤ S) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert b (K : Set (U ≃ₗ[ZMod p] U)))) ≤ S := by
  rw [commutatorSpace_le_iff]
  have hP : ∀ g ∈ Subgroup.closure (insert b (K : Set (U ≃ₗ[ZMod p] U))),
      ∀ v, g v - v ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hxK
      · intro v; exact hb ⟨v, rfl⟩
      · intro v; exact (commutatorSpace_le_iff.mp hK) x hxK v
    | one => intro v; simp
    | mul x y hx hy ihx ihy =>
      intro v
      have h1 := ihx (y v)
      have h2 := ihy v
      have heq : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
        rw [LinearEquiv.mul_apply]
        abel
      rw [heq]
      exact S.add_mem h1 h2
    | inv x hx ih =>
      intro v
      have h := ih (x⁻¹ v)
      have heq : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
      rw [heq]
      exact S.neg_mem (by simpa using h)
  exact hP

private theorem commutatorSpace_closure_b1_le [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {b c : U ≃ₗ[ZMod p] U}
    {i j : Fin 3} {f : U} {α β : ZMod p}
    (hVH0 : HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) =
      Submodule.span (ZMod p) ({e i, e j} : Set U))
    (hb1moved : HardMathSupport.Kantor79.movedSpace (b * (c * b * c⁻¹) * b) =
      Submodule.span (ZMod p)
        {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f}) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) ≤
      Submodule.span (ZMod p) ({e i, e j, f} : Set U) := by
  apply commutatorSpace_closure_insert_le
  · rw [hVH0, Submodule.span_le]
    rintro x (rfl | rfl) <;> exact Submodule.subset_span (by simp)
  · rw [hb1moved, Submodule.span_singleton_le_iff_mem]
    refine Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem closure_b1_ei_ej_mem [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {b c : U ≃ₗ[ZMod p] U}
    {i j : Fin 3} (hVH0 : HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) =
      Submodule.span (ZMod p) ({e i, e j} : Set U)) :
    e i ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) ∧
      e j ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
          (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
  have hVH0le : HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) ≤
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.span_le]
    rintro x ⟨g, hg, v, rfl⟩
    exact Submodule.subset_span ⟨g, Subgroup.subset_closure
      (Set.mem_insert_of_mem _ hg), v, rfl⟩
  exact ⟨hVH0le (by rw [hVH0]; exact Submodule.subset_span (by simp)),
    hVH0le (by rw [hVH0]; exact Submodule.subset_span (by simp))⟩

private theorem f_mem_closure_b1 {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {b c : U ≃ₗ[ZMod p] U} {i j : Fin 3} {f : U} {α β : ZMod p}
    (hcoef : α * (α + 1) ≠ 0)
    (hwV : β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ∈
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))))
    (heiV : e i ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
          (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))))
    (hejV : e j ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
          (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U))))) :
    f ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
  have h1 : (α * (α + 1)) • f =
      (β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f) -
        β • e j - (-(α + 1) * β) • e i := by module
  have hmem : (α * (α + 1)) • f ∈ HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure
          (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
    rw [h1]
    exact (HardMathSupport.Kantor79.commutatorSpace _).sub_mem
      ((HardMathSupport.Kantor79.commutatorSpace _).sub_mem hwV
        (Submodule.smul_mem _ _ hejV))
      (Submodule.smul_mem _ _ heiV)
  have hm := Submodule.smul_mem (HardMathSupport.Kantor79.commutatorSpace _)
    ((α * (α + 1))⁻¹) hmem
  rwa [smul_smul, inv_mul_cancel₀ hcoef, one_smul] at hm

private theorem commutatorSpace_closure_b1_ge [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {b c : U ≃ₗ[ZMod p] U} {i j : Fin 3} {f : U}
    {α β : ZMod p}
    (hVH0 : HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) =
      Submodule.span (ZMod p) ({e i, e j} : Set U))
    (hb1moved : HardMathSupport.Kantor79.movedSpace (b * (c * b * c⁻¹) * b) =
      Submodule.span (ZMod p)
        {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f})
    (hα0 : α ≠ 0) (hα1 : α ≠ -1) :
    Submodule.span (ZMod p) ({e i, e j, f} : Set U) ≤
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
  have hαp1 : α + 1 ≠ 0 := by intro h; apply hα1; linear_combination h
  have hcoef : α * (α + 1) ≠ 0 := mul_ne_zero hα0 hαp1
  obtain ⟨heiV, hejV⟩ := closure_b1_ei_ej_mem hVH0
  have hwV : β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ∈
      HardMathSupport.Kantor79.commutatorSpace (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) := by
    apply HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (by rw [Set.mem_insert_iff]; exact Or.inl rfl))
    rw [hb1moved]
    exact Submodule.subset_span (by simp)
  have hfV := f_mem_closure_b1 hcoef hwV heiV hejV
  rw [Submodule.span_le]
  rintro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h
  · rw [h]; exact heiV
  · rw [h]; exact hejV
  · rw [h]; exact hfV

private theorem commutatorSpace_closure_b1_eq [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {b c : U ≃ₗ[ZMod p] U}
    {i j : Fin 3} {f : U} {α β : ZMod p}
    (hVH0 : HardMathSupport.Kantor79.commutatorSpace
        (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1))) =
      Submodule.span (ZMod p) ({e i, e j} : Set U))
    (hb1moved : HardMathSupport.Kantor79.movedSpace (b * (c * b * c⁻¹) * b) =
      Submodule.span (ZMod p)
        {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f})
    (hα0 : α ≠ 0) (hα1 : α ≠ -1) :
    HardMathSupport.Kantor79.commutatorSpace
        (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U)))) =
      Submodule.span (ZMod p) ({e i, e j, f} : Set U) :=
  le_antisymm (commutatorSpace_closure_b1_le hVH0 hb1moved)
    (commutatorSpace_closure_b1_ge hVH0 hb1moved hα0 hα1)

private theorem exists_coord_of_mem_span3 {a b c x : U}
    (hx : x ∈ Submodule.span (ZMod p) ({a, b, c} : Set U)) :
    ∃ s t u : ZMod p, x = s • a + t • b + u • c := by
  obtain ⟨s, z1, hz1, rfl⟩ := Submodule.mem_span_insert.mp hx
  obtain ⟨t, z2, hz2, rfl⟩ := Submodule.mem_span_insert.mp hz1
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp hz2
  refine ⟨s, t, u, ?_⟩
  rw [← hu]
  abel

private theorem mem_of_two_smul_mem (h2 : (2 : ZMod p) ≠ 0)
    {W : Submodule (ZMod p) U} {x : U} (h : (2 : ZMod p) • x ∈ W) : x ∈ W := by
  have hm := Submodule.smul_mem W ((2 : ZMod p)⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ h2, one_smul] at hm

private theorem coord_mem_of_invariant (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3}
    (hij : i ≠ j) {f : U} (hfC : f ∈ centralizerSpace H)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hriB : r i ∈ B) (hrjB : r j ∈ B) (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X)
    {a b c : ZMod p} (hx : a • e i + b • e j + c • f ∈ X) :
    a • e i ∈ X ∧ b • e j ∈ X ∧ c • f ∈ X := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have heiC : r i (e i) = -e i := (hT.1 i).2.2
  have hejC : r i (e j) = e j := apply_e_of_ne h2 hT hij
  have hfC' : r i f = f := (mem_centralizerSpace.mp hfC) (r i) (hT.1 i).1
  have heiC' : r j (e i) = e i := apply_e_of_ne h2 hT hij.symm
  have hejC' : r j (e j) = -e j := (hT.1 j).2.2
  have hfC'' : r j f = f := (mem_centralizerSpace.mp hfC) (r j) (hT.1 j).1
  have hri_x : r i (a • e i + b • e j + c • f) = (-a) • e i + b • e j + c • f := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, heiC, hejC, hfC']
    module
  have hrj_x : r j (a • e i + b • e j + c • f) = a • e i + (-b) • e j + c • f := by
    rw [map_add, map_add, map_smul, map_smul, map_smul, heiC', hejC', hfC'']
    module
  have h2a : (2 : ZMod p) • (a • e i) ∈ X := by
    have h := X.sub_mem hx (hXinv _ hriB _ hx)
    convert h using 1
    rw [hri_x]
    module
  have h2b : (2 : ZMod p) • (b • e j) ∈ X := by
    have h := X.sub_mem hx (hXinv _ hrjB _ hx)
    convert h using 1
    rw [hrj_x]
    module
  have h2bc : (2 : ZMod p) • (b • e j + c • f) ∈ X := by
    have h := X.add_mem hx (hXinv _ hriB _ hx)
    convert h using 1
    rw [hri_x]
    module
  have hbj : b • e j ∈ X := mem_of_two_smul_mem h2 h2b
  have hbc : b • e j + c • f ∈ X := mem_of_two_smul_mem h2 h2bc
  refine ⟨mem_of_two_smul_mem h2 h2a, hbj, ?_⟩
  have h := X.sub_mem hbc hbj
  convert h using 1
  abel

private theorem coord_decomp_of_invariant (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3}
    (hij : i ≠ j) {f : U} (hfC : f ∈ centralizerSpace H)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hriB : r i ∈ B) (hrjB : r j ∈ B)
    (hXle : X ≤ Submodule.span (ZMod p) ({e i, e j, f} : Set U))
    (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X) :
    X = (X ⊓ Submodule.span (ZMod p) {e i}) ⊔ (X ⊓ Submodule.span (ZMod p) {e j}) ⊔
      (X ⊓ Submodule.span (ZMod p) {f}) := by
  refine le_antisymm ?_ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  intro x hx
  obtain ⟨a, b, c, rfl⟩ := exists_coord_of_mem_span3 (hXle hx)
  obtain ⟨hai, hbj, hcf⟩ := coord_mem_of_invariant hp hT hij hfC hriB hrjB hXinv hx
  have h1 : a • e i ∈ X ⊓ Submodule.span (ZMod p) {e i} :=
    ⟨hai, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (e i)))⟩
  have h2 : b • e j ∈ X ⊓ Submodule.span (ZMod p) {e j} :=
    ⟨hbj, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (e j)))⟩
  have h3 : c • f ∈ X ⊓ Submodule.span (ZMod p) {f} :=
    ⟨hcf, Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton f))⟩
  have h12 : a • e i + b • e j ∈
      (X ⊓ Submodule.span (ZMod p) {e i}) ⊔ (X ⊓ Submodule.span (ZMod p) {e j}) :=
    Submodule.add_mem_sup h1 h2
  exact Submodule.add_mem_sup h12 h3

private theorem coord_lines_le_of_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3}
    (hij : i ≠ j) {f : U} (hfC : f ∈ centralizerSpace H)
    {B : Subgroup (U ≃ₗ[ZMod p] U)} {X : Submodule (ZMod p) U}
    (hriB : r i ∈ B) (hrjB : r j ∈ B) (hXinv : ∀ g ∈ B, ∀ x ∈ X, g x ∈ X)
    {a b c : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hx : a • e i + b • e j + c • f ∈ X) :
    Submodule.span (ZMod p) {e i} ≤ X ∧ Submodule.span (ZMod p) {e j} ≤ X ∧
      Submodule.span (ZMod p) {f} ≤ X := by
  obtain ⟨hai, hbj, hcf⟩ := coord_mem_of_invariant hp hT hij hfC hriB hrjB hXinv hx
  have heiX : e i ∈ X := by
    have h := Submodule.smul_mem X (a⁻¹) hai
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
  have hejX : e j ∈ X := by
    have h := Submodule.smul_mem X (b⁻¹) hbj
    rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at h
  have hfX : f ∈ X := by
    have h := Submodule.smul_mem X (c⁻¹) hcf
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  exact ⟨Submodule.span_le.mpr (by rintro x rfl; exact heiX),
    Submodule.span_le.mpr (by rintro x rfl; exact hejX),
    Submodule.span_le.mpr (by rintro x rfl; exact hfX)⟩

private theorem le_of_inf_ne_bot {L X : Submodule (ZMod p) U} (hL : IsAtom L)
    (h : X ⊓ L ≠ ⊥) : L ≤ X := by
  rw [← (hL.ne_bot_iff_eq inf_le_right).mp h]
  exact inf_le_left

private theorem exists_coord_line_le {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U}
    (hfne : f ≠ 0) {X : Submodule (ZMod p) U}
    (hdec : X = (X ⊓ Submodule.span (ZMod p) {e i}) ⊔
        (X ⊓ Submodule.span (ZMod p) {e j}) ⊔ (X ⊓ Submodule.span (ZMod p) {f}))
    (hX0 : X ≠ ⊥) :
    Submodule.span (ZMod p) {e i} ≤ X ∨ Submodule.span (ZMod p) {e j} ≤ X ∨
      Submodule.span (ZMod p) {f} ≤ X := by
  have hatom_i : IsAtom (Submodule.span (ZMod p) {e i}) := by
    rw [Submodule.isAtom_iff_finrank_eq_one, finrank_span_singleton (hT.2.2.1.ne_zero i)]
  have hatom_j : IsAtom (Submodule.span (ZMod p) {e j}) := by
    rw [Submodule.isAtom_iff_finrank_eq_one, finrank_span_singleton (hT.2.2.1.ne_zero j)]
  have hatom_f : IsAtom (Submodule.span (ZMod p) {f}) := by
    rw [Submodule.isAtom_iff_finrank_eq_one, finrank_span_singleton hfne]
  have hsome : X ⊓ Submodule.span (ZMod p) {e i} ≠ ⊥ ∨
      X ⊓ Submodule.span (ZMod p) {e j} ≠ ⊥ ∨ X ⊓ Submodule.span (ZMod p) {f} ≠ ⊥ := by
    by_contra h
    push Not at h
    apply hX0
    rw [hdec, h.1, h.2.1, h.2.2]
    simp
  rcases hsome with h | h | h
  · exact Or.inl (le_of_inf_ne_bot hatom_i h)
  · exact Or.inr (Or.inl (le_of_inf_ne_bot hatom_j h))
  · exact Or.inr (Or.inr (le_of_inf_ne_bot hatom_f h))

private theorem irredOnSection_closure_insert_b1 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U}
    {α β : ZMod p} (hij : i ≠ j) (hfC : f ∈ centralizerSpace H) (hfne : f ≠ 0)
    (hα0 : α ≠ 0) (hα1 : α ≠ -1) (hβ0 : β ≠ 0)
    {b1 : U ≃ₗ[ZMod p] U} {B : Subgroup (U ≃ₗ[ZMod p] U)}
    (hriB : r i ∈ B) (hrjB : r j ∈ B) (hb1B : b1 ∈ B)
    (hb1moved : HardMathSupport.Kantor79.movedSpace b1 =
      Submodule.span (ZMod p)
        {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f})
    (hb1refl : IsRefl p b1) (hb1_ei : b1 (e i) ≠ e i) (hb1_ej : b1 (e j) ≠ e j)
    (hb1_f : b1 f ≠ f)
    (hV_B : HardMathSupport.Kantor79.commutatorSpace B =
      Submodule.span (ZMod p) ({e i, e j, f} : Set U)) :
    IrredOnSection B ⊥ (HardMathSupport.Kantor79.commutatorSpace B) := by
  have hαp1 : α + 1 ≠ 0 := by intro h; apply hα1; linear_combination h
  have hδ0 : (-(α + 1) * β) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hαp1) hβ0
  have hε0 : α * (α + 1) ≠ 0 := mul_ne_zero hα0 hαp1
  intro X hXbot hXle hXinv
  have hdec := coord_decomp_of_invariant hp hT hij hfC hriB hrjB (by rwa [← hV_B]) hXinv
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  right; by_contra hXV
  have hline := exists_coord_line_le hT hfne hdec hX0
  by_cases hwX : β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f ∈ X
  · have hlines := coord_lines_le_of_mem hp hT hij hfC hriB hrjB hXinv
      (a := -(α + 1) * β) (b := β) (c := α * (α + 1)) hδ0 hβ0 hε0 (by
        convert hwX using 1
        module)
    apply hXV
    rw [hV_B]
    apply le_antisymm (by rwa [← hV_B])
    rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h
    · rw [h]; exact hlines.1 (Submodule.subset_span (Set.mem_singleton (e i)))
    · rw [h]; exact hlines.2.1 (Submodule.subset_span (Set.mem_singleton (e j)))
    · rw [h]; exact hlines.2.2 (Submodule.subset_span (Set.mem_singleton f))
  · have hwnot : ¬ HardMathSupport.Kantor79.movedSpace b1 ≤ X := by
      rw [hb1moved, Submodule.span_singleton_le_iff_mem]
      exact hwX
    have hfix : ∀ x ∈ X, b1 x = x := by
      intro x hx
      exact apply_eq_self_of_not_movedSpace_le hb1refl.2
        (fun y hy => hXinv b1 hb1B y hy) hwnot hx
    rcases hline with h | h | h
    · exact hb1_ei (hfix (e i) (h (Submodule.subset_span (Set.mem_singleton (e i)))))
    · exact hb1_ej (hfix (e j) (h (Submodule.subset_span (Set.mem_singleton (e j)))))
    · exact hb1_f (hfix f (h (Submodule.subset_span (Set.mem_singleton f))))

private theorem finrank_reflSubgroupIn_r0 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) :
    Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)))) = 2 := by
  have hVH0 := commutatorSpace_reflSubgroupIn_eq_span (i := 1) (j := 2) hp hH hT
    (by decide) (by decide) (by decide)
  have hpairlin : LinearIndependent (ZMod p) ![e 1, e 2] :=
    (LinearIndependent.pair_iff' (hT.2.2.1.ne_zero 1)).mpr fun a ha =>
      not_mem_span_singleton_of_ne hT.2.2.1 (by decide)
        (ha ▸ Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (e 1))))
  have hrange : Set.range ![e 1, e 2] = ({e 1, e 2} : Set U) := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      fin_cases k <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  rw [hVH0]
  have hfin := finrank_span_eq_card hpairlin
  rw [hrange] at hfin
  simpa using hfin

private theorem b1_data_block (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) (hpair : IsCommIrredPair p G H (r 0) b)
    {i j : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) (hbj : b (e j) = e j)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hα : b (e i) ∉ centralizerSpace H) :
    ∃ (f : U) (α γ β : ZMod p), f ≠ 0 ∧ centralizerSpace H = Submodule.span (ZMod p) {f} ∧
      α ≠ 0 ∧ γ ≠ 0 ∧ β ≠ 0 ∧ α ≠ -1 ∧ α * α + β * γ = 1 ∧ b (e 0) = e 0 ∧
      b (e i) = α • e i + γ • f ∧ b f = β • e i + (-α) • f := by
  obtain ⟨f, hfne, hfspan⟩ := exists_centralizerSpace_span h4 hH
  have hbe0 := b_apply_e0 hp h4 hH hT hpair
  obtain ⟨α, γ, hα0, hγ0, hbei⟩ :=
    b_apply_block_first hp h4 hH hT hpair hi hj hij hbj hbi hfspan hα
  obtain ⟨β, hβ0, hbf, hαsq, hα1, hαneg⟩ :=
    b_apply_block_second hp h4 hH hT hpair hfne hbi hfspan hγ0 hbei
  exact ⟨f, α, γ, β, hfne, hfspan, hα0, hγ0, hβ0, hαneg, hαsq, hbe0, hbei, hbf⟩

private theorem b1_data_moves (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hHG : H ≤ G) (hH : SplitSupport H 3)
    {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U} {s b c : U ≃ₗ[ZMod p] U}
    (hT : IsCyclicRootTriple p H r e s) {i j : Fin 3} {f : U} {α γ β : ZMod p}
    (hc : c ∈ H) (hci : c (e i) = e j) (hcj : c (e j) = e 0) (hc0 : c (e 0) = e i)
    (hfC : f ∈ centralizerSpace H) (hfne : f ≠ 0)
    (hfspan : centralizerSpace H = Submodule.span (ZMod p) {f}) (hbe0 : b (e 0) = e 0)
    (hbj : b (e j) = e j) (hbei : b (e i) = α • e i + γ • f)
    (hbf : b f = β • e i + (-α) • f) (hbrefl : IsRefl p b) (hbG : b ∈ G)
    (hα0 : α ≠ 0) (hγ0 : γ ≠ 0) (hβ0 : β ≠ 0) (hαneg : α ≠ -1)
    (hαsq : α * α + β * γ = 1) :
    IsRefl p (b * (c * b * c⁻¹) * b) ∧
      HardMathSupport.Kantor79.movedSpace (b * (c * b * c⁻¹) * b) =
        Submodule.span (ZMod p)
          {β • e j + (-(α + 1) * β) • e i + (α * (α + 1)) • f} ∧
      (b * (c * b * c⁻¹) * b) (e 0) = e 0 ∧
      (b * (c * b * c⁻¹) * b) (e i) ≠ e i ∧
      (b * (c * b * c⁻¹) * b) (e j) ≠ e j ∧
      (b * (c * b * c⁻¹) * b) f ≠ f ∧
      b * (c * b * c⁻¹) * b ∈ G := by
  have hb1root := b1_root hp hH hT hc hci hcj hc0 hfC hbe0 hbj hbei hbf hbrefl hβ0 hαsq
  have hb1moves1 := b1_apply_moves_e0_ei hp hH hT hc hci hcj hc0 hfC hfne hfspan hbe0 hbj
    hbei hbf hbrefl hγ0 hαneg
  have hb1moves2 := b1_apply_moves_ej_f hp hH hT hc hci hcj hc0 hfC hfne hfspan hbe0 hbj
    hbei hbf hbrefl hα0 hγ0 hαneg
  refine ⟨hb1root.1, hb1root.2.1, hb1moves1.1, hb1moves1.2, hb1moves2.1,
    hb1moves2.2, ?_⟩
  exact G.mul_mem (G.mul_mem hbG (G.mul_mem (G.mul_mem (hHG hc) hbG)
    (G.inv_mem (hHG hc)))) hbG

theorem isCentralizingSplit_map_conj (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hHr : ReflGen p H) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {i j : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (hbj : b (e j) = e j)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hα : b (e i) ∈ centralizerSpace H) :
    IsCentralizingSplit p G H (H.map (MulAut.conj b).toMonoidHom) (r i) := by
  have _ := hbi
  have hbe0 := b_apply_e0 hp h4 hH hT hpair
  refine ⟨map_conj_le_G hpair.2.2.1 hHG, reflGen_map_conj b hHr,
    (by simpa [h4] using splitSupport_map_conj b hH),
    map_conj_le_centralizer hp hG hHG hT hpair.2.2.1 hpair.2.2.2.1 hα,
    reflSubgroupIn_le_map_conj hp hH hG hHG hT hpair.2.2.1 hi hj hij hbj hbe0⟩

theorem isCentralizingSplit_closure_insert_conj (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hHr : ReflGen p H) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) {i j : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j)
    (hbj : b (e j) = e j)
    (hbi : HardMathSupport.Kantor79.movedSpace b ≤
      Submodule.span (ZMod p) {e i} ⊔ centralizerSpace H)
    (hα : b (e i) ∉ centralizerSpace H) {c : U ≃ₗ[ZMod p] U} (hc : c ∈ H)
    (hci : c (e i) = e j) (hcj : c (e j) = e 0) (hc0 : c (e 0) = e i) :
    IsCentralizingSplit p G H (Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))) (r 0) := by
  have _ := hHr; obtain ⟨f, α, γ, β, hfne, hfspan, hα0, hγ0, hβ0, hαneg, hαsq, hbe0, hbei, hbf⟩ :=
    b1_data_block hp h4 hH hT hpair hi hj hij hbj hbi hα
  have hfC : f ∈ centralizerSpace H := by rw [hfspan]; exact Submodule.mem_span_singleton_self f
  obtain ⟨hb1refl, hb1moved, hb1e0, hb1ei, hb1ej, hb1f, hb1G⟩ :=
    b1_data_moves hp hHG hH hT hc hci hcj hc0 hfC hfne hfspan hbe0 hbj hbei hbf
      hpair.2.2.2.1 hpair.2.2.1 hα0 hγ0 hβ0 hαneg hαsq
  let B : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert (b * (c * b * c⁻¹) * b)
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))
  have hVH0 := commutatorSpace_reflSubgroupIn_eq_span hp hH hT hi hj hij
  have hV_B : HardMathSupport.Kantor79.commutatorSpace B =
      Submodule.span (ZMod p) ({e i, e j, f} : Set U) :=
    commutatorSpace_closure_b1_eq hVH0 hb1moved hα0 hαneg
  have hdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)))) + 2 =
      Module.finrank (ZMod p) U := by
    rw [finrank_reflSubgroupIn_r0 hp hH hT, h4]
  have hriB : r i ∈ B := Subgroup.subset_closure (by
    rw [Set.mem_insert_iff]
    exact Or.inr (r_mem_reflSubgroupIn hp hT hi))
  have hrjB : r j ∈ B := Subgroup.subset_closure (by
    rw [Set.mem_insert_iff]
    exact Or.inr (r_mem_reflSubgroupIn hp hT hj))
  have hb1B : b * (c * b * c⁻¹) * b ∈ B := Subgroup.subset_closure (by
    rw [Set.mem_insert_iff]
    exact Or.inl rfl)
  have hirr : IrredOnSection B ⊥ (HardMathSupport.Kantor79.commutatorSpace B) :=
    irredOnSection_closure_insert_b1 (s := s) hp hT
      hij hfC hfne hα0 hαneg hβ0 hriB hrjB hb1B hb1moved hb1refl hb1ei hb1ej hb1f hV_B
  exact isCentralizingSplit_of_irredOnSection (hp := hp) (hG := hG) (hHG := hHG)
    (hH := by simpa [h4] using hH) (hh := (hT.1 0).1) (hh' := (hT.1 0).2.1)
    (hb := hb1G) (hb' := hb1refl) (hhb := b1_commute_r0 hp hG hHG hT hb1G hb1e0)
    (hbH := by
      rw [hb1moved, Submodule.span_singleton_le_iff_mem]
      exact b1_root_not_mem hp hH hT hfC hfne hα0 hαneg)
    (hdim := hdim) (hirr := hirr)

theorem exists_isCentralizingSplit_four (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h4 : Module.finrank (ZMod p) U = 4) (hG : QTwoLin.TransvectionFree G) (hHG : H ≤ G)
    (hHr : ReflGen p H) (hH : SplitSupport H 3) {r : Fin 3 → U ≃ₗ[ZMod p] U} {e : Fin 3 → U}
    {s b : U ≃ₗ[ZMod p] U} (hT : IsCyclicRootTriple p H r e s)
    (hpair : IsCommIrredPair p G H (r 0) b) :
    ∃ i : Fin 3, ∃ B : Subgroup (U ≃ₗ[ZMod p] U), IsCentralizingSplit p G H B (r i) := by
  let B0 : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert b
      (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
        Set (U ≃ₗ[ZMod p] U)))
  by_cases hirr : IrredOnSection B0 ⊥ (HardMathSupport.Kantor79.commutatorSpace B0)
  · refine ⟨0, B0, ?_⟩
    refine isCentralizingSplit_of_irredOnSection (hp := hp) (hG := hG) (hHG := hHG)
      (hH := by simpa [h4] using hH) (hh := (hT.1 0).1) (hh' := (hT.1 0).2.1)
      (hb := hpair.2.2.1) (hb' := hpair.2.2.2.1) (hhb := hpair.2.2.2.2.1) (hbH := ?_)
      (hdim := ?_) (hirr := hirr)
    · intro hle
      apply false_of_preserves_commutatorSpace h4 hH ?_ hpair.2.2.2.2.2
      intro v hv
      have hdiff : b v - v ∈ HardMathSupport.Kantor79.commutatorSpace H := hle ⟨v, rfl⟩
      have hsum := (HardMathSupport.Kantor79.commutatorSpace H).add_mem hdiff hv
      simpa [sub_eq_add_neg, add_assoc] using hsum
    · rw [finrank_reflSubgroupIn_r0 hp hH hT, h4]
  · obtain ⟨i, j, hi, hj, hij, hbj, hbi⟩ :=
      exists_fix_of_not_irredOnSection hp h4 hG hHG hH hT hpair hirr
    by_cases hα : b (e i) ∈ centralizerSpace H
    · exact ⟨i, H.map (MulAut.conj b).toMonoidHom,
        isCentralizingSplit_map_conj hp h4 hG hHG hHr hH hT hpair hi hj hij hbj hbi hα⟩
    · have hcases : (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
        fin_cases i <;> fin_cases j <;> simp_all
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨0, Subgroup.closure (insert (b * (s * b * s⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U))), ?_⟩
        exact isCentralizingSplit_closure_insert_conj hp h4 hG hHG hHr hH hT hpair hi hj hij
          hbj hbi hα (c := s) hT.2.2.2.1 (hT.2.2.2.2 1) (hT.2.2.2.2 2) (hT.2.2.2.2 0)
      · refine ⟨0, Subgroup.closure (insert (b * (s⁻¹ * b * (s⁻¹)⁻¹) * b)
          (reflSubgroupIn p H (LinearMap.ker ((r 0 : U →ₗ[ZMod p] U) - 1)) :
            Set (U ≃ₗ[ZMod p] U))), ?_⟩
        have hs1 : s (e 1) = e 2 := by simpa using hT.2.2.2.2 1
        have hs0 : s (e 0) = e 1 := by simpa using hT.2.2.2.2 0
        have hs2 : s (e 2) = e 0 := by simpa using hT.2.2.2.2 2
        refine isCentralizingSplit_closure_insert_conj hp h4 hG hHG hHr hH hT hpair hi hj hij
          hbj hbi hα (c := s⁻¹) (H.inv_mem hT.2.2.2.1) ?_ ?_ ?_
        · simpa using (congrArg (fun x => s⁻¹ x) hs1).symm
        · simpa using (congrArg (fun x => s⁻¹ x) hs0).symm
        · simpa using (congrArg (fun x => s⁻¹ x) hs2).symm

theorem exists_isCentralizingSplit (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {z : U ≃ₗ[ZMod p] U} {S : Set (U ≃ₗ[ZMod p] U)} (hF : LemmaTwoThreeFrame p G H z S)
    (hCD : (∃ τ ∈ S, IsCaseCRefl p H z τ) ∨ ∃ τ h', IsCaseDPair p H z τ h')
    (hG : ReflGen p G) (hirr : IrredOnSection G ⊥ ⊤)
    (hstab : ∀ h ∈ H, IsRefl p h →
      (Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
          (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)))) + 2 =
          Module.finrank (ZMod p) U ∧
        IrredOnSection (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))) ⊥
          (HardMathSupport.Kantor79.commutatorSpace
            (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1))))) ∨
      (Module.finrank (ZMod p) U = 4 ∧
        ∃ (r : Fin 3 → U ≃ₗ[ZMod p] U) (e : Fin 3 → U) (s : U ≃ₗ[ZMod p] U),
          r 0 = h ∧ IsCyclicRootTriple p H r e s)) :
    ∃ h ∈ H, IsRefl p h ∧ ∃ B : Subgroup (U ≃ₗ[ZMod p] U), IsCentralizingSplit p G H B h := by
  obtain ⟨a, haG, haRefl, haH, haH'⟩ :=
    LemmaTwoThreeFrame.exists_isRefl_not_le hp hF hG hirr
  obtain ⟨h, b, hpair⟩ :=
    LemmaTwoThreeFrame.exists_isCommIrredPair hp hF hCD haG haRefl haH haH'
  rcases hstab h hpair.1 hpair.2.1 with ⟨hdim, hirrH⟩ | ⟨h4, r, e, s, hT0, hT⟩
  · let B : Subgroup (U ≃ₗ[ZMod p] U) :=
      Subgroup.closure (insert b
        (reflSubgroupIn p H (LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)) :
          Set (U ≃ₗ[ZMod p] U)))
    refine ⟨h, hpair.1, hpair.2.1, B, ?_⟩
    refine isCentralizingSplit_of_irredOnSection (hp := hp) (hG := hF.transvectionFree)
      (hHG := hF.le) (hH := hF.splitSupport) (hh := hpair.1) (hh' := hpair.2.1)
      (hb := hpair.2.2.1) (hb' := hpair.2.2.2.1) (hhb := hpair.2.2.2.2.1)
      (hbH := ?_) (hdim := hdim) (hirr := ?_)
    · intro hle
      apply false_of_preserves_commutatorSpace_split hF.splitSupport hF.four_le ?_
        hpair.2.2.2.2.2
      intro v hv
      have hdiff : b v - v ∈ HardMathSupport.Kantor79.commutatorSpace H := hle ⟨v, rfl⟩
      have hsum := (HardMathSupport.Kantor79.commutatorSpace H).add_mem hdiff hv
      simpa [sub_eq_add_neg, add_assoc] using hsum
    · exact irredOnSection_closure_insert_reflSubgroupIn hp hF.transvectionFree hF.le
        hF.splitSupport hpair hdim hirrH
  · obtain ⟨i, B, hB⟩ := exists_isCentralizingSplit_four hp h4 hF.transvectionFree hF.le hF.reflGen
      (by simpa [h4] using hF.splitSupport) hT (by rwa [hT0])
    exact ⟨r i, (hT.1 i).1, (hT.1 i).2.1, B, hB⟩

end CFSG.StandardType.ZS

end
