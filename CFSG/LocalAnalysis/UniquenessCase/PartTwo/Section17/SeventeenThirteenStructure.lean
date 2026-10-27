module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirteenDiagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin
open CFSG.SignalizerFunctorTheorem.McBride
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem isComponent_barImage_of_mem_calC {D : Data G} {H : Subgroup G} {U : Subgroup G}
    (hUH : U ≤ H) (hHM : H ≤ D.M) (hU : U ∈ calC D.M) :
    CFSG.IsComponent ((U.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
  obtain ⟨hsub, hperf, hq⟩ := hU
  have hsubH : CFSG.Open.IsSubnormal U H := by
    have h1 : CFSG.Assembly.IsSubnormal (U ⊓ H) (D.M ⊓ H) :=
      CFSG.Assembly.IsSubnormal.inf (CFSG.Assembly.isSubnormal_iff_open.mpr hsub) H
    rw [inf_eq_left.mpr hUH, inf_eq_right.mpr hHM] at h1
    exact CFSG.Assembly.isSubnormal_iff_open.mp h1
  obtain ⟨hsnTop, -, hqsub, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_subgroupOf (M := H)
      (show U ∈ calC H from ⟨hsubH, hperf, hq⟩)
  exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.isComponent_image (Y := ↥H) hsnTop hqsub

theorem barImage_sup_barImage_eq_top {H T X : Subgroup G} (hH : H = T ⊔ X) (hXH : X ≤ H) :
    (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⊔
      CFSG.LocalAnalysis.WeakClosure81.barImage H T = ⊤ := by
  have hsup : T.subgroupOf H ⊔ X.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := T) (A' := X) (B := H) (hH ▸ le_sup_left) hXH, hH,
      Subgroup.subgroupOf_self]
  have hmap := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) hsup
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _
    (QuotientGroup.mk'_surjective _)] at hmap
  rw [← hmap]
  exact sup_comm ..

theorem gap17_13_component_of_case_one {D : Data G} (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) {H : Subgroup G}
    (hH : H ∈ Delta17_12 D (fundPred q) r q L) (h1 : P17_12_1 r q L) :
    ∃ K : Subgroup (Bar2 H), CFSG.IsComponent K ∧
      orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
        CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤ := by
  classical
  rw [Delta17_12, dif_pos h1] at hH
  obtain ⟨x, hxM, rfl⟩ := hH
  set U : Subgroup G := L.map (MulAut.conj x).toMonoidHom with hU
  have hUcal : U ∈ calC D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map D.M (MulAut.conj x)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.mp
        (Subgroup.le_normalizer hxM)) hC.memL
  have hLM : L ≤ D.M := hC.memL.1.le
  have hUM : U ≤ D.M := by
    rw [hU, Subgroup.map_le_iff_le_comap]
    intro y hy
    rw [Subgroup.mem_comap]
    exact D.M.mul_mem (D.M.mul_mem hxM (hLM hy)) (D.M.inv_mem hxM)
  have hHM : D.T ⊔ U ≤ D.M := sup_le D.sylowM.le hUM
  refine ⟨(U.subgroupOf (D.T ⊔ U)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(D.T ⊔ U))),
    isComponent_barImage_of_mem_calC le_sup_right hHM hUcal, ?_⟩
  set K : Subgroup (Bar2 (D.T ⊔ U)) :=
    (U.subgroupOf (D.T ⊔ U)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(D.T ⊔ U))) with hK
  have hgen : K ⊔ CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T = ⊤ := by
    have h := barImage_sup_barImage_eq_top (H := D.T ⊔ U) (T := D.T) (X := U) rfl le_sup_right
    rw [hK]
    exact h
  have hid : K.map (MulAut.conj (1 : Bar2 (D.T ⊔ U))).toMonoidHom = K := by
    have hmap : (MulAut.conj (1 : Bar2 (D.T ⊔ U))).toMonoidHom =
        MonoidHom.id (Bar2 (D.T ⊔ U)) := by
      ext x
      simp
    rw [hmap, Subgroup.map_id]
  have hle : K ≤ orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T) := by
    have hmem : (1 : Bar2 (D.T ⊔ U)) ∈
        CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T := by
      rw [CFSG.LocalAnalysis.WeakClosure81.barImage]
      exact Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr (D.T.one_mem))
    have h1' := le_iSup₂ (f := fun a : Bar2 (D.T ⊔ U) =>
      fun _ : a ∈ CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T =>
        K.map (MulAut.conj a).toMonoidHom) (1 : Bar2 (D.T ⊔ U)) hmem
    rw [hid] at h1'
    exact h1'
  have htop : K ⊔ CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T ≤
      orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T) ⊔
        CFSG.LocalAnalysis.WeakClosure81.barImage (D.T ⊔ U) D.T :=
    sup_le (hle.trans le_sup_left) le_sup_right
  rw [hgen] at htop
  exact top_le_iff.mp htop

@[expose] def Gap17_13_structure_remaining (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q) : Prop :=
  (∀ H ∈ Delta17_12 D (fundPred q) r q L, ¬ P17_12_1 r q L →
    ∃ K : Subgroup (Bar2 H),
      CFSG.IsComponent K ∧
        orbitClosure K (CFSG.LocalAnalysis.WeakClosure81.barImage H D.T) ⊔
          CFSG.LocalAnalysis.WeakClosure81.barImage H D.T = ⊤) ∧
  (∀ H ∈ Delta17_12 D (fundPred q) r q L,
    HasOddComponentShapes (↥(⊤ : Subgroup (Bar2 H))) q)

theorem gap17_13_structure_of_remaining (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ)
    (hC : Ctx17_6 D V₀ V L r q) (h : Gap17_13_structure_remaining D V₀ V L r q hC) :
    Gap17_13_structure D V₀ V L r q hC := by
  intro H hH
  refine ⟨?_, h.2 H hH⟩
  by_cases h1 : P17_12_1 r q L
  · exact gap17_13_component_of_case_one V₀ V L r q hC hH h1
  · exact h.1 H hH h1

theorem seventeen_thirteen_of_inputs (D : Data G)
    (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h9 : R17_9At D V₀ V L r q hC)
    (hRee : K_ReeSylowGeneration) (hFunNe : K_FunNonempty)
    (h43c : W3Lem45_2Chief)
    (h410 : W4Lem4_10)
    (hrank57 : CFSG.ComponentClassification.GSThmB.CFAutL2Rank)
    (hrankAll : CFSG.ComponentClassification.GSThmB.CFL2Rank)
    (h411 : W4Lem4_11Prime)
    (hstr : Gap17_13_structure_remaining D V₀ V L r q hC) :
    R17_13At D (fundPred q) V₀ V L r q hC :=
  seventeen_thirteen_of_diagonal D V₀ V L r q hC h9 hRee hFunNe h43c h410 hrank57 hrankAll h411
    (gap17_13_structure_of_remaining D V₀ V L r q hC hstr)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
