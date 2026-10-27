module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs
import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
import CFSG.RankThree.GF2n.Stroth80.Sec4Model
import CFSG.RankThree.GF2n.Smith81.Sec217Perfect
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.Models.PGLSimple
import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_perfect_lift_of_surjective {Γ Γ' : Type*} [Group Γ] [Group Γ'] [Finite Γ]
    (π : Γ →* Γ') (hπ : Function.Surjective π) {C : Subgroup Γ'} (hC : ⁅C, C⁆ = C) :
    ∃ D : Subgroup Γ, ⁅D, D⁆ = D ∧ D.map π = C := by
  classical
  have hex : ∃ k : ℕ, ∃ D : Subgroup Γ, D.map π = C ∧ Nat.card D = k :=
    ⟨_, C.comap π, Subgroup.map_comap_eq_self_of_surjective hπ C, rfl⟩
  obtain ⟨D, hDC, hDk⟩ := Nat.find_spec hex
  refine ⟨D, ?_, hDC⟩
  have hle : ⁅D, D⁆ ≤ D := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    exact D.mul_mem (D.mul_mem (D.mul_mem hg hh) (D.inv_mem hg)) (D.inv_mem hh)
  have hmap : (⁅D, D⁆).map π = C := by rw [Subgroup.map_commutator, hDC, hC]
  have hmin := Nat.find_min' hex ⟨⁅D, D⁆, hmap, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hDk]; exact hmin)

theorem le_bar_H0_of_perfect [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {P : Subgroup (Mbar M Q)} (hP : ⁅P, P⁆ = P) : P ≤ bar M Q (H0 M Z) := by
  obtain ⟨D, hD, hDP⟩ := exists_perfect_lift_of_surjective (QuotientGroup.mk' (Q.subgroupOf M))
    (QuotientGroup.mk'_surjective _) hP
  have hD' : ⁅D.map M.subtype, D.map M.subtype⁆ = D.map M.subtype := by
    rw [← Subgroup.map_commutator, hD]
  haveI : Group.IsPerfect ↥(D.map M.subtype) := Subgroup.isPerfect_iff.mpr hD'
  have hcomm := Smith81.perfect_centralizes_of_semilinAct (Smith81.semilinAct_Z hc.hyp)
    (P := D.map M.subtype) (fun x hx => by obtain ⟨y, -, rfl⟩ := hx; exact y.2) inferInstance
  rw [← hDP]
  rintro _ ⟨d, hd, rfl⟩
  refine ⟨d, Subgroup.mem_subgroupOf.mpr
    (Subgroup.mem_inf.mpr ⟨d.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩), rfl⟩
  exact (hcomm d ⟨d, hd, rfl⟩ z hz).symm

theorem normal_inSubgroup_fstar {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) [H.Normal] :
    (inSubgroup generalizedFitting H).Normal := by
  refine ⟨fun x hx m => ?_⟩
  obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
  have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥H)).1
  have hmap := Subgroup.characteristic_iff_map_eq.mp hchar (MulAut.conjNormal m)
  have hmem : (MulAut.conjNormal m) x' ∈ generalizedFitting ↥H := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hx'
  exact Subgroup.mem_map.mpr ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩

theorem layer_eq_inSubgroup_fstar {Γ : Type} [Group Γ] [Finite Γ] (H : Subgroup Γ) [H.Normal]
    (hna : ∃ a b : ↥(generalizedFitting ↥H), a * b ≠ b * a)
    [hS : IsSimpleGroup ↥(generalizedFitting ↥H)]
    (hP : ∀ P : Subgroup Γ, ⁅P, P⁆ = P → P ≤ H) :
    layer Γ = inSubgroup generalizedFitting H := by
  classical
  have hXn : (inSubgroup generalizedFitting H).Normal := normal_inSubgroup_fstar H
  let eX : ↥(generalizedFitting ↥H) ≃* ↥(inSubgroup generalizedFitting H) :=
    (generalizedFitting ↥H).equivMapOfInjective H.subtype H.subtype_injective
  obtain ⟨hFq, hFc⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna
  have hXq : CFSG.IsQuasisimple ↥(inSubgroup generalizedFitting H) :=
    CFSG.IsQuasisimple.of_mulEquiv eX.symm hFq
  have hXc : CFSG.IsComponent (inSubgroup generalizedFitting H) := ⟨hXq, hXn.isSubnormal⟩
  apply le_antisymm
  · rw [layer.eq_sSup]
    refine sSup_le fun C hC => ?_
    rcases CFSG.LocalCores.distinct_components_commute hC hXc with h | h
    · exact h.le
    · have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hC.1.1
      have hCH : C ≤ H := hP C hCperf
      have hCc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      intro c hc
      have hcX : ∀ x ∈ inSubgroup generalizedFitting H, x * c = c * x := fun x hx =>
        Subgroup.mem_centralizer_iff.mp (hCc hc) x hx
      have hcF : (⟨c, hCH hc⟩ : ↥H) ∈ generalizedFitting ↥H := by
        refine CFSG.centralizer_generalizedFitting_le ↥H ?_
        refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
        exact Subtype.ext (hcX f ⟨f, hf, rfl⟩)
      have hcz : (⟨⟨c, hCH hc⟩, hcF⟩ : ↥(generalizedFitting ↥H)) ∈
          Subgroup.center ↥(generalizedFitting ↥H) := by
        refine Subgroup.mem_center_iff.mpr fun g => ?_
        refine Subtype.ext (Subtype.ext ?_)
        exact hcX g.1 ⟨g.1, g.2, rfl⟩
      rw [hFc, Subgroup.mem_bot] at hcz
      have hc1 : c = 1 := congrArg (fun y : ↥(generalizedFitting ↥H) => (y : Γ)) hcz
      rw [hc1]
      exact (inSubgroup generalizedFitting H).one_mem
  · rw [layer.eq_sSup]
    exact le_sSup hXc

theorem nonabelian_of_simple_of_perfect {X : Type} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI : IsMulCommutative X := ⟨⟨fun a b => hcon a b⟩⟩
  exact Group.IsPerfect.not_isMulCommutative X inferInstance

theorem isSimpleGroup_of_isPSLModel {q : ℕ} {X : Type} [Group X] (h : IsPSLModel 6 q X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨K, _, _, -, ⟨e⟩⟩ := h
  haveI hs : IsSimpleGroup (StatedProj (StatedSL 6 K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by norm_num)
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
  haveI : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K) :=
    CFSG.LinearGroups.linear_projective_perfect (by norm_num) (Or.inl (by norm_num))
  haveI hp : Group.IsPerfect (StatedProj (StatedSL 6 K)) :=
    Group.IsPerfect.ofSurjective
      (f := (projectiveSpecialLinearGroupEquivStatedProj 6 K).toMonoidHom)
      (MulEquiv.surjective _)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  haveI : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨inferInstance, nonabelian_of_simple_of_perfect⟩

theorem isSimpleGroup_of_isPSUModel {n : ℕ} {X : Type} [Group X] (h : IsPSUModel 6 (2 ^ n) X) :
    IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have hK' : Nat.card K = (2 ^ n) ^ 2 := hK
  have hnq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := by simp
  haveI hs : IsSimpleGroup (StatedProj (StatedSU 6 (2 ^ n) K)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 n hK' 6 (by norm_num) hnq
  haveI : Group.IsPerfect (StatedSU 6 (2 ^ n) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := n) hK' (n := 6)
      (by norm_num) hnq
  haveI hp : Group.IsPerfect (StatedProj (StatedSU 6 (2 ^ n) K)) := inferInstance
  haveI : IsSimpleGroup X := e.isSimpleGroup
  haveI : Group.IsPerfect X :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨inferInstance, nonabelian_of_simple_of_perfect⟩

@[expose] def Stroth12FStarLBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q →
    ((OmegaMinusNat hc t 3 ∧ FStarU6 M Q Z) ∨ (OmegaPlusNat hc t 3 ∧ FStarL6 M Q Z)) →
    bar M Q (LB M Q B) ≤ inSubgroup generalizedFitting (bar M Q (H0 M Z))

@[expose] def Stroth12FStarIiiStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Stroth12Hyp hc n → ∀ t ∈ LB M Q B, t ∉ Q →
    ((OmegaMinusNat hc t 3 ∧ FStarU6 M Q Z) ∨ (OmegaPlusNat hc t 3 ∧ FStarL6 M Q Z)) →
    Sec12Iii M Q Z (Lgen M (LB M Q B))

theorem stroth12FStarIii_of_lb (h : Stroth12FStarLBStatement) : Stroth12FStarIiiStatement := by
  intro G _ _ M Q Z B hN hc n h12 t ht htQ hF
  have hleaf := h G M Q Z B hc n h12 t ht htQ hF
  have hFU : FStarU6 M Q Z ∨ FStarL6 M Q Z :=
    hF.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, Nat.card Z = 2 ^ n0 := by
    obtain ⟨n0, -, hn0, -⟩ := hc.hyp.cp
    exact ⟨n0, hn0⟩
  have hsn : IsSimpleGroup ↥(generalizedFitting ↥(bar M Q (H0 M Z))) ∧
      ∃ a b : ↥(generalizedFitting ↥(bar M Q (H0 M Z))), a * b ≠ b * a := by
    rcases hFU with hU | hL
    · unfold FStarU6 at hU
      rw [hn0] at hU
      exact isSimpleGroup_of_isPSUModel hU
    · exact isSimpleGroup_of_isPSLModel hL
  obtain ⟨hs, hna⟩ := hsn
  haveI : IsSimpleGroup ↥(generalizedFitting ↥(bar M Q (H0 M Z))) := hs
  haveI hHn : (bar M Q (H0 M Z)).Normal := hc.normal_bar_H0
  have hXn : (inSubgroup generalizedFitting (bar M Q (H0 M Z))).Normal :=
    normal_inSubgroup_fstar _
  have hlayer : layer (Mbar M Q) = inSubgroup generalizedFitting (bar M Q (H0 M Z)) :=
    layer_eq_inSubgroup_fstar (bar M Q (H0 M Z)) hna (fun P hP => le_bar_H0_of_perfect hc hP)
  let eX : ↥(generalizedFitting ↥(bar M Q (H0 M Z))) ≃*
      ↥(inSubgroup generalizedFitting (bar M Q (H0 M Z))) :=
    (generalizedFitting ↥(bar M Q (H0 M Z))).equivMapOfInjective (bar M Q (H0 M Z)).subtype
      (bar M Q (H0 M Z)).subtype_injective
  haveI : IsSimpleGroup ↥(inSubgroup generalizedFitting (bar M Q (H0 M Z))) :=
    eX.symm.isSimpleGroup
  have hSX : bar M Q (Lgen M (LB M Q B)) =
      inSubgroup generalizedFitting (bar M Q (H0 M Z)) := by
    have hSle : bar M Q (Lgen M (LB M Q B)) ≤
        inSubgroup generalizedFitting (bar M Q (H0 M Z)) := by
      rw [bar_Lgen_eq_normalClosure hc]
      exact Subgroup.normalClosure_le_normal hleaf
    have hSn : (bar M Q (Lgen M (LB M Q B))).Normal := bar_normal (Lgen_normal hc.LB_le_M)
    have hsub : ((bar M Q (Lgen M (LB M Q B))).subgroupOf
        (inSubgroup generalizedFitting (bar M Q (H0 M Z)))).Normal := hSn.subgroupOf _
    haveI := hsub
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((bar M Q (Lgen M (LB M Q B))).subgroupOf
        (inSubgroup generalizedFitting (bar M Q (H0 M Z)))) with hb | ht'
    · exfalso
      have htM : t ∈ M := hc.LB_le_M ht
      have hmem : (QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩) ∈
          bar M Q (Lgen M (LB M Q B)) :=
        ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr (le_Lgen _ ht), rfl⟩
      have hmemX := hSle hmem
      have h1 : (⟨QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩, hmemX⟩ :
          ↥(inSubgroup generalizedFitting (bar M Q (H0 M Z)))) ∈
          (bar M Q (Lgen M (LB M Q B))).subgroupOf
            (inSubgroup generalizedFitting (bar M Q (H0 M Z))) := hmem
      rw [hb, Subgroup.mem_bot] at h1
      have h2 : QuotientGroup.mk' (Q.subgroupOf M) ⟨t, htM⟩ = 1 :=
        congrArg (fun y : ↥(inSubgroup generalizedFitting (bar M Q (H0 M Z))) =>
          (y : Mbar M Q)) h1
      exact htQ (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2))
    · refine le_antisymm hSle fun x hx => ?_
      have : (⟨x, hx⟩ : ↥(inSubgroup generalizedFitting (bar M Q (H0 M Z)))) ∈
          (bar M Q (Lgen M (LB M Q B))).subgroupOf
            (inSubgroup generalizedFitting (bar M Q (H0 M Z))) := by
        rw [ht']
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp this
  have hQS : Q ≤ Lgen M (LB M Q B) := sec39_Q_le_LB.trans (le_Lgen _)
  have hSM : Lgen M (LB M Q B) ≤ M := Lgen_le hc.LB_le_M
  let eS : ↥(generalizedFitting ↥(bar M Q (H0 M Z))) ≃* ↥(bar M Q (Lgen M (LB M Q B))) :=
    eX.trans (MulEquiv.subgroupCongr hSX.symm)
  refine ⟨⟨hN, ?_⟩, ?_⟩
  · show layer (Mbar M Q) = bar M Q (Lgen M (LB M Q B))
    rw [hlayer, hSX]
  · rcases hFU with hU | hL
    · left
      exact quotSat_of_bar (fun X Y _ _ e h => IsPSUModel.congr e h) hQS hSM
        (IsPSUModel.congr eS hU)
    · right
      exact quotSat_of_bar (fun X Y _ _ e h => IsPSLModel.congr e h) hQS hSM
        (IsPSLModel.congr eS hL)

end CFSG.RankThree.GF2n.Stroth80
