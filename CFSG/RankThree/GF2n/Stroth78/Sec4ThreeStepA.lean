module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualProj
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.GroupTheory.ThreeTranspositions.TransvectionSymplectic
import CFSG.Fischer.Classification.SymplecticTypeTransport
import CFSG.RankThree.GF2n.Stroth78.Sec4Two
import CFSG.RankThree.GF2n.Stroth78.Sec3Five

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory.ThreeTranspositions
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G} {S : Setting z E F}

@[expose] noncomputable def rhoW (S : Setting z E F) (a : G) (d : ↥(Xsub S a)) :
    ↥(threeResidualJoin d) →* MulAut ↥(ZQ z) :=
  (rhoZ S).comp ((Xsub S a).subtype.comp (threeResidualJoin d).subtype)

@[expose] noncomputable def CW {S : Setting z E F} {a : G} (d : ↥(Xsub S a)) :
    Subgroup ↥(threeResidualJoin d) :=
  Subgroup.centralizer
    ({(residualSelf d : ↥(threeResidualJoin d))} : Set ↥(threeResidualJoin d))

theorem residualClassW_coe_mem_Eset (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {d : ↥(Xsub S a)} (hα : (d : Hbar z) ∈ Rbar S a)
    (hα1 : (d : Hbar z) ≠ 1) {y : ↥(threeResidualJoin d)}
    (hy : y ∈ residualClassW d) :
    ((y : ↥(Xsub S a)) : Hbar z) ∈ Eset S a := by
  obtain ⟨g, rfl⟩ := hy
  have hαE : (d : Hbar z) ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα hα1)
  have hval : (((g * residualSelf d * g⁻¹ : ↥(threeResidualJoin d)) :
      ↥(Xsub S a)) : Hbar z) =
      (((g : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z) * (d : Hbar z) *
        (((g : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z)⁻¹ := by
    simp [Subgroup.coe_mul]
  rw [hval]
  exact Eset_conj_mem S a hαE _

theorem orderOf_mul_residualClassW_mem (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hα : (d : Hbar z) ∈ Rbar S a) (hα1 : (d : Hbar z) ≠ 1)
    {x y : ↥(threeResidualJoin d)} (hx : x ∈ residualClassW d)
    (hy : y ∈ residualClassW d) :
    orderOf (x * y) ∈ ({1, 2, 3} : Set ℕ) := by
  have hxE := residualClassW_coe_mem_Eset S h hα hα1 hx
  have hyE := residualClassW_coe_mem_Eset S h hα hα1 hy
  have hle : orderOf (x * y) ≤ 3 := by
    have hcoe : (((x * y : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z) =
        (((x : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z) *
          (((y : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z) := by
      simp [Subgroup.coe_mul]
    rw [← Subgroup.orderOf_coe (x * y), ← Subgroup.orderOf_coe
      (((x * y : ↥(threeResidualJoin d)) : ↥(Xsub S a))), hcoe]
    exact h3 _ hxE _ hyE
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

theorem orderOf_residualClassW_eq_two (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hα : (d : Hbar z) ∈ Rbar S a) (hα1 : (d : Hbar z) ≠ 1)
    {x : ↥(threeResidualJoin d)} (hx : x ∈ residualClassW d) :
    orderOf x = 2 := by
  obtain ⟨g, rfl⟩ := hx
  have hP := pair_Xsub S h h217 h3
  have hαE : d ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα hα1)
  have hordD : orderOf d = 2 := CFSG.Fischer.Pair.orderOf_eq_two hP hαE
  have hconj : orderOf (g * residualSelf d * g⁻¹) = orderOf (residualSelf d) := by
    simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq (residualSelf d)
  rw [hconj]
  have hself : orderOf (residualSelf d) = orderOf d := by
    rw [← Subgroup.orderOf_coe (residualSelf d)]
    rfl
  rw [hself, hordD]

theorem exists_transvection_rhoW (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hα : (d : Hbar z) ∈ Rbar S a)
    {x : ↥(threeResidualJoin d)} (hx : x ∈ residualClassW d) :
    ∃ c : ↥(ZQ z), ∀ u : ↥(ZQ z),
      rhoW S a d x u = u ∨ rhoW S a d x u = u * c := by
  obtain ⟨g, rfl⟩ := hx
  have hR : Nat.card ↥(Rbar S a) ≤ 2 := by
    rw [card_Rbar_eq_two S h h217 h3]
  obtain ⟨c, hc⟩ := rhoZ_transvection S h hR hα
    (((g : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z)
  refine ⟨c, fun u => ?_⟩
  have harg : ((Xsub S a).subtype ((threeResidualJoin d).subtype
      (g * residualSelf d * g⁻¹))) =
      (((g : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z) * (d : Hbar z) *
        (((g : ↥(threeResidualJoin d)) : ↥(Xsub S a)) : Hbar z)⁻¹ := by
    simp [Subgroup.coe_mul]
  simp only [rhoW, MonoidHom.comp_apply]
  rw [harg]
  exact hc u

theorem derivedSeries_two_le_ker_rhoW (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {d : ↥(Xsub S a)} (hα : (d : Hbar z) ∈ Rbar S a) (hα1 : (d : Hbar z) ≠ 1)
    (hnot : ¬ CFSG.Fischer.Classification.IsSymplecticType (threeResidualClass d)) :
    derivedSeries ↥(threeResidualJoin d) 2 ≤ (rhoW S a d).ker := by
  have hnotW : ¬ CFSG.Fischer.Classification.IsSymplecticType (residualClassW d) := by
    intro hsym
    apply hnot
    rw [← image_residualProj_residualClassW d]
    exact hsym.image (residualProj d)
  have hK : CFSG.Fischer.Classification.Hyp ↥(threeResidualQuot d)
      (residualProj d '' residualClassW d) := by
    have hαT : (d : Hbar z) ∈ Tset S a := h.mem_Tset_of_mem_Rbar hα hα1
    have hK0 := hyp_stroth78_36 S h h217 h3 hαT
    have hd : d = (⟨(d : Hbar z),
        subset_Xsub S a (Tset_subset_Eset S a hαT)⟩ : ↥(Xsub S a)) :=
      Subtype.ext rfl
    rw [← hd, ← image_residualProj_residualClassW] at hK0
    exact hK0
  exact (isSymplecticType_or_derivedSeries_le_ker (ZQ_mul_self S) (rhoW S a d)
    (residualProj d) (residualProj_surjective d) (residualProj_ker_le_center d)
    (odd_card_ker_residualProj d (odd_card_center_Xsub S a))
    (fun x hx g => residualClassW_conj_mem d hx g)
    (fun x hx => orderOf_residualClassW_eq_two S h h217 h3 hα hα1 hx)
    (fun x hx y hy => orderOf_mul_residualClassW_mem S h h3 hα hα1 hx hy)
    (fun x hx => exists_transvection_rhoW S h h217 h3 hα hx) hK).resolve_left hnotW

@[expose] noncomputable def J0W {S : Setting z E F} {a : G} (d : ↥(Xsub S a)) :
    Subgroup ↥(threeResidualJoin d) :=
  (CFSG.perfectResidual ↥(CW d)).map (CW d).subtype

@[expose] noncomputable def J0 (S : Setting z E F) (a : G) (d : ↥(Xsub S a)) :
    Subgroup (Hbar z) :=
  (J0W d).map ((Xsub S a).subtype.comp (threeResidualJoin d).subtype)

theorem J0W_le_derivedSeries_two {S : Setting z E F} {a : G} (d : ↥(Xsub S a)) :
    J0W d ≤ derivedSeries ↥(threeResidualJoin d) 2 := by
  have h1 : CFSG.perfectResidual ↥(CW d) ≤ derivedSeries ↥(CW d) 2 := iInf_le _ 2
  have h2 : (CFSG.perfectResidual ↥(CW d)).map (CW d).subtype ≤
      (derivedSeries ↥(CW d) 2).map (CW d).subtype :=
    Subgroup.map_mono (f := (CW d).subtype) h1
  have h3 : (derivedSeries ↥(CW d) 2).map (CW d).subtype ≤
      derivedSeries ↥(threeResidualJoin d) 2 :=
    map_derivedSeries_le_derivedSeries (f := (CW d).subtype) 2
  exact h2.trans h3

theorem commutator_J0W {S : Setting z E F} {a : G} (d : ↥(Xsub S a)) :
    ⁅J0W d, J0W d⁆ = J0W d := by
  have hperf : Group.IsPerfect ↥(J0W d) := by
    change Group.IsPerfect ↥((CFSG.perfectResidual ↥(CW d)).map (CW d).subtype)
    have h0 : Group.IsPerfect (CFSG.perfectResidual ↥(CW d)) :=
      (CFSG.perfect_residual_characterization (G := ↥(CW d))).2.2.1
    exact Group.IsPerfect.map (CW d).subtype
      (H := CFSG.perfectResidual ↥(CW d))
  have hcomm : commutator ↥(J0W d) = ⊤ := Group.isPerfect_def.mp hperf
  rw [← Subgroup.map_subtype_commutator (J0W d), hcomm, Subgroup.map_top,
    Subgroup.range_subtype]

theorem commutator_J0 (S : Setting z E F) (a : G) (d : ↥(Xsub S a)) :
    ⁅J0 S a d, J0 S a d⁆ = J0 S a d := by
  rw [J0, ← Subgroup.map_commutator
    (f := (Xsub S a).subtype.comp (threeResidualJoin d).subtype), commutator_J0W]

theorem commute_of_mem_J0 (S : Setting z E F) (a : G) (d : ↥(Xsub S a))
    {y : Hbar z} (hy : y ∈ J0 S a d) : y * (d : Hbar z) = (d : Hbar z) * y := by
  rw [J0] at hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  rw [J0W] at hx
  obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.1 hx
  have hcomm : (c : ↥(threeResidualJoin d)) * residualSelf d =
      residualSelf d * (c : ↥(threeResidualJoin d)) :=
    Subgroup.mem_centralizer_singleton_iff.mp c.2
  have h := congrArg ((Xsub S a).subtype.comp (threeResidualJoin d).subtype) hcomm
  simpa [residualSelf] using h

theorem J0_le_CH_of_ker (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (d : ↥(Xsub S a)) (hα : (d : Hbar z) ∈ Rbar S a) (hα1 : (d : Hbar z) ≠ 1)
    (hker : derivedSeries ↥(threeResidualJoin d) 2 ≤ (rhoW S a d).ker) :
    J0 S a d ≤ CH a := by
  have hA := mem_A2set_and_aVec_mem_of_mem_Rbar h hα hα1
  refine le_CH_of_perfect (S := S) h (commutator_J0 S a d) hA.1 hA.2
    (fun y hy => commute_of_mem_J0 S a d hy) ?_
  intro x hxP v hv
  let v' : ↥(ZQ z) := ⟨v, hv⟩
  have hxJ : QuotientGroup.mk x ∈ J0 S a d := hxP
  rw [J0] at hxJ
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxJ
  have hrho : rhoW S a d y = 1 :=
    MonoidHom.mem_ker.mp (hker (J0W_le_derivedSeries_two d hy))
  have hrho' : rhoZ S (QuotientGroup.mk x) = 1 := by
    rw [← hyx]
    simpa [rhoW] using hrho
  have hval : (rhoZ S (QuotientGroup.mk x) v' : ↥(ZQ z)) = v' := by
    simpa using congrArg (fun e : MulAut ↥(ZQ z) => e v') hrho'
  calc
    (x : G) * v * (x : G)⁻¹ = ((rhoZ S (QuotientGroup.mk x) v' : ↥(ZQ z)) : G) :=
      (rhoZ_mk S x v').symm
    _ = v := by rw [hval]

theorem J0_le_normalizer_Lbar_of_ker (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) (d : ↥(Xsub S a)) (hα : (d : Hbar z) ∈ Rbar S a)
    (hα1 : (d : Hbar z) ≠ 1)
    (hker : derivedSeries ↥(threeResidualJoin d) 2 ≤ (rhoW S a d).ker) :
    J0 S a d ≤ Subgroup.normalizer (Lbar S a : Set (Hbar z)) :=
  (J0_le_CH_of_ker S h d hα hα1 hker).trans (CH_le_normalizer_Lbar S a)

end CFSG.RankThree.GF2n.Stroth78
