module

public import CFSG.LocalAnalysis.StandardType.FF81.FrameModel
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CommutatorCentralDecomposition
import CFSG.Mathlib.GroupTheory.ConjCentralizer
import CFSG.Mathlib.GroupTheory.SimpleConj
import CFSG.RankThree.PartOne.TAIL.LSideOutAut
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFLin
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
import CFSG.RankThree.LocalRank.SelectorCases
import CFSG.RankThree.PartOne.Assembly
import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.TAIL.KSideCen
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherDefs
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType.FF81

open CFSG.ClassicalInvolution.WeakCT
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] {n : ℕ} {b : G} {L : Subgroup G}

private noncomputable def frameJEquiv [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2)) :
    SL(n - 1, ZMod 2) ≃* ↥(frameJ φ) :=
  (MonoidHom.ofInjective (jBlock_injective n)).trans
    ((Subgroup.equivMapOfInjective (jBlock n).range φ.symm.toMonoidHom
        φ.symm.injective).trans
      (Subgroup.equivMapOfInjective ((jBlock n).range.map φ.symm.toMonoidHom) L.subtype
        L.subtype_injective))

private theorem frameJEquiv_coe_apply [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2))
    (B : SL(n - 1, ZMod 2)) :
    ((frameJEquiv φ B : ↥(frameJ φ)) : G) = (φ.symm (jBlock n B) : G) :=
  rfl

private theorem isSimpleGroup_frameJ [NeZero n] (hn : 5 ≤ n)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) : IsSimpleGroup ↥(frameJ φ) :=
  @MulEquiv.isSimpleGroup ↥(frameJ φ) _ (SL(n - 1, ZMod 2)) _
    (CFSG.RankThree.PartTwo.Sec4.RonanK429F.isSimpleGroup_SL_zmod_two (by omega))
    (frameJEquiv φ).symm

private theorem isSimpleGroup_map_conj_frameJ [NeZero n] (hn : 5 ≤ n)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) {τ : G} :
    IsSimpleGroup ↥((frameJ φ).map (MulAut.conj τ).toMonoidHom) := by
  have hsimple : IsSimpleGroup ↥(frameJ φ) := isSimpleGroup_frameJ hn φ
  exact @MulEquiv.isSimpleGroup ↥((frameJ φ).map (MulAut.conj τ).toMonoidHom) _
    ↥(frameJ φ) _ hsimple
    (Subgroup.equivMapOfInjective (frameJ φ) (MulAut.conj τ).toMonoidHom
      (MulAut.conj τ).injective).symm

private theorem isPerfect_map_conj_frameJ [NeZero n] (hn : 5 ≤ n)
    (φ : ↥L ≃* SL(n + 1, ZMod 2)) {τ : G} :
    Group.IsPerfect ↥((frameJ φ).map (MulAut.conj τ).toMonoidHom) := by
  let e : SL(n - 1, ZMod 2) ≃* ↥((frameJ φ).map (MulAut.conj τ).toMonoidHom) :=
    (frameJEquiv φ).trans
      (Subgroup.equivMapOfInjective (frameJ φ) (MulAut.conj τ).toMonoidHom
        (MulAut.conj τ).injective)
  let : Group.IsPerfect (SL(n - 1, ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem map_conj_frameJ_le_L [Finite G] (hA : HypA G n b L) [NeZero n]
    {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    (hφ0 : φ (z 0) = tOne n) (hφ1 : φ (z 1) ∈ (jBlock n).range) {τ : G}
    (hτz : τ * (z 0 : G) * τ⁻¹ = b) (hτ1 : τ * (z 1 : G) * τ⁻¹ = z 1) :
    (frameJ φ).map (MulAut.conj τ).toMonoidHom ≤ L := by
  have hn5 : 5 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  let J' : Subgroup G := (frameJ φ).map (MulAut.conj τ).toMonoidHom
  have hJb : frameJ φ ≤ Subgroup.centralizer ({b} : Set G) :=
    (pullSL_le φ (jBlock n).range).trans hA.le
  have hJz : frameJ φ ≤ Subgroup.centralizer ({(z 0 : G)} : Set G) := by
    intro j hj
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_frameJ hφ0 hj).symm
  have hJ'b : J' ≤ Subgroup.centralizer ({b} : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj τ).toMonoidHom) hJz
    rw [Subgroup.map_conj_centralizer_singleton, hτz] at h
    exact h
  have hJ'N : J' ≤ Subgroup.normalizer (L : Set G) := hJ'b.trans hA.nor
  have hz1mem : (z 1 : G) ∈ frameJ φ := by
    show (z 1 : G) ∈ pullSL φ (jBlock n).range
    rw [mem_pullSL_iff]
    exact hφ1
  have hz1J' : (z 1 : G) ∈ J' := Subgroup.mem_map.mpr ⟨_, hz1mem, hτ1⟩
  have hz1ne : (z 1 : G) ≠ 1 := fun h =>
    hz.z_ne_one 1 (Subtype.ext (by simpa using h))
  exact CFSG.le_of_forall_conj_mem_of_isSimpleGroup
    (isSimpleGroup_map_conj_frameJ hn5 φ)
    (fun j hj k hk => (Subgroup.mem_normalizer_iff.mp (hJ'N hj) k).mp hk)
    hz1J' (z 1).2 hz1ne

private theorem map_conj_frameJ_le_frameJ [NeZero n] {z : Fin 3 → ↥L}
    {φ : ↥L ≃* SL(n + 1, ZMod 2)} (hφ0 : φ (z 0) = tOne n) {τ : G}
    (hL : (frameJ φ).map (MulAut.conj τ).toMonoidHom ≤ L)
    (hC : (frameJ φ).map (MulAut.conj τ).toMonoidHom ≤
      Subgroup.centralizer ({(z 0 : G)} : Set G))
    (hperf : Group.IsPerfect ↥((frameJ φ).map (MulAut.conj τ).toMonoidHom)) :
    (frameJ φ).map (MulAut.conj τ).toMonoidHom ≤ frameJ φ := by
  let J' : Subgroup G := (frameJ φ).map (MulAut.conj τ).toMonoidHom
  have hcommle : ⁅J', J'⁆ ≤ frameJ φ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxL : x ∈ L := hL hx
    have hyL : y ∈ L := hL hy
    have hxz : (⟨x, hxL⟩ : ↥L) * (z 0) = (z 0) * ⟨x, hxL⟩ :=
      Subtype.ext (by simpa using Subgroup.mem_centralizer_singleton_iff.mp (hC hx))
    have hyz : (⟨y, hyL⟩ : ↥L) * (z 0) = (z 0) * ⟨y, hyL⟩ :=
      Subtype.ext (by simpa using Subgroup.mem_centralizer_singleton_iff.mp (hC hy))
    obtain ⟨a, jx, hjx, hxeq⟩ :=
      (mem_centralizer_iff_of_eq_tOne hφ0 ⟨x, hxL⟩).mp hxz
    obtain ⟨b, jy, hjy, hyeq⟩ :=
      (mem_centralizer_iff_of_eq_tOne hφ0 ⟨y, hyL⟩).mp hyz
    have hxeq' : x = (z 0 : G) ^ a * jx := hxeq
    have hyeq' : y = (z 0 : G) ^ b * jy := hyeq
    have hcx : Commute (z 0 : G) jx := commute_of_mem_frameJ hφ0 hjx
    have hcy : Commute (z 0 : G) jy := commute_of_mem_frameJ hφ0 hjy
    have hz₁y : Commute ((z 0 : G) ^ a) y := by
      rw [hyeq']
      exact (((Commute.refl (z 0 : G)).pow_left a).pow_right b).mul_right (hcy.pow_left a)
    have hz₂x : Commute ((z 0 : G) ^ b) x := by
      rw [hxeq']
      exact (((Commute.refl (z 0 : G)).pow_left b).pow_right a).mul_right (hcx.pow_left b)
    have hcomm : ⁅x, y⁆ = ⁅jx, jy⁆ :=
      CFSG.GorensteinWalter.commutator_eq_of_central_decomposition hxeq' hyeq'
        (hcx.pow_left a).eq (hcy.pow_left a).eq (hcx.pow_left b).eq (hcy.pow_left b).eq
        hz₁y.eq hz₂x.eq
    rw [hcomm]
    exact (Subgroup.commutator_le_self (frameJ φ))
      (Subgroup.commutator_mem_commutator hjx hjy)
  have hself : ⁅J', J'⁆ = J' := @Subgroup.commutator_eq_self G _ J' hperf
  calc J' = ⁅J', J'⁆ := hself.symm
    _ ≤ frameJ φ := hcommle

theorem map_conj_frameJ [Finite G] (hA : HypA G n b L) [NeZero n] {z : Fin 3 → ↥L}
    (hz : GGFF.Model ↥L z) {φ : ↥L ≃* SL(n + 1, ZMod 2)} (hφ0 : φ (z 0) = tOne n)
    (hφ1 : φ (z 1) ∈ (jBlock n).range) {τ : G} (hτb : τ * b * τ⁻¹ = z 0)
    (hτz : τ * (z 0 : G) * τ⁻¹ = b) (hτ1 : τ * (z 1 : G) * τ⁻¹ = z 1) :
    (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ := by
  have hn5 : 5 ≤ n := by rcases hA.n_cases with rfl | rfl <;> norm_num
  let J' : Subgroup G := (frameJ φ).map (MulAut.conj τ).toMonoidHom
  have hJb : frameJ φ ≤ Subgroup.centralizer ({b} : Set G) :=
    (pullSL_le φ (jBlock n).range).trans hA.le
  have hJ'z : J' ≤ Subgroup.centralizer ({(z 0 : G)} : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj τ).toMonoidHom) hJb
    rw [Subgroup.map_conj_centralizer_singleton, hτb] at h
    exact h
  have hJ'leL : J' ≤ L := map_conj_frameJ_le_L hA hz hφ0 hφ1 hτz hτ1
  have hJ'leJ : J' ≤ frameJ φ :=
    map_conj_frameJ_le_frameJ (z := z) hφ0 hJ'leL hJ'z (isPerfect_map_conj_frameJ hn5 φ)
  have hcard : Nat.card ↥J' = Nat.card ↥(frameJ φ) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj τ).toMonoidHom)
      (MulAut.conj τ).injective
  exact Subgroup.eq_of_le_of_card_ge hJ'leJ hcard.symm.le

private noncomputable def frameJEmbedding [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2)) :
    SL(n - 1, ZMod 2) →* G :=
  (frameJ φ).subtype.comp (frameJEquiv φ).toMonoidHom

private theorem blockSL2_eq_comp [NeZero n] {i : Fin n} (hi : 2 ≤ (i : ℕ)) :
    blockSL2 (ZMod 2) n i =
      (jBlock n).comp (blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)) := by
  apply MonoidHom.ext
  intro A
  rw [MonoidHom.comp_apply]
  have hfin : (⟨(i : ℕ) - 2 + 2, by omega⟩ : Fin n) = i := by
    apply Fin.ext
    simp
    omega
  have h := jBlock_blockSL n ((i : ℕ) - 2) (by omega) A
  exact (congrArg (fun j : Fin n => blockSL2 (ZMod 2) n j A) hfin).symm.trans h.symm

private theorem pullSL_blockSL2_range [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2))
    (i : Fin n) (hi : 2 ≤ (i : ℕ)) :
    pullSL φ (blockSL2 (ZMod 2) n i).range =
      ((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (frameJEmbedding φ)) := by
  apply le_antisymm
  · intro y hy
    have hyL : y ∈ L := pullSL_le φ _ hy
    have hyφ : φ (⟨y, hyL⟩ : ↥L) ∈ (blockSL2 (ZMod 2) n i).range := by
      rw [← mem_pullSL_iff]
      exact hy
    rw [blockSL2_eq_comp hi, MonoidHom.range_comp] at hyφ
    obtain ⟨A, hA, hAx⟩ := Subgroup.mem_map.mp hyφ
    refine Subgroup.mem_map.mpr ⟨A, hA, ?_⟩
    change (((frameJEquiv φ) A : ↥(frameJ φ)) : G) = y
    rw [frameJEquiv_coe_apply, hAx]
    simp
  · intro y hy
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hy
    change (((frameJEquiv φ) A : ↥(frameJ φ)) : G) ∈
      pullSL φ (blockSL2 (ZMod 2) n i).range
    rw [frameJEquiv_coe_apply, mem_pullSL_iff, MulEquiv.apply_symm_apply,
      blockSL2_eq_comp hi, MonoidHom.range_comp]
    exact Subgroup.mem_map_of_mem (jBlock n) hA

private theorem map_range_blockSL_eq [NeZero n] {i : Fin n} (hi : 2 ≤ (i : ℕ))
    {g : SL(n - 1, ZMod 2)} {ε : ℕ} (hε : ε ≤ 1) {α : MulAut (SL(n - 1, ZMod 2))}
    (hα : α = MulAut.conj g * slGraphAut (n - 1) (ZMod 2) ^ ε) :
    ((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map α.toMonoidHom) =
      ((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (MulAut.conj g).toMonoidHom) := by
  have hδ : ((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
      (slGraphAut (n - 1) (ZMod 2) ^ ε).toMonoidHom) =
      (blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range := by
    interval_cases ε
    · rw [pow_zero, MulAut.one_def]
      exact Subgroup.map_id _
    · simpa using map_slGraphAut_range_blockSL (n - 1) ((i : ℕ) - 2) (by omega)
  rw [hα]
  have hcomp : (MulAut.conj g * slGraphAut (n - 1) (ZMod 2) ^ ε).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp
        (slGraphAut (n - 1) (ZMod 2) ^ ε).toMonoidHom := by
    apply MonoidHom.ext
    intro B
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rfl
  rw [hcomp, ← Subgroup.map_map, hδ]

private theorem map_conj_frameJEmbedding_mul [NeZero n] (φ : ↥L ≃* SL(n + 1, ZMod 2))
    (i : Fin n) (hi : 2 ≤ (i : ℕ)) (g : SL(n - 1, ZMod 2)) :
    (((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (frameJEmbedding φ)).map
      (MulAut.conj (frameJEmbedding φ g)).toMonoidHom) =
      (((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (MulAut.conj g).toMonoidHom).map (frameJEmbedding φ)) := by
  have hcomp : (MulAut.conj (frameJEmbedding φ g)).toMonoidHom.comp (frameJEmbedding φ) =
      (frameJEmbedding φ).comp (MulAut.conj g).toMonoidHom := by
    apply MonoidHom.ext
    intro B
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [map_mul, map_inv]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem exists_mem_frameJ_map_conj_eq [NeZero n] (hn : 4 ≤ n) {φ : ↥L ≃* SL(n + 1, ZMod 2)}
    {τ : G} (hτJ : (frameJ φ).map (MulAut.conj τ).toMonoidHom = frameJ φ) :
    ∃ j ∈ frameJ φ, ∀ i : Fin n, 2 ≤ (i : ℕ) →
      (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj τ).toMonoidHom =
        (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj j).toMonoidHom := by
  let θ := frameJEquiv φ
  have hτN : τ ∈ Subgroup.normalizer (frameJ φ : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hτJ
  let β : MulAut ↥(frameJ φ) := (frameJ φ).normalizerMonoidHom ⟨τ, hτN⟩
  let α : MulAut (SL(n - 1, ZMod 2)) := (MulAut.congr θ).symm β
  have hαβ : ∀ B : SL(n - 1, ZMod 2), θ (α B) = β (θ B) := by
    intro B
    have h : (MulAut.congr θ) α = β := (MulAut.congr θ).apply_symm_apply β
    have := congrArg (fun e : MulAut ↥(frameJ φ) => e (θ B)) h
    rw [MulAut.congr_apply] at this
    simpa using this
  have hβcoe : ∀ x : ↥(frameJ φ), (β x : G) = τ * (x : G) * τ⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (frameJ φ) ⟨τ, hτN⟩ x
  obtain ⟨g, ε, hε, hα⟩ :=
    CFSG.RankThree.PartOne.TAIL.aut_sl_zmod_two (by omega : 3 ≤ n - 1) α
  let j : G := frameJEmbedding φ g
  refine ⟨j, (θ g).2, fun i hi => ?_⟩
  have hτ : (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj τ).toMonoidHom =
      (((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (MulAut.conj g).toMonoidHom).map (frameJEmbedding φ)) := by
    rw [pullSL_blockSL2_range φ i hi, Subgroup.map_map]
    have hcomp : (MulAut.conj τ).toMonoidHom.comp (frameJEmbedding φ) =
        (frameJEmbedding φ).comp α.toMonoidHom := by
      apply MonoidHom.ext
      intro B
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      change τ * ((θ B : ↥(frameJ φ)) : G) * τ⁻¹ =
        ((θ (α B) : ↥(frameJ φ)) : G)
      rw [hαβ B, hβcoe]
    rw [hcomp, ← Subgroup.map_map]
    congr 1
    exact map_range_blockSL_eq hi hε hα
  have hj : (pullSL φ (blockSL2 (ZMod 2) n i).range).map (MulAut.conj j).toMonoidHom =
      (((blockSL (ZMod 2) (n - 1) 2 ((i : ℕ) - 2) (by omega)).range.map
        (MulAut.conj g).toMonoidHom).map (frameJEmbedding φ)) := by
    rw [pullSL_blockSL2_range φ i hi]
    exact map_conj_frameJEmbedding_mul φ i hi g
  rw [hτ, hj]

end CFSG.StandardType.FF81
