module

public import CFSG.RankThree.PartOne.TCX.Ree.Closure
import CFSG.RankThree.PartOne.KLR.FrameTorus
import CFSG.RankThree.PartOne.KE.A1Weyl
import CFSG.LieType.AlgebraicGroups.ConnectedToralLangFrobenius
import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover
import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.CTMain
public import CFSG.RankThree.PartOne.KLR.CoreGroup
public import CFSG.RankThree.PartOne.KLR.FrobTrick
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.RankThree.PartOne.KE.A1SL2
import CFSG.RankThree.PartOne.KE.A1Torus
import CFSG.RankThree.PartOne.KE.A2Family
import CFSG.RankThree.PartOne.KE.A2Shape
import CFSG.RankThree.PartOne.KE.SigmaUntwisted
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.TCX.Ree

theorem kgLangRee_torus_lang {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (C : ReeClosure L) (b : ℕ) (n : adjointGroup ReeTag.F4.tag L)
    (hn : (n : ModGL ReeTag.F4.tag L) ∈
      Subgroup.normalizer (torusGroup ReeTag.F4.tag L : Set (ModGL ReeTag.F4.tag L))) :
    ∀ c : adjointGroup ReeTag.F4.tag L, (c : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L →
      ∃ z : adjointGroup ReeTag.F4.tag L, (z : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L ∧
        c = z⁻¹ * (n * (C.Φ * C.Fr ^ b) z * n⁻¹) := by
  classical
  intro c hc
  set S : MulAut (adjointGroup ReeTag.F4.tag L) := C.Φ * C.Fr ^ b with hS
  set F : MulAut (adjointGroup ReeTag.F4.tag L) := MulAut.conj n * S with hF
  set Q : ModGL ReeTag.F4.tag L := (n : ModGL ReeTag.F4.tag L) * (S n : ModGL ReeTag.F4.tag L) with hQ
  set Hadj : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    (torusGroup ReeTag.F4.tag L).subgroupOf (adjointGroup ReeTag.F4.tag L) with hHadj
  have hFrtw : ∀ y : adjointGroup ReeTag.F4.tag L,
      C.Fr y = frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L 2 1) y := fun y =>
    Subtype.ext (C.fr_apply y)
  have hRee : CFSG.RankThree.PartOne.KLR.IsReeFrob b S := by
    rw [hS]; exact CFSG.RankThree.PartOne.KLR.isReeFrob_of_exceptional C.isExc hFrtw b
  have hSsq : S * S = C.Fr ^ (2 * b + 1) := by
    have hpow : C.Φ * C.Fr ^ b = C.Φ ^ (2 * b + 1) := by
      rw [← C.sq, ← _root_.sq, ← pow_mul, ← pow_succ']
    rw [hS, hpow, ← pow_add, show 2 * b + 1 + (2 * b + 1) = 2 * (2 * b + 1) by ring, pow_mul,
      _root_.sq, C.sq]
  have hS0_le : Hadj.map S.toMonoidHom ≤ Hadj := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hadj, hmap⟩ := hRee.map_torusGroup (Subgroup.mem_subgroupOf.mp hx)
    have hx_eq : (⟨(x : ModGL ReeTag.F4.tag L), hadj⟩ : adjointGroup ReeTag.F4.tag L) = x :=
      Subtype.ext rfl
    rw [hx_eq] at hmap
    exact Subgroup.mem_subgroupOf.mpr hmap
  have hn_conj_le : Hadj.map (MulAut.conj n).toMonoidHom ≤ Hadj := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (x : ModGL ReeTag.F4.tag L)).1
      (Subgroup.mem_subgroupOf.mp hx)
    show (((MulAut.conj n) x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
      torusGroup ReeTag.F4.tag L
    rw [MulAut.conj_apply]
    simpa using h1
  have hF_le : Hadj.map F.toMonoidHom ≤ Hadj := by
    rw [hF]
    have hcomp : (MulAut.conj n * S).toMonoidHom =
        (MulAut.conj n).toMonoidHom.comp S.toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map]
    exact (Subgroup.map_mono hS0_le).trans hn_conj_le
  have hF2_le : Hadj.map (F * F).toMonoidHom ≤ Hadj := by
    have hcomp : (F * F).toMonoidHom = F.toMonoidHom.comp F.toMonoidHom := rfl
    rw [hcomp, ← Subgroup.map_map]
    exact (Subgroup.map_mono hF_le).trans hF_le
  have hSconj : S * MulAut.conj n = MulAut.conj (S n) * S := by
    refine MulEquiv.ext fun z => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv]
  have hFF : F * F = MulAut.conj (n * S n) * (S * S) := by
    rw [hF]
    calc (MulAut.conj n * S) * (MulAut.conj n * S)
        = MulAut.conj n * (S * MulAut.conj n) * S := by group
      _ = MulAut.conj n * (MulAut.conj (S n) * S) * S := by rw [hSconj]
      _ = (MulAut.conj n * MulAut.conj (S n)) * (S * S) := by group
      _ = MulAut.conj (n * S n) * (S * S) := by rw [← map_mul]
  have hF2coe : ∀ z : adjointGroup ReeTag.F4.tag L,
      (((F * F) z : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        CFSG.LieType.AlgebraicGroups.frobTwistGL ReeTag.F4.tag L 2 (2 * b + 1) Q (z : ModGL ReeTag.F4.tag L) := by
    intro z
    rw [hFF, hSsq, MulAut.mul_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [CFSG.LieType.AlgebraicGroups.frobTwistGL_apply, hQ,
      coe_pow_apply_of_entrywise_frobenius 2 C.Fr C.fr_apply (2 * b + 1) z]
  have hstab : ∀ g ∈ torusGroup ReeTag.F4.tag L,
      CFSG.LieType.AlgebraicGroups.frobTwistGL ReeTag.F4.tag L 2 (2 * b + 1) Q g ∈ torusGroup ReeTag.F4.tag L := by
    intro g hg
    set g' : adjointGroup ReeTag.F4.tag L := ⟨g, CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup hg⟩ with hg'
    have hcoe : ((F * F) g' : ModGL ReeTag.F4.tag L) =
        CFSG.LieType.AlgebraicGroups.frobTwistGL ReeTag.F4.tag L 2 (2 * b + 1) Q g :=
      hF2coe g'
    have hg'mem : g' ∈ Hadj := Subgroup.mem_subgroupOf.mpr hg
    have hmem : (F * F) g' ∈ Hadj :=
      hF2_le (Subgroup.mem_map_of_mem (F * F).toMonoidHom hg'mem)
    rw [← hcoe]
    exact Subgroup.mem_subgroupOf.mp hmem
  have hker : CFSG.LieType.Chevalley.kernelRoots
      (MonoidHom.id (Multiplicative (Fin ReeTag.F4.tag.rank → ℤ))) = ∅ := by
    ext α
    simp only [CFSG.LieType.Chevalley.kernelRoots, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_and, MonoidHom.id_apply]
    exact fun hα => hα.ne_zero
  letI : Group (WithConv (CFSG.LieType.AlgebraicGroups.GLCoord L (Label ReeTag.F4.tag) →ₐ[L] L)) :=
    AlgHom.convGroup
  have hconn : CFSG.LieType.AlgebraicGroups.IsConnectedAlgebraicSubgroup L
      (Subgroup.map (CFSG.LieType.AlgebraicGroups.modGLPoint ReeTag.F4.tag L).toMonoidHom
        (torusGroup ReeTag.F4.tag L)) := by
    have h :=
      CFSG.HardMathSupport.Timmesfeld.Torality.isConnectedAlgebraicSubgroup_torus_sup_rootSpan_kernelRoots
        (τ := ReeTag.F4.tag) (k := L) (MonoidHom.id (Multiplicative (Fin ReeTag.F4.tag.rank → ℤ)))
    simpa [hker, rootSpan] using h
  obtain ⟨-, -, -, hlang⟩ := CFSG.LieType.AlgebraicGroups.exists_frobTwist_restriction 2 hconn (by omega) Q hstab
  obtain ⟨z, hzH, hz⟩ := hlang (c : ModGL ReeTag.F4.tag L) hc
  set z_adj : adjointGroup ReeTag.F4.tag L := ⟨z, CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup hzH⟩ with hz_adj
  have hz_adj_mem : z_adj ∈ Hadj := Subgroup.mem_subgroupOf.mpr hzH
  have hF_mem : F z_adj ∈ Hadj := hF_le (Subgroup.mem_map_of_mem F.toMonoidHom hz_adj_mem)
  have hzF2 : z_adj⁻¹ * (F * F) z_adj = c := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hF2coe]
    exact hz
  have hcomm : z_adj * F z_adj = F z_adj * z_adj := by
    apply Subtype.ext
    exact CFSG.RankThree.PartOne.KE.torusGroup_comm
      (Subgroup.mem_subgroupOf.mp hz_adj_mem) (Subgroup.mem_subgroupOf.mp hF_mem)
  refine ⟨z_adj * F z_adj, Hadj.mul_mem hz_adj_mem hF_mem, ?_⟩
  change c = (z_adj * F z_adj)⁻¹ * F (z_adj * F z_adj)
  have hcomm' : (F z_adj)⁻¹ * z_adj⁻¹ = z_adj⁻¹ * (F z_adj)⁻¹ := by
    rw [← mul_inv_rev, hcomm, mul_inv_rev]
  rw [map_mul, ← MulAut.mul_apply, mul_inv_rev, hcomm']
  group
  exact hzF2.symm

end CFSG.StandardType
