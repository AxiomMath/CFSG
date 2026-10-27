module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Certificates.Kernel.TwoAC.Fact
import Certificates.Kernel.TwoAC.Comm
import Certificates.Kernel.BabyMonster.Seeds
import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicBReduce
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.SymplecticPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Q3.ModelCenter
import CFSG.ClassicalInvolution.RouteD.LocalLift
import CFSG.Goldschmidt.StatementsG4
import CFSG.GroupTheory.ThompsonIndexTwo
import CFSG.LieType.Chevalley.EvenRootCommutatorF4
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma26
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma39Bar
import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionFitting
import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentInvolutionMoved
import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupLemma37Statement
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaGlobalLSide
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSylowReduction
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.FittingNilpotence
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian_models
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.Walter.J1Recog
import CFSG.Walter.Ree.Thompson2.BaseFin
import CFSG.Walter.ReeOrder.WardLocal
import CFSG.Walter.W67.Section8.Prop83
import Certificates.Certificate7000
import Certificates.Certificate7001
import Certificates.Certificate7002
import Certificates.Certificate7003
import Certificates.Certificate7004
import Certificates.Certificate7005
import Certificates.Certificate7006
import Certificates.Certificate7007
import Certificates.Certificate7008
import Certificates.Certificate7009
import Certificates.Certificate7010
import Certificates.Certificate7011

public section

namespace CertificateChecks.KernelTwoAC

open CFSG.Blueprint CFSG.KC.BM.TwoAC Subgroup

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

theorem rank_add_le' (M N : MatB) : (M + N).rank ≤ M.rank + N.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem add_self_mat (M : MatB) : M + M = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) M, h2, zero_smul]

theorem mul_ne_one_of_rank {M N : MatB} (h : (M * N).rank < 4370) : M * N ≠ 1 := by
  intro e
  rw [e, Matrix.rank_one, Fintype.card_fin] at h
  exact lt_irrefl _ h

theorem sq_add_of_sq_zero (N L : MatB) (h : N * N = 0) :
    (N + L) * (N + L) = N * L + L * N + L * L := by
  rw [add_mul, mul_add, mul_add, h]
  abel

theorem one_add_sq (X : MatB) (h : X * X = 1) : (1 + X) * (1 + X) = 0 := by
  simp only [add_mul, mul_add, one_mul, mul_one, h]
  rw [add_comm X 1, add_self_mat]

theorem exists_unit {S : Submonoid MatB} {X Y : MatB} (hX : X ∈ S) (hY : Y ∈ S) (h1 : X * Y = 1)
    (h2 : Y * X = 1) : ∃ u : Sˣ, u.val.val = X :=
  ⟨⟨⟨X, hX⟩, ⟨Y, hY⟩, Subtype.ext h1, Subtype.ext h2⟩, rfl⟩

@[expose] def matOf (S : Submonoid MatB) : Sˣ →* MatB := S.subtype.comp (Units.coeHom S)

theorem matOf_apply (S : Submonoid MatB) (u : Sˣ) : matOf S u = u.val.val := rfl

theorem matOf_inj (S : Submonoid MatB) {u v : Sˣ} (h : matOf S u = matOf S v) : u = v :=
  Units.ext (Subtype.ext h)

theorem classData_of_fact {S : Submonoid MatB} {A B : MatB} (hA : A ∈ S) (hB : B ∈ S)
    (hf : TwoACFact A B) : ∃ x : Sˣ, x ^ 2 = 1 ∧ x ≠ 1 ∧ (x.val.val + 1).rank ≤ 1860 ∧
      ∃ P : Subgroup Sˣ, ⁅P, P⁆ = P ∧ P ≤ centralizer {x} ∧
        ∀ y ∈ centralizer (P : Set Sˣ), y * x = x * y → y ^ 2 = 1 → y ≠ 1 → y ≠ x →
          (y.val.val + 1).rank ≤ 1859 ∨ ((x * y).val.val + 1).rank ≤ 1859 := by
  obtain ⟨hx2, hxr, ha2, hb17, hab, hax, hbx, T₁, T₂, hT₁, hT₂, hcomm⟩ := hf
  have hw : wW A B ∈ S := by
    unfold wW
    with_reducible repeat' first | exact hA | exact hB | apply S.pow_mem | apply S.mul_mem
  have hXS : xW A B ∈ S := S.pow_mem hw _
  have hbS : bW A B ∈ S := S.pow_mem hw _
  have haS : aW A B ∈ S := by
    unfold aW hW gW
    with_reducible repeat' first | exact hA | exact hB | exact hXS | apply S.pow_mem |
      apply S.mul_mem
  have hX1 : xW A B * xW A B = 1 := by rw [← sq, hx2]
  have ha1 : aW A B * aW A B = 1 := by rw [← sq, ha2]
  obtain ⟨x, hx⟩ := exists_unit hXS hXS hX1 hX1
  obtain ⟨a, ha⟩ := exists_unit haS haS ha1 ha1
  obtain ⟨b, hb⟩ := exists_unit hbS (S.pow_mem hbS 16) (by rw [← pow_succ']; exact hb17)
    (by rw [← pow_succ]; exact hb17)
  have hXY : xW A B - 1 = xW A B + 1 := by
    rw [sub_eq_iff_eq_add, add_assoc, add_self_mat, add_zero]
  have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
  refine ⟨x, matOf_inj S (by rw [map_pow, map_one, matOf_apply, hx, hx2]), ?_, ?_,
    closure {a, b}, ?_, ?_, ?_⟩
  · intro h
    have e : xW A B = 1 := by rw [← hx, h]; rfl
    rw [e, sub_self, Matrix.rank_zero] at hxr
    exact absurd hxr (by norm_num)
  · exact le_of_eq (by rw [hx, ← hXY, hxr])
  · refine CFSG.ComponentClassification.RankTwoSporadic.commutator_closure_pair
      (p := 2) (q := 17) (r := 13) (matOf_inj S ?_) (matOf_inj S ?_) (matOf_inj S ?_)
      (by norm_num) (by norm_num) (by norm_num)
    · rw [map_pow, map_one, matOf_apply, ha, ha2]
    · rw [map_pow, map_one, matOf_apply, hb, hb17]
    · rw [map_pow, map_mul, map_one, matOf_apply, matOf_apply, ha, hb, hab]
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    refine matOf_inj S ?_
    rw [map_mul, map_mul, matOf_apply, matOf_apply, hx]
    rcases hg with rfl | rfl
    · rw [ha, hax]
    · rw [hb, hbx]
  intro y hy _ hy2 _ _
  have hya : a * y = y * a := (mem_centralizer_iff.1 hy) a (subset_closure (Set.mem_insert _ _))
  have hyb : b * y = y * b :=
    (mem_centralizer_iff.1 hy) b (subset_closure (Set.mem_insert_of_mem _ rfl))
  have hMa : y.val.val * aW A B = aW A B * y.val.val := by
    have e := congrArg (matOf S) hya
    rw [map_mul, map_mul, matOf_apply, matOf_apply, ha] at e
    exact e.symm
  have hMb : y.val.val * bW A B = bW A B * y.val.val := by
    have e := congrArg (matOf S) hyb
    rw [map_mul, map_mul, matOf_apply, matOf_apply, hb] at e
    exact e.symm
  have hM2 : y.val.val * y.val.val = 1 := by
    have e := congrArg (matOf S) hy2
    rwa [map_pow, map_one, matOf_apply, sq] at e
  have hxy : (x * y).val.val = xW A B * y.val.val := by
    rw [← hx]
    rfl
  obtain ⟨c, hc⟩ := hcomm _ hMa hMb
  obtain ⟨L, hLdef⟩ : ∃ L, L = c 2 • T₁ + c 3 • T₂ := ⟨_, rfl⟩
  have hsm : ∀ (r : ZMod 2) (T : MatB), (r • T).rank ≤ T.rank := by
    intro r T
    rcases h01 r with rfl | rfl
    · rw [zero_smul, Matrix.rank_zero]
      exact Nat.zero_le _
    · rw [one_smul]
  have hL : L.rank ≤ 79 := by
    have h1 := hsm (c 2) T₁
    have h2 := hsm (c 3) T₂
    have h3 := rank_add_le' (c 2 • T₁) (c 3 • T₂)
    rw [hLdef]
    omega
  have hML : y.val.val = c 0 • 1 + c 1 • xW A B + L := by rw [hc, add_assoc _ (c 2 • T₁), hLdef]
  rcases h01 (c 0) with h0 | h0 <;> rcases h01 (c 1) with h1 | h1 <;>
    simp only [h0, h1, zero_smul, one_smul, zero_add, add_zero] at hML
  ·
    exfalso
    refine mul_ne_one_of_rank ?_ hM2
    rw [hML]
    exact lt_of_le_of_lt (Matrix.rank_mul_le_left _ _) (by omega)
  ·
    right
    have e : (x * y).val.val + 1 = xW A B * L := by
      rw [hxy, hML, mul_add, hX1, add_comm (1 : MatB) (xW A B * L), add_assoc, add_self_mat,
        add_zero]
    rw [e]
    exact (Matrix.rank_mul_le_right _ _).trans (by omega)
  ·
    left
    have e : y.val.val + 1 = L := by
      rw [hML, add_comm (1 : MatB) L, add_assoc, add_self_mat, add_zero]
    rw [e]
    omega
  ·
    exfalso
    refine mul_ne_one_of_rank ?_ hM2
    rw [hML, sq_add_of_sq_zero _ _ (one_add_sq _ hX1)]
    have h1 := Matrix.rank_mul_le_right (1 + xW A B) L
    have h2 := Matrix.rank_mul_le_left L (1 + xW A B)
    have h3 := Matrix.rank_mul_le_left L L
    have h4 := rank_add_le' ((1 + xW A B) * L + L * (1 + xW A B)) (L * L)
    have h5 := rank_add_le' ((1 + xW A B) * L) (L * (1 + xW A B))
    omega

end CertificateChecks.KernelTwoAC

namespace Certificates

open CertificateChecks

open CFSG.Blueprint

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

open CFSG.Blueprint Subgroup in
theorem certificate15048 : ∃ x : NativeSporadic.B, x ^ 2 = 1 ∧ x ≠ 1 ∧ (x.val.val + 1).rank ≤ 1860 ∧
    ∃ P : Subgroup NativeSporadic.B, ⁅P, P⁆ = P ∧ P ≤ centralizer {x} ∧
      ∀ y ∈ centralizer (P : Set NativeSporadic.B), y * x = x * y → y ^ 2 = 1 → y ≠ 1 →
        y ≠ x → (y.val.val + 1).rank ≤ 1859 ∨ ((x * y).val.val + 1).rank ≤ 1859 := by
  have hf : CFSG.KC.BM.TwoAC.TwoACFact CFSG.Monster.B.genA₁ CFSG.Monster.B.genA₂ := by
    rw [KernelBM.genA₁_eq_stripMat, KernelBM.genA₂_eq_stripMat]
    exact KernelTwoAC.twoAC_fact
  exact KernelTwoAC.classData_of_fact
    (S := NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2)
    (Submonoid.subset_closure (Set.mem_insert _ _))
    (Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)) hf

end Certificates
