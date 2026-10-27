module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp

import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinBlock
import CFSG.LocalAnalysis.StandardType.GGSummandMarkingCentralSurj
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.RankThree.PartTwo.Sec11.Data
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item143N
import CFSG.RankThree.PartTwo.Sec15.Item157
import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.Sec16.Item164Proof
import CFSG.RankThree.PartTwo.Sec16.Item169HJ
import CFSG.RankThree.PartTwo.Sec17.Item1724Two
import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
import CFSG.RankThree.PartTwo.Sec17.RouteProvers
import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec6.Statements
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedSL)


private noncomputable def l02qq2lb_statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem l02qq2lb_statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    l02qq2lb_statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [l02qq2lb_statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem l02qq2lb_specialLinearGroupEquivStatedSL_symm_slConjugation {m : ℕ} {E : Type}
    [Field E] {A : GL (Fin m) E} {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) = A * (l : GL (Fin m) E) * A⁻¹) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l' =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  have hl : (l : GL (Fin m) E) =
      ((e.symm l : Matrix.SpecialLinearGroup (Fin m) E) : GL (Fin m) E) := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l]
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l))
  have h' := congrArg (fun u : GL (Fin m) E => (u : Matrix (Fin m) (Fin m) E)) h
  rw [hl] at h'
  rw [show ((e (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        (e.symm l)) : StatedSL m E) : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
          (e.symm l)) from
    Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E _)]
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact h'

private theorem l02qq2lb_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qq2lb_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qq2lb_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

private theorem l02qq2lb_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : ↥(LargeEvenSLGroup (Fin d) K)) :
    CFSG.StandardType.TypeA.slKerEquiv d K
        (MulAut.conjNormal (H := LargeEvenSLGroup (Fin d) K) A z) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K A
        (CFSG.StandardType.TypeA.slKerEquiv d K z) := by
  apply Subtype.ext
  rw [CFSG.StandardType.TypeA.coe_slKerEquiv,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    CFSG.StandardType.TypeA.coe_slKerEquiv]
  rw [MulAut.conjNormal_apply]
  rfl

private theorem l02qq2lb_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    CFSG.StandardType.TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A z) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A
        (CFSG.StandardType.TypeA.recipeEquiv d K z) := by
  induction z using QuotientGroup.induction_on with
  | H h =>
    rw [TableB.linConjAut_mk]
    change CFSG.StandardType.TypeA.recipeEquiv d K
        (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)
          (MulAut.conjNormal (H := LargeEvenSLGroup (Fin d) K) A h)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A
        (CFSG.StandardType.TypeA.recipeEquiv d K
          (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h))
    rw [CFSG.StandardType.TypeA.recipeEquiv_mk, CFSG.StandardType.TypeA.recipeEquiv_mk,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj,
      l02qq2lb_slKerEquiv_conjNormal]

private theorem l02qq2lb_recipeEquiv_symm_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K) :
    TableB.linConjAut (Fin d) K A ((CFSG.StandardType.TypeA.recipeEquiv d K).symm z) =
      (CFSG.StandardType.TypeA.recipeEquiv d K).symm
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A z) := by
  apply (CFSG.StandardType.TypeA.recipeEquiv d K).injective
  have h := l02qq2lb_recipeEquiv_linConjAut (d := d) (K := K) A
    ((CFSG.StandardType.TypeA.recipeEquiv d K).symm z)
  rw [h, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem q2Lin_block {N : ℕ} (hN : 2 ≤ N) {K : Type} [Field K] [Finite K] [CharP K 2]
    (g : GL (Fin N) K) (hg : Odd (orderOf g)) (C : Subgroup (GL (Fin N) K))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({g} : Set (GL (Fin N) K))))
    (hCSL : C ≤ LargeEvenSLGroup (Fin N) K)
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)))
    (hJ₀ : J₀ = (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))) :
    ∃ (m : ℕ) (D : Type) (_ : Field D) (_ : Finite D)
      (ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) D))
      (π : ↥(Subgroup.centralizer ({g} : Set (GL (Fin N) K))) →* GL (Fin m) D),
      ∀ (h : ↥(Subgroup.centralizer ({g} : Set (GL (Fin N) K)))) (j j' : ↥J₀),
        (j' : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
            TableB.linConjAut (Fin N) K (h : GL (Fin N) K) (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) →
          TableB.linConjAut (Fin m) D (π h) (ψ (QuotientGroup.mk j)) = ψ (QuotientGroup.mk j') := by
  classical
  have hord : (orderOf g : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 2] at h
    exact (Nat.not_even_iff_odd.mpr hg) (even_iff_two_dvd.mpr h)
  have hM : CFSG.Open.IsComponentOf C
      (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
    have hM' : IsComponentOf C
        (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ LargeEvenSLGroup (Fin N) K) :=
      hC.of_le_of_le (le_inf hC.1 hCSL) inf_le_left
    have hM'' : IsComponentOf C
        (Subgroup.centralizer ({g} : Set (GL (Fin N) K)) ⊓ StatedSL N K) := by
      rwa [CFSG.Assembly.largeEvenSLGroup_eq_statedSL N] at hM'
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hM''
  obtain ⟨r, D, d, hFld, hFin, hAlg, Φ, θ, hd1, hΦinj, hθinj, hθrange, hθapply, i, hd2, hMeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsLinBlock_exists g hord C hM
  letI : ∀ j, Field (D j) := hFld
  haveI : ∀ j, Finite (D j) := hFin
  letI : ∀ j, Algebra K (D j) := hAlg
  let mulI : GL (Fin (d i)) (D i) →* (∀ j, GL (Fin (d j)) (D j)) :=
    MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i
  have hmulI_inj : Function.Injective mulI := by
    intro a b hab
    have := congrFun hab i
    simpa [mulI, MonoidHom.mulSingle_apply] using this
  let φ : StatedSL (d i) (D i) →* ↥C :=
    { toFun := fun x => ⟨θ (mulI x), by
        rw [hMeq]
        exact Subgroup.mem_map.mpr ⟨mulI x, Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp [mulI]
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, MonoidHom.map_mul] }
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have h1 : θ (mulI (x : GL (Fin (d i)) (D i))) = θ (mulI (y : GL (Fin (d i)) (D i))) :=
      congrArg Subtype.val hxy
    exact hmulI_inj (hθinj h1)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨c, hc⟩
    have hc' : c ∈ Subgroup.map θ (Subgroup.map mulI (StatedSL (d i) (D i))) := by
      rw [← hMeq]
      exact hc
    obtain ⟨y, hy, hyc⟩ := Subgroup.mem_map.mp hc'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    show θ (mulI x) = c
    rw [hxy, hyc]
  let e : StatedSL (d i) (D i) ≃* ↥C := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hQ : CFSG.Assembly.IsQuasisimple (StatedSL (d i) (D i)) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv e hC.2.2
  have hperf : commutator (StatedSL (d i) (D i)) = ⊤ := hQ.1
  have hperfG : Group.IsPerfect (StatedSL (d i) (D i)) := ⟨hperf⟩
  have hconj_mem : ∀ (A : GL (Fin (d i)) (D i)) (x : StatedSL (d i) (D i)),
      A * (x : GL (Fin (d i)) (D i)) * A⁻¹ ∈ StatedSL (d i) (D i) := by
    intro A x
    have hxL : (x : GL (Fin (d i)) (D i)) ∈ LargeEvenSLGroup (Fin (d i)) (D i) := by
      rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (d i)]
      exact x.2
    have h := (inferInstance : (LargeEvenSLGroup (Fin (d i)) (D i)).Normal).conj_mem
      (x : GL (Fin (d i)) (D i)) hxL A
    rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (d i)] at h
    exact h
  let πCSL : ↥C →* ↥(LargeEvenSLGroup (Fin N) K) := Subgroup.inclusion hCSL
  let πC : ↥C →* ↥J₀ :=
    { toFun := fun c => ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c), by
        rw [hJ₀]
        exact Subgroup.mem_map.mpr ⟨πCSL c, Subgroup.mem_subgroupOf.mpr c.2, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hπC_surj : Function.Surjective πC := by
    rintro ⟨j, hj⟩
    have hj' : j ∈ (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
      rw [← hJ₀]
      exact hj
    obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj'
    refine ⟨⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩, ?_⟩
    apply Subtype.ext
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)
      (πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩) = j
    have hpc : πCSL ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩ = y := Subtype.ext rfl
    rw [hpc]
    exact hyj
  have hπC_ker : πC.ker ≤ Subgroup.center ↥C := by
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hc' : πCSL c ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker := by
      rw [MonoidHom.mem_ker]
      simpa [πC] using congrArg Subtype.val hc
    have hcen := l02qq2lb_ker_projMk_le_center (LargeEvenSLGroup (Fin N) K) hc'
    rw [Subgroup.mem_center_iff] at hcen ⊢
    intro d
    apply Subtype.ext
    show (πCSL d : GL (Fin N) K) * (πCSL c : GL (Fin N) K) =
      (πCSL c : GL (Fin N) K) * (πCSL d : GL (Fin N) K)
    exact congrArg Subtype.val (hcen (πCSL d))
  let gAB : StatedSL (d i) (D i) →* ↥J₀ := πC.comp φ
  have hgAB_surj : Function.Surjective gAB := hπC_surj.comp hφsurj
  have hker : gAB.ker ≤ Subgroup.center (StatedSL (d i) (D i)) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : φ x ∈ πC.ker := by rw [MonoidHom.mem_ker]; exact hx
    have hx2 : φ x ∈ Subgroup.center ↥C := hπC_ker hx1
    rw [Subgroup.mem_center_iff] at hx2 ⊢
    intro y
    apply hφinj
    rw [map_mul, map_mul]
    exact hx2 (φ y)
  let θc : (∀ j, GL (Fin (d j)) (D j)) →*
      ↥(Subgroup.centralizer ({g} : Set (GL (Fin N) K))) :=
    { toFun := fun w => ⟨θ w, by
        rw [← hθrange]
        exact MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp }
  have hθc_inj : Function.Injective θc := by
    intro a b hab
    apply hθinj
    exact congrArg Subtype.val hab
  have hθc_surj : Function.Surjective θc := by
    rintro ⟨h, hh⟩
    have hh' : h ∈ θ.range := by rw [hθrange]; exact hh
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hh'
    exact ⟨w, Subtype.ext hw⟩
  let eθ : (∀ j, GL (Fin (d j)) (D j)) ≃*
      ↥(Subgroup.centralizer ({g} : Set (GL (Fin N) K))) :=
    MulEquiv.ofBijective θc ⟨hθc_inj, hθc_surj⟩
  let projI : (∀ j, GL (Fin (d j)) (D j)) →* GL (Fin (d i)) (D i) :=
    { toFun := fun w => w i
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let π : ↥(Subgroup.centralizer ({g} : Set (GL (Fin N) K))) →* GL (Fin (d i)) (D i) :=
    projI.comp eθ.symm
  let φq : StatedSL (d i) (D i) →* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp gAB
  have hφqsurj : Function.Surjective φq :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).comp hgAB_surj
  have hcomap : (Subgroup.center ↥J₀).comap gAB =
      Subgroup.center (StatedSL (d i) (D i)) :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperfG gAB hgAB_surj hker
  have hφqker : Subgroup.center (StatedSL (d i) (D i)) = φq.ker := by
    dsimp only [φq]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let ecent : StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i)) ≃*
      ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    QuotientGroup.liftEquiv (Subgroup.center (StatedSL (d i) (D i))) (φ := φq)
      hφqsurj hφqker
  have hecent_mk : ∀ a : StatedSL (d i) (D i),
      ecent (QuotientGroup.mk a) = QuotientGroup.mk (gAB a) :=
    fun a => QuotientGroup.liftEquiv_mk (Subgroup.center (StatedSL (d i) (D i)))
      (φ := φq) hφqsurj hφqker a
  let projSL : StatedSL (d i) (D i) ⧸ Subgroup.center (StatedSL (d i) (D i)) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin (d i)) (D i)) :=
    l02qq2lb_statedSLCenterQuotEquivProjective.trans
      (CFSG.StandardType.TypeA.recipeEquiv (d i) (D i)).symm
  let ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin (d i)) (D i)) :=
    ecent.symm.trans projSL
  refine ⟨d i, D i, inferInstance, inferInstance, ψ, π, ?_⟩
  intro h j j' hj'
  have hcomm : (h : GL (Fin N) K) * g = g * (h : GL (Fin N) K) :=
    Subgroup.mem_centralizer_singleton_iff.mp h.2
  have hh_range : (h : GL (Fin N) K) ∈ θ.range := by rw [hθrange]; exact h.2
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hh_range
  let A : GL (Fin (d i)) (D i) := w i
  have heθ : eθ w = h := Subtype.ext hw
  have hπ : π h = A := by
    change projI (eθ.symm h) = A
    rw [show eθ.symm h = w from by rw [← heθ, MulEquiv.symm_apply_apply]]
    rfl
  have hj_map : (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) ∈
      (C.subgroupOf (LargeEvenSLGroup (Fin N) K)).map
        (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
    rw [← hJ₀]; exact j.2
  obtain ⟨y, hy, hyj⟩ := Subgroup.mem_map.mp hj_map
  let c : ↥C := ⟨(y : GL (Fin N) K), Subgroup.mem_subgroupOf.mp hy⟩
  have hpc : πCSL c = y := Subtype.ext rfl
  have hjc : (πC c : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) := by
    change LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (πCSL c) = _
    rw [hpc]
    exact hyj
  let x : StatedSL (d i) (D i) := e.symm c
  have hφx : φ x = c := MulEquiv.apply_symm_apply e c
  have hgAB_x : gAB x = j := by
    change πC (φ x) = j
    rw [hφx]
    exact Subtype.ext hjc
  let y' : StatedSL (d i) (D i) :=
    ⟨A * (x : GL (Fin (d i)) (D i)) * A⁻¹, hconj_mem A x⟩
  have hconj_eq : w * mulI x * w⁻¹ = mulI (y' : GL (Fin (d i)) (D i)) := by
    ext jj
    by_cases hj : jj = i
    · subst hj; simp [mulI, y', A, MonoidHom.mulSingle_apply]
    · simp [mulI, y', A, MonoidHom.mulSingle_apply, hj]
  have hconj : (φ y' : GL (Fin N) K) =
      (h : GL (Fin N) K) * (φ x : GL (Fin N) K) * (h : GL (Fin N) K)⁻¹ := by
    calc (φ y' : GL (Fin N) K)
        = θ (mulI (y' : GL (Fin (d i)) (D i))) := rfl
      _ = θ (w * mulI x * w⁻¹) := by rw [← hconj_eq]
      _ = θ w * θ (mulI x) * (θ w)⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (h : GL (Fin N) K) * (φ x : GL (Fin N) K) * (h : GL (Fin N) K)⁻¹ := by
            rw [hw]; rfl
  have hπCSL : (πCSL c : GL (Fin N) K) = (φ x : GL (Fin N) K) := by
    have h1 : ((φ x : ↥C) : GL (Fin N) K) = (c : GL (Fin N) K) := congrArg Subtype.val hφx
    have h2 : (πCSL c : GL (Fin N) K) = (c : GL (Fin N) K) := rfl
    rw [h2]
    exact h1.symm
  have hconjπ : πCSL (φ y') = MulAut.conjNormal (h : GL (Fin N) K) (πCSL c) := by
    apply Subtype.ext
    change (φ y' : GL (Fin N) K) =
      (MulAut.conjNormal (h : GL (Fin N) K) (πCSL c) : GL (Fin N) K)
    rw [MulAut.conjNormal_apply, hconj, hπCSL]
  have hkey : TableB.linConjAut (Fin N) K (h : GL (Fin N) K)
      (j : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (πC (φ y') : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) := by
    rw [← hjc]
    change TableB.linConjAut (Fin N) K (h : GL (Fin N) K)
        ((πCSL c : ↥(LargeEvenSLGroup (Fin N) K)) :
          LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      ((πCSL (φ y') : ↥(LargeEvenSLGroup (Fin N) K)) :
        LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    rw [TableB.linConjAut_mk, hconjπ]
  have hgAB_y' : gAB y' = j' := by
    apply Subtype.ext
    change (πC (φ y') : LargeEvenProj (LargeEvenSLGroup (Fin N) K)) =
      (j' : LargeEvenProj (LargeEvenSLGroup (Fin N) K))
    rw [← hkey]
    exact hj'.symm
  have hecent_x : ecent (QuotientGroup.mk x) = QuotientGroup.mk j := by
    rw [hecent_mk x, hgAB_x]
  have hecent_y' : ecent (QuotientGroup.mk y') = QuotientGroup.mk j' := by
    rw [hecent_mk y', hgAB_y']
  have hψj : ψ (QuotientGroup.mk j) = projSL (QuotientGroup.mk x) := by
    change projSL (ecent.symm (QuotientGroup.mk j)) = projSL (QuotientGroup.mk x)
    rw [show ecent.symm (QuotientGroup.mk j) = QuotientGroup.mk x from by
      rw [← hecent_x, MulEquiv.symm_apply_apply]]
  have hψj' : ψ (QuotientGroup.mk j') = projSL (QuotientGroup.mk y') := by
    change projSL (ecent.symm (QuotientGroup.mk j')) = projSL (QuotientGroup.mk y')
    rw [show ecent.symm (QuotientGroup.mk j') = QuotientGroup.mk y' from by
      rw [← hecent_y', MulEquiv.symm_apply_apply]]
  rw [hψj, hψj', hπ]
  have hslconj :
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm y' =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (d i) (D i) A
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm x) :=
    l02qq2lb_specialLinearGroupEquivStatedSL_symm_slConjugation (A := A)
      (l := x) (l' := y') rfl
  have hprojSL : ∀ z : StatedSL (d i) (D i),
      projSL (QuotientGroup.mk z) =
        (CFSG.StandardType.TypeA.recipeEquiv (d i) (D i)).symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (d i) (D i)
            ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm z)) := by
    intro z
    change (CFSG.StandardType.TypeA.recipeEquiv (d i) (D i)).symm
        (l02qq2lb_statedSLCenterQuotEquivProjective (QuotientGroup.mk z)) = _
    rw [l02qq2lb_statedSLCenterQuotEquivProjective_mk]
  rw [hprojSL x, hprojSL y']
  rw [l02qq2lb_recipeEquiv_symm_linConjAut A
    (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj (d i) (D i)
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (d i) (D i)).symm x))]
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  rw [hslconj]

end CFSG.StandardType
