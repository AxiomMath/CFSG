module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPComp
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
public import CFSG.HardMathSupport.Solomon.Coordinator.L3C143AltMain
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Input252
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
public import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalanceThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Transitive
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Inputs
public import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.HeldB.Common
public import Certificates.Certificate14953
public import Certificates.Certificate7233Base
public import Certificates.Certificate8166
import CFSG.Assembly.OpenBridges
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup exists_glaPComponent_map_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open scoped commutatorElement

private lemma llft_conj_scalar_mul {n : Type} [DecidableEq n] [Fintype n] {K : Type} [Field K]
    (c : Kˣ) (x y : GL n K) :
    x⁻¹ * (x * y * x⁻¹ * Matrix.GeneralLinearGroup.scalar n c) * x =
      Matrix.GeneralLinearGroup.scalar n c * y := by
  have hx : x⁻¹ * Matrix.GeneralLinearGroup.scalar n c * x =
      Matrix.GeneralLinearGroup.scalar n c := by
    rw [show x⁻¹ * Matrix.GeneralLinearGroup.scalar n c =
        Matrix.GeneralLinearGroup.scalar n c * x⁻¹ from
      (Matrix.GeneralLinearGroup.scalar_commute c x⁻¹).symm]
    group
  calc x⁻¹ * (x * y * x⁻¹ * Matrix.GeneralLinearGroup.scalar n c) * x
      = y * (x⁻¹ * Matrix.GeneralLinearGroup.scalar n c * x) := by group
    _ = y * Matrix.GeneralLinearGroup.scalar n c := by rw [hx]
    _ = Matrix.GeneralLinearGroup.scalar n c * y :=
          (Matrix.GeneralLinearGroup.scalar_commute c y).symm

theorem ggNbrLSideLin_map_le_of_perfect {G : Type} [Group G] {S N : Subgroup G}
    (hS : ⁅S, S⁆ = S) (hN : N ≤ Subgroup.center G) (γ : MulAut G)
    (h : ∀ s ∈ S, ∃ t ∈ S, ∃ z ∈ N, γ s = t * z) : ∀ s ∈ S, γ s ∈ S := by
  have hle : S ≤ S ⊓ S.comap (γ : G →* G) := by
    have hcomm_le : ⁅S, S⁆ ≤ S ⊓ S.comap (γ : G →* G) := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro x ⟨a, ha, b, hb, rfl⟩
      obtain ⟨ta, hta, za, hza, hγa⟩ := h a ha
      obtain ⟨tb, htb, zb, hzb, hγb⟩ := h b hb
      have hzaC : ∀ y : G, y * za = za * y := Subgroup.mem_center_iff.mp (hN hza)
      have hzbC : ∀ y : G, y * zb = zb * y := Subgroup.mem_center_iff.mp (hN hzb)
      have hperm : ⁅ta * za, tb * zb⁆ = ⁅ta, tb⁆ := by
        have h1 : ⁅za, tb * zb⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact (hzaC (tb * zb)).symm
        have h2 : ⁅ta, zb⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_mul_comm]
          exact hzbC ta
        rw [commutatorElement_mul_left_eq_conj_mul, h1,
          commutatorElement_mul_right_eq_mul_conj, h2]
        group
      change ⁅a, b⁆ ∈ S ∧ ⁅a, b⁆ ∈ S.comap (γ : G →* G)
      refine ⟨hS ▸ Subgroup.commutator_mem_commutator ha hb, ?_⟩
      rw [Subgroup.mem_comap, map_commutatorElement]
      change ⁅γ a, γ b⁆ ∈ S
      rw [hγa, hγb, hperm]
      exact hS ▸ Subgroup.commutator_mem_commutator hta htb
    rwa [hS] at hcomm_le
  intro s hs
  exact Subgroup.mem_comap.mpr ((hle hs).2)

theorem ggNbrLSideLin_commScalar {K : Type} [Field K] (h2 : (2 : K) = 0) {d : ℕ}
    {A B : GL (Fin d) K} {φ ψ : MulAut (LargeEvenProj (StatedSL d K))}
    (hφ : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hψ : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = B * (h : GL (Fin d) K) * B⁻¹ →
      ψ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hcomm : φ * ψ = ψ * φ) :
    ∃ μ : Kˣ, B * A * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) μ * A := by
  by_cases hd : d = 0
  · subst hd
    refine ⟨1, ?_⟩
    haveI : Subsingleton (GL (Fin 0) K) :=
      ⟨fun a b => Units.ext (Subsingleton.elim (a : Matrix (Fin 0) (Fin 0) K) b)⟩
    exact Subsingleton.elim (B * A * B⁻¹) (Matrix.GeneralLinearGroup.scalar (Fin 0) 1 * A)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    haveI : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
    let C : GL (Fin d) K := (A * B)⁻¹ * (B * A)
    have key : ∀ h : ↥(StatedSL d K), ∃ c : Kˣ,
        C * (h : GL (Fin d) K) * C⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin d) c * (h : GL (Fin d) K) := by
      intro h
      have hψB : ψ (LargeEvenProjMk (StatedSL d K) h) =
          LargeEvenProjMk (StatedSL d K) (conjSL B h) :=
        hψ h (conjSL B h) (conjSL_apply_val B h)
      have hφA : φ (LargeEvenProjMk (StatedSL d K) h) =
          LargeEvenProjMk (StatedSL d K) (conjSL A h) :=
        hφ h (conjSL A h) (conjSL_apply_val A h)
      have hXY : φ (ψ (LargeEvenProjMk (StatedSL d K) h)) =
          LargeEvenProjMk (StatedSL d K) (conjSL A (conjSL B h)) := by
        rw [hψB]
        exact hφ (conjSL B h) (conjSL A (conjSL B h)) (conjSL_apply_val A (conjSL B h))
      have hYX : ψ (φ (LargeEvenProjMk (StatedSL d K) h)) =
          LargeEvenProjMk (StatedSL d K) (conjSL B (conjSL A h)) := by
        rw [hφA]
        exact hψ (conjSL A h) (conjSL B (conjSL A h)) (conjSL_apply_val B (conjSL A h))
      have heq : LargeEvenProjMk (StatedSL d K) (conjSL A (conjSL B h)) =
          LargeEvenProjMk (StatedSL d K) (conjSL B (conjSL A h)) := by
        have hh := congrArg (fun f : MulAut (LargeEvenProj (StatedSL d K)) =>
          f (LargeEvenProjMk (StatedSL d K) h)) hcomm
        rw [MulAut.mul_apply, MulAut.mul_apply, hXY, hYX] at hh
        exact hh
      obtain ⟨c, hc⟩ :=
        (projMk_eq_iff (conjSL A (conjSL B h)) (conjSL B (conjSL A h))).mp heq
      refine ⟨c, ?_⟩
      have hAB : ((conjSL A (conjSL B h) : ↥(StatedSL d K)) : GL (Fin d) K) =
          (A * B) * (h : GL (Fin d) K) * (A * B)⁻¹ := by
        rw [conjSL_apply_val, conjSL_apply_val]; group
      have hBA : ((conjSL B (conjSL A h) : ↥(StatedSL d K)) : GL (Fin d) K) =
          (B * A) * (h : GL (Fin d) K) * (B * A)⁻¹ := by
        rw [conjSL_apply_val, conjSL_apply_val]; group
      have hYeq : ((conjSL B (conjSL A h) : ↥(StatedSL d K)) : GL (Fin d) K) =
          ((conjSL A (conjSL B h) : ↥(StatedSL d K)) : GL (Fin d) K) *
            Matrix.GeneralLinearGroup.scalar (Fin d) c := by
        rw [hc]; group
      have h1 : (B * A) * (h : GL (Fin d) K) * (B * A)⁻¹ =
          (A * B) * (h : GL (Fin d) K) * (A * B)⁻¹ *
            Matrix.GeneralLinearGroup.scalar (Fin d) c := by
        rw [← hBA, hYeq, hAB]
      calc C * (h : GL (Fin d) K) * C⁻¹
          = (A * B)⁻¹ * ((B * A) * (h : GL (Fin d) K) * (B * A)⁻¹) * (A * B) := by
              rw [show C = (A * B)⁻¹ * (B * A) from rfl]; group
        _ = (A * B)⁻¹ * ((A * B) * (h : GL (Fin d) K) * (A * B)⁻¹ *
              Matrix.GeneralLinearGroup.scalar (Fin d) c) * (A * B) := by rw [h1]
        _ = Matrix.GeneralLinearGroup.scalar (Fin d) c * (h : GL (Fin d) K) :=
              llft_conj_scalar_mul c (A * B) (h : GL (Fin d) K)
    have H : ∀ g : GL (Fin d) K, g ∈ StatedSL d K → ∃ c : K,
        (C : Matrix (Fin d) (Fin d) K) * (g : Matrix (Fin d) (Fin d) K) *
          ((C⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
            c • (g : Matrix (Fin d) (Fin d) K) := by
      intro g hg
      let h : ↥(StatedSL d K) := ⟨g, hg⟩
      obtain ⟨c, hc⟩ := key h
      refine ⟨(c : K), ?_⟩
      have hv := congrArg (fun z : GL (Fin d) K => (z : Matrix (Fin d) (Fin d) K)) hc
      simp only [Units.val_mul] at hv
      rw [show (h : GL (Fin d) K) = g from rfl] at hv
      rw [hv, val_scalar_gl, Matrix.smul_mul, Matrix.one_mul]
    obtain ⟨c₀, hc₀⟩ := gl_isScalar_of_conj_mod_scalar h2 C H
    have hc₀ne : c₀ ≠ 0 := by
      intro h0
      have hC0 : (C : Matrix (Fin d) (Fin d) K) = 0 := by rw [hc₀, h0, zero_smul]
      have hmul : (C : Matrix (Fin d) (Fin d) K) *
          ((C⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv C
      have h10 : (1 : Matrix (Fin d) (Fin d) K) = 0 := by rw [← hmul, hC0, zero_mul]
      exact one_ne_zero h10
    let μ : Kˣ := Units.mk0 c₀ hc₀ne
    have hCscalar : C = Matrix.GeneralLinearGroup.scalar (Fin d) μ := by
      apply Units.ext
      dsimp only [μ]
      rw [val_scalar_gl]
      simpa using hc₀
    have hBA_eq : B * A = (A * B) * Matrix.GeneralLinearGroup.scalar (Fin d) μ := by
      have h := congrArg (fun z : GL (Fin d) K => (A * B) * z) hCscalar
      rw [← h]
      show B * A = (A * B) * ((A * B)⁻¹ * (B * A))
      group
    refine ⟨μ, ?_⟩
    have hBs : B * Matrix.GeneralLinearGroup.scalar (Fin d) μ * B⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) μ := by
      rw [show B * Matrix.GeneralLinearGroup.scalar (Fin d) μ =
          Matrix.GeneralLinearGroup.scalar (Fin d) μ * B from
        (Matrix.GeneralLinearGroup.scalar_commute μ B).symm]
      group
    calc B * A * B⁻¹
        = (A * B) * Matrix.GeneralLinearGroup.scalar (Fin d) μ * B⁻¹ := by rw [hBA_eq]
      _ = A * (B * Matrix.GeneralLinearGroup.scalar (Fin d) μ * B⁻¹) := by group
      _ = A * Matrix.GeneralLinearGroup.scalar (Fin d) μ := by rw [hBs]
      _ = Matrix.GeneralLinearGroup.scalar (Fin d) μ * A :=
            (Matrix.GeneralLinearGroup.scalar_commute μ A).symm

theorem ggNbrLSideLin_lift {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    (A : GL (Fin d) K) (φ : MulAut (LargeEvenProj (StatedSL d K)))
    (hφ : ∀ h h' : ↥(StatedSL d K), (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
      φ (LargeEvenProjMk (StatedSL d K) h) = LargeEvenProjMk (StatedSL d K) h')
    (hφ3 : φ ^ 3 = 1) {J : Subgroup (LargeEvenProj (StatedSL d K))}
    (hJ : GLAPComponent 3 (fixSubgroup φ) J) :
    ∃ M₀ : Subgroup ↥(StatedSL d K), M₀.map (LargeEvenProjMk (StatedSL d K)) = J ∧
      CFSG.Open.IsComponentOf (M₀.map (StatedSL d K).subtype)
        (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K) := by
  classical
  have hd : 1 ≤ d := by
    by_contra hd0
    obtain rfl : d = 0 := by omega
    haveI : Subsingleton (LargeEvenProj (StatedSL 0 K)) := inferInstance
    haveI := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial
      (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
    obtain ⟨a, b, hab⟩ := exists_pair_ne (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 J)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (congrArg _ (Subtype.ext (Subsingleton.elim _ _)))
  obtain ⟨c, hc⟩ := Y10GInnLin.isScalar_of_pow_trivial h2 A 3 φ hφ hφ3
  have hodd : Odd (orderOf A) :=
    Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A (Nat.prime_three.odd_of_ne_two (by norm_num)) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 := Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨M₀, hM₀, hM₀J⟩ := exists_glaPComponent_map_fixSubgroup
    (LargeEvenProjMk (StatedSL d K)) Y10GInnLin.ker_projMk_le_center (Y10GInnLin.conjSL A) φ
    (fun k => (hφ k (Y10GInnLin.conjSL A k) rfl).symm) QuotientGroup.mk_surjective
    Nat.prime_three hJ
  have hMinj : Function.Injective (StatedSL d K).subtype := Subtype.val_injective
  have hM' : GLAPComponent 3 (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K)
      (M₀.map (StatedSL d K).subtype) := by
    rw [← Y10GInnLin.map_fixSubgroup_conjSL A]
    exact (CFSG.LocalAnalysis.GLTheoremA.Y10F.glaPComponent_map_iff Nat.prime_three hMinj).mpr hM₀
  exact ⟨M₀, hM₀J, Y10GInnLin.LinPCompIsComp_holds K d 3 Nat.prime_three A hord
    (M₀.map (StatedSL d K).subtype) hM'⟩

end CFSG.StandardType

end
