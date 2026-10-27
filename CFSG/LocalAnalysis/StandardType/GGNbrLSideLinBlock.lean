module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLSideLinDim
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinBlock
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinField
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
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
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open scoped Matrix

private theorem lblk_mulSingle_conj {r : ℕ} {G : Fin r → Type} [∀ j, Group (G j)]
    (i : Fin r) (w : ∀ j, G j) (x : G i) :
    w * MonoidHom.mulSingle G i x * w⁻¹ =
      MonoidHom.mulSingle G i (w i * x * (w i)⁻¹) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [MonoidHom.mulSingle_apply]
  · simp only [Pi.mul_apply, Pi.inv_apply, MonoidHom.mulSingle_apply]
    rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
    simp

private theorem lblk_pi_mul_single {r : ℕ} {M : Fin r → Type} [∀ j, NonUnitalNonAssocSemiring (M j)]
    (i : Fin r) (W : ∀ j, M j) (Y : M i) :
    W * Pi.single (M := M) i Y = Pi.single (M := M) i (W i * Y) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

private theorem lblk_pi_single_smul {K : Type} [Field K] {r : ℕ} {M : Fin r → Type}
    [∀ j, AddCommMonoid (M j)] [∀ j, Module K (M j)]
    (i : Fin r) (γ : K) (Y : M i) :
    Pi.single (M := M) i (γ • Y) = γ • Pi.single (M := M) i Y := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

private theorem lblk_scalar_eq_smul_one {K : Type} [Field K] {a : ℕ} (c : K) :
    Matrix.scalar (Fin a) c = c • (1 : Matrix (Fin a) (Fin a) K) := by
  ext p q
  by_cases hpq : p = q <;> simp [Matrix.scalar_apply, hpq]

private theorem lblk_mulVec_inv_mul {K : Type} [Field K] {n : ℕ} (B : GL (Fin n) K)
    (u : Fin n → K) :
    (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ
      ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec]
  have h : ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (B : Matrix (Fin n) (Fin n) K) = 1 := Units.inv_mul B
  rw [h, Matrix.one_mulVec]

private theorem lblk_exists_mulVec_ne_zero {K : Type} [Field K] {n : ℕ}
    {M : Matrix (Fin n) (Fin n) K} (hM : M ≠ 0) : ∃ v : Fin n → K, M *ᵥ v ≠ 0 := by
  by_contra h
  push Not at h
  apply hM
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h1
  simpa using h1

private theorem lblk_mu_eq_one_of_eigen {K : Type} [Field K] {n : ℕ} {A B : GL (Fin n) K}
    {μ γ : K}
    (hAB : (A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) =
      μ⁻¹ • ((B : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K)))
    {u : Fin n → K} (hu : u ≠ 0)
    (hAu : (A : Matrix (Fin n) (Fin n) K) *ᵥ u = γ • u)
    (hABu : (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      γ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u)) :
    μ = 1 := by
  have hB_ne : ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) ≠ 0 := by
    intro h0
    apply hu
    have h := lblk_mulVec_inv_mul B u
    rw [h0, Matrix.mulVec_zero] at h
    exact h.symm
  have hA_ne : ((A : Matrix (Fin n) (Fin n) K) *ᵥ u) ≠ 0 := by
    intro h0
    apply hu
    have h := lblk_mulVec_inv_mul A u
    rw [h0, Matrix.mulVec_zero] at h
    exact h.symm
  have hγ : γ ≠ 0 := by
    intro h0
    apply hA_ne
    rw [hAu, h0, zero_smul]
  have h1 : γ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) =
      (μ⁻¹ * γ) • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) := by
    calc γ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u)
        = (A : Matrix (Fin n) (Fin n) K) *ᵥ ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) :=
          hABu.symm
      _ = μ⁻¹ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ ((A : Matrix (Fin n) (Fin n) K) *ᵥ u)) := by
            rw [Matrix.mulVec_mulVec, hAB, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
      _ = μ⁻¹ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ (γ • u)) := by rw [hAu]
      _ = μ⁻¹ • (γ • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u)) := by rw [Matrix.mulVec_smul]
      _ = (μ⁻¹ * γ) • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) := by rw [smul_smul]
  have h2 : (γ - μ⁻¹ * γ) • ((B : Matrix (Fin n) (Fin n) K) *ᵥ u) = 0 := by
    rw [sub_smul, h1, sub_self]
  have hcoef : γ - μ⁻¹ * γ = 0 := (smul_eq_zero.mp h2).resolve_right hB_ne
  have hmul : γ * (1 - μ⁻¹) = 0 := by
    have hcoef' : γ - γ * μ⁻¹ = 0 := by
      rw [mul_comm μ⁻¹ γ] at hcoef
      exact hcoef
    rw [mul_sub, mul_one]
    exact hcoef'
  have h1m : 1 - μ⁻¹ = 0 := (mul_eq_zero.mp hmul).resolve_left hγ
  exact inv_eq_one.mp (sub_eq_zero.mp h1m).symm

private theorem lblk_A_mul_sub_one
    {K : Type} [Field K] {d r : ℕ} {D : Fin r → Type} {blk : Fin r → ℕ}
    [∀ j, Field (D j)] [∀ j, Algebra K (D j)]
    (Φ : (∀ j, Matrix (Fin (blk j)) (Fin (blk j)) (D j)) →ₐ[K] Matrix (Fin d) (Fin d) K)
    (θ : (∀ j, GL (Fin (blk j)) (D j)) →* GL (Fin d) K)
    (hθΦ : ∀ w, ((θ w : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Φ (fun j => ((w j : GL (Fin (blk j)) (D j)) : Matrix (Fin (blk j)) (Fin (blk j)) (D j))))
    (A : GL (Fin d) K) (wA : ∀ j, GL (Fin (blk j)) (D j)) (hwA : θ wA = A)
    (i : Fin r) (a₀ : (D i)ˣ)
    (ha₀ : Matrix.GeneralLinearGroup.scalar (Fin (blk i)) a₀ = wA i)
    (γ : K) (hγ : (a₀ : D i) = algebraMap K (D i) γ)
    (x : ↥(StatedSL (blk i) (D i)))
    (m : GL (Fin d) K)
    (hm : m = θ (MonoidHom.mulSingle (fun j => GL (Fin (blk j)) (D j)) i x)) :
    (A : Matrix (Fin d) (Fin d) K) * ((m : Matrix (Fin d) (Fin d) K) - 1) =
      γ • ((m : Matrix (Fin d) (Fin d) K) - 1) := by
  classical
  set W : ∀ j, Matrix (Fin (blk j)) (Fin (blk j)) (D j) :=
    fun j => ((wA j : GL (Fin (blk j)) (D j)) : Matrix (Fin (blk j)) (Fin (blk j)) (D j))
    with hW
  set F : ∀ j, Matrix (Fin (blk j)) (Fin (blk j)) (D j) :=
    fun j => (((MonoidHom.mulSingle (fun j => GL (Fin (blk j)) (D j)) i x) j :
      GL (Fin (blk j)) (D j)) : Matrix (Fin (blk j)) (Fin (blk j)) (D j)) with hF
  have hAexpr : (A : Matrix (Fin d) (Fin d) K) = Φ W := by
    rw [← hwA, hθΦ wA]
  have hmexpr : (m : Matrix (Fin d) (Fin d) K) = Φ F := by
    rw [hm, hθΦ (MonoidHom.mulSingle (fun j => GL (Fin (blk j)) (D j)) i x)]
  have hF1 : F - 1 = Pi.single i
      (((x : GL (Fin (blk i)) (D i)) : Matrix (Fin (blk i)) (Fin (blk i)) (D i)) - 1) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hF, MonoidHom.mulSingle_apply]
    · simp [hF, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj, Pi.single_eq_of_ne hj]
  have hWi : W i = Matrix.scalar (Fin (blk i)) (a₀ : D i) := by
    change ((wA i : GL (Fin (blk i)) (D i)) : Matrix (Fin (blk i)) (Fin (blk i)) (D i)) =
      Matrix.scalar (Fin (blk i)) (a₀ : D i)
    rw [← ha₀]
    rfl
  have hWm : W * (F - 1) = γ • (F - 1) := by
    rw [hF1, lblk_pi_mul_single]
    rw [hWi, lblk_scalar_eq_smul_one, Matrix.smul_mul, Matrix.one_mul, hγ, algebraMap_smul]
    rw [lblk_pi_single_smul]
  have hsub : Φ F - 1 = Φ (F - 1) := by
    rw [show (1 : Matrix (Fin d) (Fin d) K) = Φ 1 from (map_one Φ).symm, map_sub]
  calc (A : Matrix (Fin d) (Fin d) K) * ((m : Matrix (Fin d) (Fin d) K) - 1)
      = Φ W * (Φ F - 1) := by rw [hAexpr, hmexpr]
    _ = Φ W * Φ (F - 1) := by rw [hsub]
    _ = Φ (W * (F - 1)) := by rw [map_mul]
    _ = Φ (γ • (F - 1)) := by rw [hWm]
    _ = γ • Φ (F - 1) := by rw [map_smul]
    _ = γ • (Φ F - 1) := by rw [hsub]
    _ = γ • ((m : Matrix (Fin d) (Fin d) K) - 1) := by rw [hmexpr]

theorem ggNbrLSideLin_block {K : Type} [Field K] [Finite K] (h2 : (2 : K) = 0) {d : ℕ}
    {A B : GL (Fin d) K}
    (hA3 : ∃ c : K, ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      c • (1 : Matrix (Fin d) (Fin d) K))
    {μ : Kˣ} (hBA : B * A * B⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin d) μ * A)
    {M : Subgroup (GL (Fin d) K)}
    (hM : CFSG.Open.IsComponentOf M
      (Subgroup.centralizer ({A} : Set (GL (Fin d) K)) ⊓ StatedSL d K))
    (hBM : ∀ m ∈ M, B * m * B⁻¹ ∈ M) :
    ∃ (a : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E)
      (e : ↥M ≃* ↥(StatedSL a E)), 2 ≤ a ∧ a * Module.finrank K E ≤ d ∧
      (μ = 1 → ∃ N : GL (Fin a) E, ∀ m : ↥M,
        ((e ⟨B * (m : GL (Fin d) K) * B⁻¹, hBM m m.2⟩ : ↥(StatedSL a E)) : GL (Fin a) E) =
          N * ((e m : ↥(StatedSL a E)) : GL (Fin a) E) * N⁻¹) ∧
      (μ ≠ 1 → 3 ∣ Module.finrank K E) := by
  classical
  have hd : 1 ≤ d := by
    by_contra hlt
    have hd0 : d = 0 := by omega
    haveI : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    have hcomm : ∀ a b : ↥M, a * b = b * a := by
      intro a b
      apply Subtype.ext
      apply Units.ext
      funext i j
      exact (IsEmpty.false i).elim
    exact CFSG.LieType.SemisimpleCentralizers.Held.not_isQuasisimple_of_comm hcomm hM.2.2
  have hA3copy := hA3
  obtain ⟨c, hc⟩ := hA3
  have hodd : Odd (orderOf A) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.odd_orderOf_of_pow_scalar h2 hd A
      (by norm_num : Odd 3) hc
  have hord : ((orderOf A : ℕ) : K) ≠ 0 :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.cast_orderOf_ne_zero_of_odd h2 A hodd
  obtain ⟨r, D, blk, hFld, hFin, hAlg, Φ, θ, hblk, hΦ, hθ, hθA, hθΦ, i, hi, hMeq⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsLinBlock_exists A hord M hM
  letI : ∀ j, Field (D j) := hFld
  letI : ∀ j, Finite (D j) := hFin
  letI : ∀ j, Algebra K (D j) := hAlg
  let mS : GL (Fin (blk i)) (D i) →* (∀ j, GL (Fin (blk j)) (D j)) :=
    MonoidHom.mulSingle (fun j => GL (Fin (blk j)) (D j)) i
  have hms : Function.Injective mS := by
    intro a b hab
    have := congrFun hab i
    simpa [mS, MonoidHom.mulSingle_apply] using this
  let eJ : ↥M ≃* ↥(StatedSL (blk i) (D i)) :=
    (MulEquiv.subgroupCongr hMeq).trans
      ((Subgroup.equivMapOfInjective ((StatedSL (blk i) (D i)).map mS) θ hθ).symm.trans
        (Subgroup.equivMapOfInjective (StatedSL (blk i) (D i)) mS hms).symm)
  have heJ : ∀ x : ↥(StatedSL (blk i) (D i)),
      eJ ⟨θ (mS x),
        hMeq.symm ▸ Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem mS x.2)⟩ = x := by
    intro x
    have hmem : θ (mS x) ∈ M :=
      hMeq.symm ▸ Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem mS x.2)
    change eJ ⟨θ (mS x), hmem⟩ = x
    have hsymm : eJ.symm x = ⟨θ (mS x), hmem⟩ := by
      apply Subtype.ext
      rfl
    rw [← hsymm, MulEquiv.apply_symm_apply]
  have hdim : blk i * Module.finrank K (D i) ≤ d := ggNbrLSideLin_dim Φ hΦ i
  have hμ3 : μ ^ 3 = 1 := by
    have hc0 : c ≠ 0 := by
      intro h0
      have hA3inv : ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (((A ^ 3)⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv (A ^ 3)
      rw [hc, h0, zero_smul, zero_mul] at hA3inv
      have hp : Fin d := ⟨0, hd⟩
      have hcontr : (0 : K) = 1 := by simpa using congrFun (congrFun hA3inv hp) hp
      exact zero_ne_one hcontr
    let u : Kˣ := Units.mk0 c hc0
    have hAu : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) u := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, lblk_scalar_eq_smul_one]
      exact hc
    have hconj : B * A ^ 3 * B⁻¹ = (B * A * B⁻¹) ^ 3 := by
      rw [← MulAut.conj_apply B A, ← map_pow (MulAut.conj B) A 3, MulAut.conj_apply B (A ^ 3)]
    rw [hBA] at hconj
    have hscal : Commute (Matrix.GeneralLinearGroup.scalar (Fin d) μ) A :=
      Matrix.GeneralLinearGroup.scalar_commute μ A
    have hpow : (Matrix.GeneralLinearGroup.scalar (Fin d) μ * A) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) * A ^ 3 := by
      rw [Commute.mul_pow hscal, ← map_pow]
    have hleft : B * A ^ 3 * B⁻¹ = A ^ 3 := by
      rw [hAu]
      rw [show B * Matrix.GeneralLinearGroup.scalar (Fin d) u * B⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin d) u by
        rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute u B⁻¹, ← mul_assoc]
        simp]
    have heq : Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) * A ^ 3 = A ^ 3 := by
      rw [← hpow, ← hconj, hleft]
    have hone : Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) = 1 := by
      exact mul_right_cancel (show Matrix.GeneralLinearGroup.scalar (Fin d) (μ ^ 3) * A ^ 3 =
        1 * A ^ 3 by rw [one_mul]; exact heq)
    have hmat : Matrix.scalar (Fin d) ((μ ^ 3 : Kˣ) : K) = 1 := by
      have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hone
      simpa only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one] using h
    have hp : Fin d := ⟨0, hd⟩
    have hentry := congrFun (congrFun hmat hp) hp
    exact Units.ext (by simpa [Matrix.scalar_apply] using hentry)
  have hmu1 : μ = 1 → ∃ N : GL (Fin (blk i)) (D i), ∀ m : ↥M,
      ((eJ ⟨B * (m : GL (Fin d) K) * B⁻¹, hBM m m.2⟩ : ↥(StatedSL (blk i) (D i))) :
        GL (Fin (blk i)) (D i)) =
        N * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) * N⁻¹ := by
    intro hμeq
    have hBA1 : B * A * B⁻¹ = A := by
      rw [hBA, hμeq, map_one, one_mul]
    have hBcent : B ∈ Subgroup.centralizer ({A} : Set (GL (Fin d) K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      exact (mul_inv_eq_iff_eq_mul.mp hBA1).symm
    have hBrange : B ∈ θ.range := by rw [hθA]; exact hBcent
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hBrange
    refine ⟨w i, ?_⟩
    intro m
    have hmrepr : (m : GL (Fin d) K) = θ (mS (eJ m)) := by
      have hm_mem : (m : GL (Fin d) K) ∈ ((StatedSL (blk i) (D i)).map mS).map θ :=
        hMeq ▸ m.2
      obtain ⟨y, hy, hmy⟩ := Subgroup.mem_map.mp hm_mem
      obtain ⟨z, hz, hyz⟩ := Subgroup.mem_map.mp hy
      have hmz : (m : GL (Fin d) K) = θ (mS z) := by rw [← hmy, hyz]
      have heqz : eJ m = ⟨z, hz⟩ := by
        rw [show m = ⟨θ (mS z),
          hMeq.symm ▸ Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem mS hz)⟩ from
          Subtype.ext hmz]
        exact heJ ⟨z, hz⟩
      rw [hmz, heqz]
    have hBconj : B * (m : GL (Fin d) K) * B⁻¹ =
        θ (mS (w i * eJ m * (w i)⁻¹)) := by
      rw [hmrepr, ← hw]
      rw [← map_inv, ← map_mul, ← map_mul]
      rw [show w * mS (eJ m) * w⁻¹ = mS (w i * eJ m * (w i)⁻¹) from
        lblk_mulSingle_conj i w (eJ m)]
    have hz'mem : w i * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) *
        (w i)⁻¹ ∈ StatedSL (blk i) (D i) := by
      have hmem : θ (mS (w i * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) *
          (w i)⁻¹)) ∈ M := by
        rw [← hBconj]; exact hBM m m.2
      have hmem' : θ (mS (w i * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) *
          (w i)⁻¹)) ∈ ((StatedSL (blk i) (D i)).map mS).map θ := hMeq ▸ hmem
      obtain ⟨y, hy, hmy⟩ := Subgroup.mem_map.mp hmem'
      obtain ⟨z, hz, hyz⟩ := Subgroup.mem_map.mp hy
      have hz' : z = w i * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) *
          (w i)⁻¹ := by
        apply hms
        apply hθ
        rw [hyz, hmy]
      rw [hz'] at hz
      exact hz
    let z' : ↥(StatedSL (blk i) (D i)) :=
      ⟨w i * ((eJ m : ↥(StatedSL (blk i) (D i))) : GL (Fin (blk i)) (D i)) * (w i)⁻¹, hz'mem⟩
    have harg : (⟨B * (m : GL (Fin d) K) * B⁻¹, hBM m m.2⟩ : ↥M) =
        ⟨θ (mS z'), hMeq.symm ▸ Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem mS z'.2)⟩ :=
      Subtype.ext hBconj
    rw [harg, heJ z']
  have hmune : μ ≠ 1 → 3 ∣ Module.finrank K (D i) := by
    intro hμne
    have hA_range : A ∈ θ.range := by
      rw [hθA, Subgroup.mem_centralizer_iff]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      rfl
    obtain ⟨wA, hwA⟩ := MonoidHom.mem_range.mp hA_range
    have hwA_center : wA ∈ Subgroup.center (∀ j, GL (Fin (blk j)) (D j)) := by
      rw [Subgroup.mem_center_iff]
      intro v
      apply hθ
      rw [map_mul, map_mul, hwA]
      have hv : θ v ∈ Subgroup.centralizer ({A} : Set (GL (Fin d) K)) := by
        rw [← hθA]; exact ⟨v, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hv A (by simp)).symm
    have hcenter (j : Fin r) : wA j ∈ Subgroup.center (GL (Fin (blk j)) (D j)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := Subgroup.mem_center_iff.mp hwA_center
        (MonoidHom.mulSingle (fun k => GL (Fin (blk k)) (D k)) j g)
      have h2 := congrFun h j
      simp only [Pi.mul_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at h2
      exact h2
    have hwA_scalar (j : Fin r) : ∃ a : (D j)ˣ,
        Matrix.GeneralLinearGroup.scalar (Fin (blk j)) a = wA j := by
      have h : wA j ∈ (Matrix.GeneralLinearGroup.scalar (Fin (blk j))).range := by
        rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact hcenter j
      exact MonoidHom.mem_range.mp h
    obtain ⟨a₀, ha₀⟩ := hwA_scalar i
    have ha₀_pow_mem : ((a₀ : D i) ^ 3) ∈ (algebraMap K (D i)).range := by
      obtain ⟨c₀, hc₀⟩ := hA3copy
      have hA3expr : ((A ^ 3 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
          Φ (fun j => (((wA j) ^ 3 : GL (Fin (blk j)) (D j))
            : Matrix (Fin (blk j)) (Fin (blk j)) (D j))) := by
        have hpow : A ^ 3 = θ (wA ^ 3) := by rw [← hwA, ← map_pow]
        rw [hpow, hθΦ (wA ^ 3)]
        congr 1
      have hcoords3 : (fun j => (((wA j) ^ 3 : GL (Fin (blk j)) (D j))
            : Matrix (Fin (blk j)) (Fin (blk j)) (D j)))
          = algebraMap K (∀ j, Matrix (Fin (blk j)) (Fin (blk j)) (D j)) c₀ := by
        apply hΦ
        rw [AlgHom.commutes, ← hA3expr, hc₀, Algebra.algebraMap_eq_smul_one]
      refine ⟨c₀, ?_⟩
      have hcoord_i := (congrFun hcoords3 i).symm
      have hp : Fin (blk i) := ⟨0, by have := hblk i; omega⟩
      have hentry := congrFun (congrFun hcoord_i hp) hp
      rw [show ((algebraMap K (∀ j, Matrix (Fin (blk j)) (Fin (blk j)) (D j))) c₀) i
          = algebraMap K (Matrix (Fin (blk i)) (Fin (blk i)) (D i)) c₀ from rfl] at hentry
      rw [Matrix.algebraMap_matrix_apply, if_pos rfl] at hentry
      rw [← ha₀, ← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq] at hentry
      exact hentry
    have ha₀_notmem : (a₀ : D i) ∉ (algebraMap K (D i)).range := by
      rintro ⟨γ, hγ⟩
      have hfix : ∀ (m : GL (Fin d) K), m ∈ M →
          (A : Matrix (Fin d) (Fin d) K) * ((m : Matrix (Fin d) (Fin d) K) - 1) =
            γ • ((m : Matrix (Fin d) (Fin d) K) - 1) := by
        intro m hm
        have hm_mem : m ∈ ((StatedSL (blk i) (D i)).map mS).map θ := hMeq ▸ hm
        obtain ⟨y, hy, hmy⟩ := Subgroup.mem_map.mp hm_mem
        obtain ⟨z, hz, hyz⟩ := Subgroup.mem_map.mp hy
        have hmz : m = θ (mS z) := by rw [← hmy, hyz]
        exact lblk_A_mul_sub_one Φ θ hθΦ A wA hwA i a₀ ha₀ γ hγ.symm ⟨z, hz⟩ m hmz
      obtain ⟨m, hm_ne⟩ : ∃ m : ↥M, m ≠ 1 := by
        by_contra h
        push Not at h
        exact CFSG.LieType.SemisimpleCentralizers.Held.not_isQuasisimple_of_comm
          (fun a b : ↥M => by rw [h a, h b]) hM.2.2
      have hm1 : ((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1 ≠ 0 := by
        intro h0
        apply hm_ne
        apply Subtype.ext
        apply Units.ext
        simpa using sub_eq_zero.mp h0
      obtain ⟨v, hv⟩ := lblk_exists_mulVec_ne_zero hm1
      let u : Fin d → K := (((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v
      have hu : u ≠ 0 := hv
      have hAu : (A : Matrix (Fin d) (Fin d) K) *ᵥ u = γ • u := by
        change (A : Matrix (Fin d) (Fin d) K) *ᵥ
          ((((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v) = γ •
          ((((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v)
        rw [Matrix.mulVec_mulVec, hfix (m : GL (Fin d) K) m.2, Matrix.smul_mulVec]
      let m' : GL (Fin d) K := B * (m : GL (Fin d) K) * B⁻¹
      have hm'_mem : m' ∈ M := hBM (m : GL (Fin d) K) m.2
      have hm'Bmat : ((m' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
          (B : Matrix (Fin d) (Fin d) K) =
          (B : Matrix (Fin d) (Fin d) K) * ((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
        have hgl : m' * B = B * (m : GL (Fin d) K) := by
          change (B * (m : GL (Fin d) K) * B⁻¹) * B = B * (m : GL (Fin d) K)
          group
        have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hgl
        simpa using h
      have hm'v : (((m' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ
          ((B : Matrix (Fin d) (Fin d) K) *ᵥ v) =
          (B : Matrix (Fin d) (Fin d) K) *ᵥ u := by
        change (((m' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ
            ((B : Matrix (Fin d) (Fin d) K) *ᵥ v) =
          (B : Matrix (Fin d) (Fin d) K) *ᵥ
            ((((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) *ᵥ v)
        rw [Matrix.mulVec_mulVec, Matrix.sub_mul, Matrix.one_mul, hm'Bmat]
        rw [show (B : Matrix (Fin d) (Fin d) K) * ((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) -
            (B : Matrix (Fin d) (Fin d) K) =
            (B : Matrix (Fin d) (Fin d) K) *
              (((m : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) - 1) by
          rw [Matrix.mul_sub, Matrix.mul_one]]
        rw [Matrix.mulVec_mulVec]
      have hABu : (A : Matrix (Fin d) (Fin d) K) *ᵥ
          ((B : Matrix (Fin d) (Fin d) K) *ᵥ u) = γ • ((B : Matrix (Fin d) (Fin d) K) *ᵥ u) := by
        rw [← hm'v]
        rw [Matrix.mulVec_mulVec, hfix m' hm'_mem, Matrix.smul_mulVec]
      have hBA' : B * A = Matrix.GeneralLinearGroup.scalar (Fin d) μ * A * B := by
        rw [← hBA]; group
      have hABg : A * B = (Matrix.GeneralLinearGroup.scalar (Fin d) μ)⁻¹ * (B * A) := by
        rw [hBA']; group
      have hABmat : (A : Matrix (Fin d) (Fin d) K) * (B : Matrix (Fin d) (Fin d) K) =
          ((μ : K))⁻¹ • ((B : Matrix (Fin d) (Fin d) K) * (A : Matrix (Fin d) (Fin d) K)) := by
        have h := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hABg
        simp only [Units.val_mul] at h
        rw [h, ← map_inv, Matrix.GeneralLinearGroup.coe_scalar, Units.val_inv_eq_inv_val,
          lblk_scalar_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
      have hμneK' : (μ : K) ≠ 1 := fun h => hμne (Units.ext h)
      exact absurd (lblk_mu_eq_one_of_eigen hABmat hu hAu hABu) hμneK'
    haveI : FiniteDimensional K (D i) :=
      (Module.finite_iff_finite (R := K) (M := D i)).2 inferInstance
    have hμ3K : (μ : K) ^ 3 = 1 := by
      have h := congrArg (fun u : Kˣ => (u : K)) hμ3
      simpa [Units.val_pow_eq_pow_val] using h
    have hμneK : (μ : K) ≠ 1 := fun h => hμne (Units.ext h)
    exact CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsLinField_dvd_finrank
      ⟨(μ : K), hμ3K, hμneK⟩ ha₀_notmem ha₀_pow_mem
  exact ⟨blk i, D i, hFld i, hAlg i, hFin i, eJ, hi, hdim, hmu1, hmune⟩

end CFSG.StandardType

end
