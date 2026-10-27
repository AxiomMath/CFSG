module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSCore
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideKitExcl
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniVac
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsUniLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInUniTransPow
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3LInput
import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Derivation
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTM5
import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.KD76c
import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
import CFSG.LocalAnalysis.GLTheoremA.PartI.I1132
import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Holds
import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDown
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultSporadic
import CFSG.LocalAnalysis.GLTheoremA.S4.YS02Holds
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
import CFSG.RankThree.S4Free.SuzukiEight
import Certificates.Certificate8166

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LieType.SemisimpleCentralizers.Held (heldGU heldSU)

private theorem uni_three_dvd_card_projectiveSL {F : Type} [Field F] [Finite F]
    (h : 3 ∣ Nat.card F - 1) : 3 ∣ Nat.card (projectiveSL 3 F) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3u : 3 ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3u
  have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
  have hωne : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    omega
  have hw3 : (ω : F) ^ 3 = 1 := by simpa using congrArg (fun u : Fˣ => (u : F)) hω3
  have hw1 : (ω : F) ≠ 1 := fun h1 => hωne (Units.ext h1)
  set w : F := (ω : F) with hwdef
  let v : Fin 3 → F := ![1, w, w ^ 2]
  have hdet : (Matrix.diagonal v).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show (1 : F) * w * w ^ 2 = 1
    calc (1 : F) * w * w ^ 2 = w ^ 3 := by ring
      _ = 1 := hw3
  let g : Matrix.SpecialLinearGroup (Fin 3) F := ⟨Matrix.diagonal v, hdet⟩
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    show Matrix.diagonal v ^ 3 = 1
    rw [Matrix.diagonal_pow]
    have hv : v ^ 3 = fun _ => (1 : F) := by
      funext i
      fin_cases i
      · simp [v]
      · simpa [v] using hw3
      · calc (v ^ 3) 2 = (w ^ 3) ^ 2 := by simp [v, ← pow_mul, mul_comm]
          _ = 1 := by rw [hw3, one_pow]
    rw [hv]
    exact Matrix.diagonal_one
  have hgne : proj 3 F g ≠ 1 := by
    intro h1
    rw [proj_eq_one_iff] at h1
    obtain ⟨c, -, hc⟩ := h1
    have e0 := congrFun (congrFun hc 0) 0
    have e1 := congrFun (congrFun hc 1) 1
    have e0' : (1 : F) = (c : F) := by simpa [g, v, Matrix.scalar_apply] using e0
    have e1' : w = (c : F) := by simpa [g, v, Matrix.scalar_apply] using e1
    exact hw1 (e1'.trans e0'.symm)
  have hord : orderOf (proj 3 F g) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, hg3, map_one]
    · exact hgne
  have hdvd : orderOf (proj 3 F g) ∣ Nat.card (projectiveSL 3 F) := orderOf_dvd_natCard _
  rwa [hord] at hdvd

theorem ggNbrLSideUni_dich (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput)
    (lab : LargeEvenLabel) {K : Type} [Field K] [Finite K] {j d : ℕ} (hj : 1 ≤ j)
    (hK : Nat.card K = (2 ^ j) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ j) ≠ (3, 2))
    (hsplit : d = 4 ∨ 3 ∣ 2 ^ j + 1) :
    GGNbrLSideDich lab (LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ j)))
      (LargeEvenGUSet (Fin d) K (2 ^ j))) := by
  classical
  intro φ hφ ψ _ hφ1 hφ3 _ _ J hJ Q hQ4 hQ3 hF α _
  exfalso
  obtain ⟨F, hFfld, hFfin, hFcard, ⟨eJ⟩⟩ := hF
  obtain ⟨A₀, hA₀GU, hA₀⟩ := hφ
  obtain ⟨τ, hτQ, hτ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv hK
  obtain ⟨σ, hσ⟩ := CFSG.LocalAnalysis.GLTheoremA.T171Sh.exists_scalar_mul_mem_heldGU
    hτ hτQ hK A₀ hA₀GU
  set A : GL (Fin d) K := Matrix.GeneralLinearGroup.scalar (Fin d) σ * A₀ with hAdef
  have hAconj : ∀ g : GL (Fin d) K, A * g * A⁻¹ = A₀ * g * A₀⁻¹ := by
    intro g
    have hcen : Matrix.GeneralLinearGroup.scalar (Fin d) σ ∈ Subgroup.center (GL (Fin d) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨σ, rfl⟩
    have hc := Subgroup.mem_center_iff.mp hcen (A₀ * g * A₀⁻¹)
    calc A * g * A⁻¹
        = Matrix.GeneralLinearGroup.scalar (Fin d) σ * (A₀ * g * A₀⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin d) σ)⁻¹ := by rw [hAdef]; group
      _ = A₀ * g * A₀⁻¹ := by rw [← hc]; group
  have hu : ∀ h h' : ↥(StatedSU d (2 ^ j) K),
      (h' : GL (Fin d) K) = A * (h : GL (Fin d) K) * A⁻¹ →
        φ (LargeEvenProjMk (StatedSU d (2 ^ j) K) h) =
          LargeEvenProjMk (StatedSU d (2 ^ j) K) h' := by
    intro h h' hh'
    exact hA₀ h h' (hh'.trans (hAconj h))
  have h3J : 3 ∣ Nat.card ↥J := by
    have h3F : 3 ∣ Nat.card F - 1 := by rw [hFcard]; exact hQ3
    have h1 : 3 ∣ Nat.card (projectiveSL 3 F) := uni_three_dvd_card_projectiveSL h3F
    have h2 : Nat.card (↥J ⧸ Subgroup.center ↥J) = Nat.card (projectiveSL 3 F) :=
      Nat.card_congr eJ.toEquiv
    have h3 : Nat.card (↥J ⧸ Subgroup.center ↥J) ∣ Nat.card ↥J :=
      Subgroup.index_dvd_card (Subgroup.center ↥J)
    rw [← h2] at h1
    exact h1.trans h3
  have hJ3 : GLAPComponent 3 (fixSubgroup φ) J :=
    CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf hJ h3J
  obtain ⟨hA3, M, hMcomp, ⟨eP⟩, -⟩ := CFSG.LocalAnalysis.GLTheoremA.K1419.k1419ClsUniLift
    hτ hτQ hK hd hdq A hσ φ hu hφ3 J hJ3
  have hAns : ∀ c : K, (A : Matrix (Fin d) (Fin d) K) ≠ c • (1 : Matrix (Fin d) (Fin d) K) := by
    intro c hc
    apply hφ1
    have hcomm : ∀ g : GL (Fin d) K, A * g * A⁻¹ = g := by
      intro g
      have hAg : A * g = g * A := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
      rw [hAg, mul_inv_cancel_right]
    refine MulEquiv.ext fun x => ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact hu h h (by rw [hcomm])
  haveI : IsSimpleGroup (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 J) :=
    (CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ3).2
  obtain ⟨eS⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter 3 J hJ.2.2
    inferInstance
  have hF4 : 4 ≤ Nat.card F := by rw [hFcard]; exact hQ4
  exact ggNbrLSideUni_noPSL3 hDet hO hτ hj hτQ hK hd hsplit A hσ hA3 hAns M hMcomp hF4
    (eP.symm.trans (eS.trans eJ))

theorem ggNbrLSideUni_split_twA {ℓ n : ℕ} (h : LargeEvenSplit 3 ⟨.twA, ℓ, n⟩) :
    3 ∣ 2 ^ n + 1 := by
  rcases h with ⟨hu, -⟩ | ⟨-, -, h3⟩ | ⟨h, -⟩ | ⟨hn, -⟩
  · exact absurd hu (by simp [LargeEvenUntwisted])
  · exact h3
  · rcases h with h | h <;> simp at h
  · subst hn
    norm_num

theorem ggNbrLSideUnitaryData_holds (hDet : GGNbrLSideClsDet)
    (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideUnitaryData := by
  refine ⟨fun ℓ n K _ _ hlam hs hK => ?_, fun n K _ _ hlam _ hK => ?_⟩
  · obtain ⟨hn, hℓ, hℓ2⟩ := hlam
    have hn' : 1 ≤ n := hn
    have hℓ' : 2 ≤ ℓ := hℓ
    have hℓ2' : ℓ = 2 → 2 ≤ n := hℓ2
    refine ggNbrLSideUni_dich hDet hO _ hn' hK (by omega) ?_
      (Or.inr (ggNbrLSideUni_split_twA hs))
    intro h
    have h1 : ℓ + 1 = 3 := (Prod.mk.inj h).1
    have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have hn2 : 2 ≤ n := hℓ2' (by omega)
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  · obtain ⟨hn, -⟩ := hlam
    have hn' : 1 ≤ n := hn
    exact ggNbrLSideUni_dich hDet hO _ hn' hK (by norm_num)
      (fun h => absurd (Prod.mk.inj h).1 (by norm_num)) (Or.inl rfl)

end CFSG.StandardType
