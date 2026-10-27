module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSUShort
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValSU4U
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignTwist
import CFSG.Timmesfeld.Transvection.ModelSUFour
import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiPartner
public import CFSG.LocalAnalysis.StandardType.GGSixRCK1416Defs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIShortModel
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpOmegaSix
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpOrthPoint
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIp
import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseS
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUAlignBlock
import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectW

public section

namespace CFSG.StandardType.RCKC1

open scoped Matrix

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.StandardType.LieKnownR2.Short CFSG.StandardType.GGOppRadSpU
  CFSG.SeitzReduction.F4Pilot

theorem card_centralizer_of_mem_suPair_four
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ 1) ^ 2)
    {v w v' w' : Fin 4 → F} (hfr : SUFrame hF 4 v w v' w')
    {g : SU (unitaryInvolution F 2 1) 4}
    (hg : g ∈ suPair (unitaryInvolution F 2 1) 4 v w) (hg1 : g ≠ 1) :
    Nat.card (Subgroup.centralizer ({g} : Set (SU (unitaryInvolution F 2 1) 4))) = 96 := by
  classical
  let σ := unitaryInvolution F 2 1
  let H := suH hF 4
  have hσ : ∀ a : F, σ (σ a) = a := unitaryInvolution_involutive hF
  obtain ⟨c, hgc⟩ := exists_mulVec_of_mem_suPair hF hfr.2.2.1.1 hfr.2.2.1.2.1
    hfr.2.2.2.1 hg
  have hc : c ≠ 0 := by
    intro hc
    apply hg1
    apply natRep_injective (SU σ 4)
    refine LinearMap.ext fun y => ?_
    rw [hgc y, hc]
    simp
  have hσc : σ c ≠ 0 := (map_ne_zero σ).mpr hc
  obtain ⟨hvw', hwv', ⟨hvv, hww, hv'v', hw'w'⟩, ⟨hvw, hvv', hww', hv'w'⟩⟩ := hfr
  change H.β v w' = 1 at hvw'
  change H.β w v' = 1 at hwv'
  change H.β v v = 0 at hvv
  change H.β w w = 0 at hww
  change H.β v' v' = 0 at hv'v'
  change H.β w' w' = 0 at hw'w'
  change H.β v w = 0 at hvw
  change H.β v v' = 0 at hvv'
  change H.β w w' = 0 at hww'
  change H.β v' w' = 0 at hv'w'
  have hHσ : H.σ = σ := rfl
  have hsymm (a b : Fin 4 → F) : H.β b a = σ (H.β a b) :=
    suForm_symm σ hσ a b
  have hwv : H.β w v = 0 := by rw [hsymm, hvw, map_zero]
  have hv'v : H.β v' v = 0 := by rw [hsymm, hvv', map_zero]
  have hw'w : H.β w' w = 0 := by rw [hsymm, hww', map_zero]
  have hw'v' : H.β w' v' = 0 := by rw [hsymm, hv'w', map_zero]
  have hw'v : H.β w' v = 1 := by rw [hsymm, hvw', map_one]
  have hv'w : H.β v' w = 1 := by rw [hsymm, hwv', map_one]
  let b : Fin 4 → Fin 4 → F := ![c • v, w, v', (σ c)⁻¹ • w']
  let P : Matrix (Fin 4) (Fin 4) F := Matrix.of fun i j => b j i
  have hGramEntry (i j : Fin 4) :
      (conjTr σ P * (antidiag 4 : Matrix (Fin 4) (Fin 4) F) * P) i j = H.β (b i) (b j) := by
    rw [conjTr_mul_antidiag_mul_apply]
    change (∑ k, σ (b i k) * b j (Fin.rev k)) = _
    rfl
  have hGram : conjTr σ P * (antidiag 4 : Matrix (Fin 4) (Fin 4) F) * P = antidiag 4 := by
    ext i j
    rw [hGramEntry]
    fin_cases i <;> fin_cases j <;>
      simp [b, H.smul_left, H.smul_right, hvw', hwv', hvv, hww, hv'v', hw'w', hvw,
        hvv', hww', hv'w', hwv, hv'v, hw'w, hw'v', hw'v, hv'w, hσc, hc, hHσ, hσ, antidiag]
  have hdet : P.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hGram
    simp only [Matrix.det_mul, hz, mul_zero] at h
    exact det_antidiag_ne_zero 4 h.symm
  let A : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hdet
  have hA : conjTr σ (A : Matrix (Fin 4) (Fin 4) F) * antidiag 4 *
      (A : Matrix (Fin 4) (Fin 4) F) = antidiag 4 := hGram
  have hAA : (A : Matrix (Fin 4) (Fin 4) F) *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    exact congrArg Units.val (mul_inv_cancel A)
  have hA' : conjTr σ ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * antidiag 4 *
      ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = antidiag 4 := by
    calc
      _ = conjTr σ ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (conjTr σ (A : Matrix (Fin 4) (Fin 4) F) * antidiag 4 *
            (A : Matrix (Fin 4) (Fin 4) F)) *
          ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by rw [hA]
      _ = (conjTr σ ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          conjTr σ (A : Matrix (Fin 4) (Fin 4) F)) * antidiag 4 *
          ((A : Matrix (Fin 4) (Fin 4) F) *
            ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
        simp only [Matrix.mul_assoc]
      _ = antidiag 4 := by
        rw [← conjTr_mul, hAA, conjTr_one, Matrix.one_mul, Matrix.mul_one]
  letI : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* CFSG.GH74.Uniqueness.SU.SU5.F4c :=
    FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, hF, CFSG.GH74.Uniqueness.SU.SU5.F4c.card_eq]
      norm_num)
  have heF (a : F) : eF (σ a) = f4Frob (eF a) := by
    rw [unitaryInvolution_apply, f4Frob_apply, pow_one, sq, map_mul]
  let e := suCongr eF heF 4
  let r₀ := e.symm su4U
  have hr₀ : ((r₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1] := by
    apply eF.mapMatrix.injective
    have h := congrArg (fun a : SU f4Frob 4 =>
      ((a : GL (Fin 4) CFSG.GH74.Uniqueness.SU.SU5.F4c) : M4c)) (e.apply_symm_apply su4U)
    change eF.mapMatrix _ = su4UM at h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [su4UM]
  have hgvec (y : Fin 4 → F) :
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ y =
        y + (c * H.β w y) • v + (σ c * H.β v y) • w := hgc y
  have hg0 : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ (c • v) = c • v := by
    rw [hgvec, H.smul_right, H.smul_right, hwv, hvv]
    simp
  have hg1' : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ w = w := by
    rw [hgvec, hww, hvw]
    simp
  have hg2 : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ v' = v' + c • v := by
    rw [hgvec, hwv', hvv']
    simp
  have hg3 : ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ ((σ c)⁻¹ • w') =
      (σ c)⁻¹ • w' + w := by
    rw [hgvec, H.smul_right, H.smul_right, hww', hvw']
    simp [hσc]
  have hAg : A * (r₀ : GL (Fin 4) F) = (g : GL (Fin 4) F) * A := by
    apply Units.ext
    change P * ((r₀ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P
    rw [hr₀]
    ext i j
    have hcol : (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * P) i j =
        (((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *ᵥ b j) i := rfl
    rw [hcol]
    fin_cases j <;>
      simp [P, b, Matrix.mul_apply, Fin.sum_univ_four, hg0, hg1', hg2, hg3, add_comm]
  have hconj : CFSG.SeitzReduction.SymplecticPilot.ctuaConjAut σ A hA hA' r₀ = g := by
    apply Subtype.ext
    change A * (r₀ : GL (Fin 4) F) * A⁻¹ = (g : GL (Fin 4) F)
    rw [hAg, mul_assoc, mul_inv_cancel, mul_one]
  rw [← hconj, card_centralizer_mulEquiv
      (CFSG.SeitzReduction.SymplecticPilot.ctuaConjAut σ A hA hA') r₀]
  rw [← card_centralizer_mulEquiv e r₀]
  change Nat.card (Subgroup.centralizer ({e (e.symm su4U)} : Set (SU f4Frob 4))) = 96
  rw [e.apply_symm_apply]
  exact su4_card_centralizer_u

section Certificates


open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType

theorem card_centralizer_of_short_root_via_unitary_four
    {Jb : Type} [Group Jb] [Finite Jb]
    {β : Fin (ggU .PSU 4 1).D.rank → ℤ} {R : Subgroup Jb}
    (hβ : β ∈ (ggU .PSU 4 1).D.roots)
    (hs : ¬ GGLongRoot (ggU .PSU 4 1).D β)
    (h2β : 2 • β ∉ (ggU .PSU 4 1).D.roots)
    (hvia : GGRootVia (ggU .PSU 4 1) ⊤ R β)
    {rb : Jb ⧸ Subgroup.center Jb}
    (hrb : rb ∈ R.map (QuotientGroup.mk' (Subgroup.center Jb))) (hrb1 : rb ≠ 1) :
    Nat.card (Subgroup.centralizer ({rb} : Set (Jb ⧸ Subgroup.center Jb))) = 96 := by
  have hU : ggU .PSU 4 1 =
      ⟨SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4,
        Unitary.rootDatum (card_galoisField_two_mul 2 1 (by decide)) 4⟩ := by
    simp only [ggU, lieUniversal, show 1 ≤ (1 : ℕ) from le_refl 1, ↓reduceDIte]
  revert β
  rw [hU]
  intro β hβ hs h2β hvia
  obtain ⟨φ, hφrange, hφker, u, hR⟩ := hvia
  have hZ : Subgroup.center
      (SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4) = ⊥ :=
    CFSG.Timmesfeld.Transvection.ModelRank.center_SU_four_eq_bot
      (unitaryInvolution_involutive (card_galoisField_two_mul 2 1 (by decide)))
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact le_bot_iff.mp (hφker.trans (le_of_eq hZ))
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
  let eJ := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hZJ : Subgroup.center Jb = ⊥ := by
    rw [← Subgroup.map_center_eq eJ, hZ, Subgroup.map_bot]
  let eQ : Jb ≃* Jb ⧸ Subgroup.center Jb :=
    (QuotientGroup.quotientMulEquivOfEq hZJ).trans QuotientGroup.quotientBot |>.symm
  let e := eJ.trans eQ
  have he (x : SU (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4) :
      e x = QuotientGroup.mk' (Subgroup.center Jb) (φ x) := rfl
  rw [hR] at hrb
  obtain ⟨j, ⟨y, hy, rfl⟩, hyr⟩ := Subgroup.mem_map.mp hrb
  have hy1 : y ≠ 1 := by
    intro hy1
    apply hrb1
    rw [← hyr, hy1, map_one, map_one]
  obtain ⟨v, w, v', w', hfr, hPair, -⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_unitPairGroup_eq_conj_rootGroup_SU
      (card_galoisField_two_mul 2 1 (by decide)) 4 hβ hs h2β u
  have hyPair : y ∈ suPair (unitaryInvolution (GaloisField 2 (2 * 1)) 2 1) 4 v w := by
    rw [← hPair]
    exact hy
  have hcard := card_centralizer_of_mem_suPair_four
    (card_galoisField_two_mul 2 1 (by decide)) hfr hyPair hy1
  rw [← hyr, ← he, card_centralizer_mulEquiv e]
  exact hcard

end Certificates

section RecognitionCertificates


open CFSG.Blueprint

theorem cent96At_of_shortAt_psu_four
    {X : Type} [Group X] [Finite X] {J V : Subgroup X} {r : X}
    (hOddJ : Odd (Nat.card (Subgroup.center ↥J))) (hFour : FourAt J V r)
    (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1)
    (hShort : ShortAt J r) : Cent96At J r := by
  obtain ⟨rJ, hrJ, hPos⟩ := hShort
  have hrJ2 : rJ * rJ = 1 := by
    apply Subtype.ext
    change (rJ : X) * (rJ : X) = 1
    rw [hrJ]
    simpa [pow_two] using hFour.2.2.1.2 r hFour.1
  have hrb1 : QuotientGroup.mk' (Subgroup.center ↥J) rJ ≠ 1 := by
    intro hrb1
    have hrJ1 : rJ = 1 := eq_of_mk_eq_of_mul_self_eq_one hOddJ hrJ2
      (show (1 : J) * 1 = 1 by simp) (by simpa using hrb1)
    apply hFour.2.2.2.2.1
    rw [← hrJ, hrJ1]
    rfl
  refine ⟨rJ, hrJ, ?_⟩
  obtain ⟨β, R, hβ, hs, h2β, hvia, hrb⟩ :=
    exists_shortRoot_psuFour_two hJ hPos hrb1
  exact card_centralizer_of_short_root_via_unitary_four hβ hs h2β hvia hrb hrb1

theorem k2At_of_omegaSixEmbed_shortAt_psu_four
    {X : Type} [Group X] [Finite X] {K J V : Subgroup X} {r : X}
    (hOddJ : Odd (Nat.card (Subgroup.center ↥J)))
    (hOddK : Odd (Nat.card (Subgroup.center ↥K)))
    (hFour : FourAt J V r) (hCore : CoreCommAt J V r)
    (hJ : LieModel (↥J ⧸ Subgroup.center ↥J) .PSU 4 2 1)
    (hShort : ShortAt J r) (hEmbed : OmegaSixEmbed K J) : K2At K V r := by
  have hCent := cent96At_of_shortAt_psu_four hOddJ hFour hJ hShort
  exact rckOrthPointK2 X K V r hOddK
    (rckIIpOmegaSixBridge X K J V r hOddJ hOddK hFour hCore hCent hEmbed)

end RecognitionCertificates

end CFSG.StandardType.RCKC1
