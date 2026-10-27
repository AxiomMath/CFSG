module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoord
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.WittTransport
import CFSG.HardMathSupport.Timmesfeld.Torality.PeelBlockN
import CFSG.LieType.Chevalley.E7Three.HeisenbergPair
import CFSG.HardMathSupport.GuralnickMalle.CyclicTwo
import CFSG.HardMathSupport.GuralnickMalle.FGeneral
import CFSG.HardMathSupport.GuralnickMalle.Prop24General

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.StandardType.RCKK1IIISU

open CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar (wittMat suToStated coe_suToStated)
open CFSG.SeitzReduction.F4Pilot (suCongr coe_suCongr)
open CFSG.LieType.Chevalley.E7Three.HeisenbergPair (exists_sl_conj_eq)

variable {L : Type} [Field L] {ν : ℕ}

@[expose] noncomputable def suCornerSL (hν : 4 ≤ ν) (x y : L) : SL(ν, L) :=
  SpecialLinearGroup.transvection (i := sI0 hν) (j := Fin.rev (sI1 hν))
      (by simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega) x *
    SpecialLinearGroup.transvection (i := sI1 hν) (j := Fin.rev (sI0 hν))
      (by simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega) y

theorem coe_suCornerSL (hν : 4 ≤ ν) (x y : L) :
    ((suCornerSL hν x y : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      1 + single (sI0 hν) (Fin.rev (sI1 hν)) x + single (sI1 hν) (Fin.rev (sI0 hν)) y := by
  rw [suCornerSL, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.single_mul_single_of_ne _ _ _ _ (by
    simp [sI1, Fin.ext_iff, Fin.val_rev]; omega), add_zero]

theorem exists_conj_suCornerSL [IsAlgClosed L] (hν : 4 ≤ ν) (c₀ c₁ : Lˣ) :
    ∃ D : SL(ν, L), ∀ x y : L,
      D * suCornerSL hν x y * D⁻¹ = suCornerSL hν ((c₀ : L) * x) ((c₁ : L) * y) := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (c₀ : L) (n := 2) (by norm_num)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c₁ : L) (n := 2) (by norm_num)
  let u : Lˣ := Units.mk0 t (by rintro rfl; exact c₀.ne_zero (by simpa using ht.symm))
  let v : Lˣ := Units.mk0 s (by rintro rfl; exact c₁.ne_zero (by simpa using hs.symm))
  let a : Fin ν := sI0 hν
  let b : Fin ν := Fin.rev (sI1 hν)
  let c : Fin ν := sI1 hν
  let e : Fin ν := Fin.rev (sI0 hν)
  have hab : a ≠ b := by simp [a, b, sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have hac : a ≠ c := by simp [a, c, sI0, sI1, Fin.ext_iff]
  have hae : a ≠ e := by simp [a, e, sI0, Fin.ext_iff, Fin.val_rev]; omega
  have hbc : b ≠ c := by simp [b, c, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have hbe : b ≠ e := by simp [b, e, sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  have hce : c ≠ e := by simp [c, e, sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega
  let d : Fin ν → Lˣ := fun i =>
    (if i = a then u else 1) * (if i = b then u⁻¹ else 1) *
      (if i = c then v else 1) * (if i = e then v⁻¹ else 1)
  have hdprod : (∏ i, d i) = 1 := by
    change (∏ i, (if i = a then u else 1) * (if i = b then u⁻¹ else 1) *
      (if i = c then v else 1) * (if i = e then v⁻¹ else 1)) = 1
    simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    group
  have hdprod' : (∏ i, (((d i)⁻¹ : Lˣ) : L)) = 1 := by
    rw [← Units.coe_prod, Finset.prod_inv_distrib, hdprod]
    simp
  have hdprod1 : (∏ i, (((1 : Lˣ) * d i : Lˣ) : L)) = 1 := by
    simpa [one_mul] using congrArg (fun w : Lˣ => (w : L)) hdprod
  have hdprod1' : (∏ i, ((((1 : Lˣ) * d i)⁻¹ : Lˣ) : L)) = 1 := by
    simpa [one_mul] using hdprod'
  refine ⟨diagSLn (fun i => (1 : Lˣ) * d i) hdprod1, fun x y => ?_⟩
  rw [diagSLn_conj d 1 hdprod1 hdprod1']
  have h1 : (d a : L) * x * ((d b)⁻¹ : Lˣ) = (c₀ : L) * x := by
    rw [show d a = u from by simp [d, hab, hac, hae],
      show d b = u⁻¹ from by simp [d, hab.symm, hbc, hbe], inv_inv, ← ht]
    change t * x * t = t ^ 2 * x
    ring
  have h2 : (d c : L) * y * ((d e)⁻¹ : Lˣ) = (c₁ : L) * y := by
    rw [show d c = v from by simp [d, hac.symm, hbc.symm, hce],
      show d e = v⁻¹ from by simp [d, hae.symm, hbe.symm, hce.symm], inv_inv, ← hs]
    change s * y * s = s ^ 2 * y
    ring
  rw [suCornerSL, ← conjDiagnHom_apply, map_mul, conjDiagnHom_apply, conjDiagnHom_apply,
    conjDiagn_transvection, conjDiagn_transvection, h1, h2]
  rfl

theorem exists_statedSU_mulEquiv_SUG [IsAlgClosed L] {K : Subfield L} (hK : Nat.card K = 4) :
    ∃ (e : StatedSU ν 2 K ≃* SUG ν) (κ : SUF →+* L) (P : SL(ν, L)), ∀ s,
      ((statedSUToSL K ν 2 s : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
        (P : Matrix (Fin ν) (Fin ν) L) *
          (((e s : SUG ν) : GL (Fin ν) SUF) : Matrix (Fin ν) (Fin ν) SUF).map κ *
            ((P⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) := by
  classical
  have hFinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let hFintK : Fintype K := Fintype.ofFinite K
  let hFintSUF : Fintype SUF := Fintype.ofFinite SUF
  have hcardK : Fintype.card K = 2 ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
  have hCharK : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) hcardK
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hcardF : Fintype.card K = Fintype.card SUF := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK,
      GaloisField.card (p := 2) (n := 2 * 1) (by norm_num)]
    norm_num
  let φ : K ≃+* SUF := FiniteField.ringEquivOfCardEq hcardF
  have hφ : ∀ c : K, φ (unitaryInvolution K 2 1 c) = unitaryInvolution SUF 2 1 (φ c) := by
    intro c
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply,
      CFSG.LieType.BorelTits.unitaryInvolution_apply, map_pow]
  let κ : SUF →+* L := K.subtype.comp φ.symm.toRingHom
  let W : GL (Fin ν) K := wittMat (F := K) (p := 2) (f := 1) hK' ν
  let PL : GL (Fin ν) L := GeneralLinearGroup.map K.subtype W
  let e : StatedSU ν 2 K ≃* SUG ν :=
    (suToStated (F := K) (p := 2) (f := 1) hK' ν).symm.trans
      (suCongr (σ := unitaryInvolution K 2 1) (σ' := unitaryInvolution SUF 2 1) φ hφ ν)
  have hWinv : (((W⁻¹ : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map K.subtype) =
      (PL : Matrix (Fin ν) (Fin ν) L)⁻¹ := by
    rw [show ((W⁻¹ : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map K.subtype =
        ((GeneralLinearGroup.map K.subtype W⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) from
        rfl, GeneralLinearGroup.map_inv, Matrix.coe_units_inv]
  obtain ⟨P, hP⟩ := exists_sl_conj_eq (Q := (PL : Matrix (Fin ν) (Fin ν) L)⁻¹)
    (by simpa using Matrix.isUnits_det_units (PL⁻¹ : GL (Fin ν) L))
  refine ⟨e, κ, P, fun s => ?_⟩
  let A : SU (unitaryInvolution K 2 1) ν := (suToStated (F := K) (p := 2) (f := 1) hK' ν).symm s
  let X' : Matrix (Fin ν) (Fin ν) L :=
    ((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map K.subtype
  have hX : ((((e s : SUG ν) : GL (Fin ν) SUF) : Matrix (Fin ν) (Fin ν) SUF).map κ) = X' := by
    rw [show e s = suCongr (σ := unitaryInvolution K 2 1) (σ' := unitaryInvolution SUF 2 1)
      φ hφ ν A from rfl, coe_suCongr]
    ext i j; simp [X', κ]
  have hXdet : X'.det = 1 := by
    simpa [X', A.2.1] using
      (RingHom.map_det K.subtype ((A : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K)).symm
  have hsmap : ((s : GL (Fin ν) K) : Matrix (Fin ν) (Fin ν) K).map K.subtype =
      (PL : Matrix (Fin ν) (Fin ν) L) * X' * (PL : Matrix (Fin ν) (Fin ν) L)⁻¹ := by
    have h := congrArg (fun g : GL (Fin ν) K => (g : Matrix (Fin ν) (Fin ν) K))
      (coe_suToStated (F := K) (p := 2) (f := 1) hK' ν A)
    rw [show suToStated hK' ν A = s from by simp [A]] at h
    rw [h, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul,
      show ((W : Matrix (Fin ν) (Fin ν) K).map K.subtype) = (PL : Matrix (Fin ν) (Fin ν) L) from
        rfl, hWinv]
  have hPX : (P : Matrix (Fin ν) (Fin ν) L) * X' * ((P⁻¹ : SL(ν, L)) : Matrix (Fin ν) (Fin ν) L) =
      (PL : Matrix (Fin ν) (Fin ν) L) * X' * (PL : Matrix (Fin ν) (Fin ν) L)⁻¹ := by
    have h := hP ⟨X', hXdet⟩
    rwa [Matrix.nonsing_inv_nonsing_inv (A := (PL : Matrix (Fin ν) (Fin ν) L))
      (Matrix.isUnits_det_units PL)] at h
  rw [hX, coe_statedSUToSL]
  exact hsmap.trans hPX.symm

end CFSG.StandardType.RCKK1IIISU

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.IsSLFrame

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.RCKK1IIISU

variable {τ : Tag} {L : Type}
  [Field L] {ν : ℕ} {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem exists_map_suCornerSL (hψ : IsSLFrame ψ σ) (hν : 4 ≤ ν) :
    ∃ ε₀ ε₁ : Lˣ, ∀ x y : L, ψ (suCornerSL hν x y) =
      pinnedX τ L (σ (sI0 hν) (Fin.rev (sI1 hν))) ((ε₀ : L) * x) *
        pinnedX τ L (σ (sI1 hν) (Fin.rev (sI0 hν))) ((ε₁ : L) * y) := by
  obtain ⟨ε₀, h₀⟩ := hψ.transv (sI0 hν) (Fin.rev (sI1 hν))
    (by simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega)
  obtain ⟨ε₁, h₁⟩ := hψ.transv (sI1 hν) (Fin.rev (sI0 hν))
    (by simp [sI0, sI1, Fin.ext_iff, Fin.val_rev]; omega)
  exact ⟨ε₀, ε₁, fun x y => by rw [suCornerSL, map_mul, h₀, h₁]⟩

end CFSG.HardMathSupport.Timmesfeld.CrossChar.IsSLFrame

end
