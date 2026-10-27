module

public import Certificates.Data.Co2CentDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2ThreeDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestCover
public import Certificates.Kernel.Co2Cent.CaseAGlue
public import Certificates.Kernel.Co2Cent.CaseBL
public import Certificates.Kernel.Co2Cent.Fusion
public import Certificates.Kernel.Co2Cent.FusBind
public import Certificates.Kernel.Co2Three.Glue
public import Certificates.Kernel.Co2Pump.Facts
public import Certificates.Kernel.Misc.Perm.C2G
public import CFSG.Certificates.Kernel.Spor.RawSiftMem
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.OuterTrivial
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCo2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KD.Co2Cent Subgroup CFSG.Sporadic.Co2Cert CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.Co2Cent
open CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest (evalW)
open CFSG.HardMathSupport.Dickson.I271.U42Presentation (u42Words)

theorem fdFacts : (∀ i < 4, CertificateChecks.KernelMisc.Co2K.bindK (getS DG i)
      (CertificateChecks.KernelCo2Pump.DD i)
      (CertificateChecks.KernelMisc.Co2K.mmK (CertificateChecks.KernelCo2Pump.DD i)
        (CertificateChecks.KernelCo2Pump.DD i)) = true) ∧
    xA = getS DG 1 ∧ xB = getS DG 0 := by
  have h := ch17351_fd
  simp only [bAnd_iff] at h
  exact ⟨allN_spec h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem prepDG {i : ℕ} (hi : i < 4) : PRep 2300 12 (getS DG i) (dGenP i) := by
  obtain ⟨-, e, -⟩ := CertificateChecks.KernelMisc.Co2K.bind_facts
    (a := unpack 2300 12 (getS DG i)) rfl (fdFacts.1 i hi)
  rw [← (CertificateChecks.KernelCo2Pump.dG hi).1] at e
  refine prep_of_rep ?_
  rw [e]
  exact CertificateChecks.KernelCo2Three.krep_dGen hi

theorem dEltP_eq {k : ℕ} (hk : k < 81) : dEltP k = ((dgtWord k).map dGenP).prod := by
  rw [CertificateChecks.KernelCo2Three.kdElt_eq hk, dgtWord_prod]
  simp only [digit3, Nat.div_one, pow_zero, pow_one, Nat.reducePow]

theorem co2XA_eq' : co2XA = dGenP 1 := by
  change dEltP 3 = dGenP 1
  rw [CertificateChecks.KernelCo2Three.kdElt_eq (by norm_num)]
  norm_num [digit3]

theorem co2XB_eq' : co2XB = dGenP 0 := by
  change dEltP 1 = dGenP 0
  rw [CertificateChecks.KernelCo2Three.kdElt_eq (by norm_num)]
  norm_num [digit3]

theorem prepXA : PRep 2300 12 xA co2XA := by
  rw [co2XA_eq', fdFacts.2.1]
  exact prepDG (by norm_num)

theorem prepXB : PRep 2300 12 xB co2XB := by
  rw [co2XB_eq', fdFacts.2.2]
  exact prepDG (by norm_num)

theorem rA_eq {j : ℕ} (hj : j < 4) : permOfArr 2300 (co2RGens ())[j]! = rA j := by
  have e : (co2RGens ())[j]! = unpack 2300 12 (RGp j) := by
    rw [co2RGens, getElem!_pos _ j (by simp; omega), Array.getElem_ofFn]
    exact CertificateChecks.KernelCo2I301.co2Arr_eq (33 + j) (by omega)
  rw [e]
  exact permOfArr_eq_of_rep (rep_unpack (prepRG hj))

theorem RA_eq : closure (permsA 2300 (co2RGens ())) = CertificateChecks.KernelCo2Cent.RA := by
  rw [CertificateChecks.KernelCo2Cent.RA]
  congr 1
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk4 : k < 4 := by simpa [co2RGens] using hk
    exact ⟨⟨k, hk4⟩, (rA_eq hk4).symm⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    exact ⟨k, by simpa [co2RGens] using hk, rA_eq hk⟩

theorem SL_eq {j : ℕ} (hj : j < 6) : getS SL j = CertificateChecks.KernelCo2I301.CH.F (37 + j) := by
  have h := ch17351_oAB
  simp only [bAnd_iff] at h
  exact Nat.eq_of_beq_eq_true (allN_spec h.2.2.2.2 j hj)

theorem uvGen_eq : uvGen = uvL := by
  funext i
  have hi := i.2
  have e : (co2LGens ())[i.val]! = co2Arr (37 + i.val) := by
    rw [co2LGens, getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
  rw [uvGen, e, CertificateChecks.KernelCo2I301.co2Arr_eq _ (by omega), uvL, sL, SL_eq (by omega)]

theorem Lsub_eq_Lg : Lsub = Lg := by
  rw [Lsub, Lg, uvGen_eq]

theorem LArrs_eq : co2LArrs () = SLarr := by
  refine Array.ext (by simp [co2LArrs, SLarr]) fun i h1 _ => ?_
  have hi : i < 6 := by simpa [co2LArrs] using h1
  simp only [co2LArrs, SLarr, Array.getElem_ofFn]
  rw [SL_eq hi, CertificateChecks.KernelCo2I301.co2Arr_eq _ (by omega)]

theorem LBase_get : ∀ t < 3, co2LBase[t]! = pg 12 (mask 12) (packB 12 BL) t := by
  decide +kernel

theorem LBase_eq : co2LBase = BLarr := by
  refine Array.ext (by simp [co2LBase, BLarr]) fun t h1 _ => ?_
  have ht : t < 3 := by simpa [co2LBase] using h1
  simp only [BLarr, Array.getElem_ofFn]
  rw [← getElem!_pos co2LBase t h1]
  exact LBase_get t ht

theorem mem_Lsub_of_sift {t : Array ℕ} {G : Equiv.Perm (Fin 2300)} (hG : Rep 2300 t G)
    (h : siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0 t = true) : G ∈ Lsub := by
  obtain ⟨W, hd⟩ := hdL
  rw [LArrs_eq, LBase_eq] at h
  rw [Lsub_eq_Lg, ← genL_eq]
  exact mem_Gen_of_sift hd hG h

theorem hdD :
    ∀ i < 4, PRep 2300 12 (getS DG i) (dGenP i) := fun _ hi => prepDG hi

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Sporadic.Co2Cert CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.Co2Cent
  CFSG.HardMathSupport.Dickson.I271.U42Presentation in
theorem kproof :

    (∀ k, 0 < k → k < 81 → ∃ h ∈ co2P, ∃ c : Equiv.Perm (Fin 2300), (c = co2XA ∨ c = co2XB) ∧
      ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP k * h⁻¹ = c ^ e) ∧
    (∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP 5 * h⁻¹ = co2XA ^ e) ∧
    (∃ h ∈ co2P, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ h * dEltP 4 * h⁻¹ = co2XB ^ e) ∧
    (co2XA ^ 3 = 1 ∧ co2XA ≠ 1 ∧ co2XA ∈ co2P ∧
      Nat.card (closure (permsA 2300 (co2RGens ()))) = 243 ∧
      closure (permsA 2300 (co2RGens ())) ≤ centralizer {co2XA} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XA} ⊓ co2P, ∀ r ∈ closure (permsA 2300 (co2RGens ())),
        g * r * g⁻¹ ∈ closure (permsA 2300 (co2RGens ()))) ∧
      centralizer (closure (permsA 2300 (co2RGens ())) : Set (Equiv.Perm (Fin 2300))) ⊓
        (centralizer {co2XA} ⊓ co2P) ≤ closure (permsA 2300 (co2RGens ()))) ∧
    (co2XB ^ 3 = 1 ∧ co2XB ≠ 1 ∧ co2XB ∈ co2P ∧ Nat.card Lsub = 25920 ∧
      Lsub ≤ centralizer {co2XB} ⊓ co2P ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, ∀ l ∈ Lsub, g * l * g⁻¹ ∈ Lsub) ∧
      (∀ g ∈ centralizer {co2XB} ⊓ co2P, (∀ l ∈ Lsub, l * g = g * l) → g ^ 3 = 1) ∧
      ∀ w ∈ u42Words,
        CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest.evalW uvGen w = 1) ∧
    ∀ (t : Array ℕ) (G : Equiv.Perm (Fin 2300)), Rep 2300 t G →
      siftA 2300 (rawLevels 2300 (co2LArrs ()) co2LBase) co2LBase 0 t = true → G ∈ Lsub := by
  refine ⟨fun k hk0 hk => ?_, ?_, ?_, ?_, ?_, fun t G hG h => mem_Lsub_of_sift hG h⟩
  · obtain ⟨h, hh, c, hc, e, he, hcon, -, -⟩ := fusion hdD prepXA prepXB hk0 hk
    rw [← dEltP_eq hk] at hcon
    exact ⟨h, hh, c, hc, e, he, hcon⟩
  · obtain ⟨h, hh, e, he, hcon⟩ := fusion_d5 hdD prepXA prepXB
    rw [← dEltP_eq (by norm_num)] at hcon
    exact ⟨h, hh, e, he, hcon⟩
  · obtain ⟨h, hh, e, he, hcon⟩ := fusion_d4 hdD prepXA prepXB
    rw [← dEltP_eq (by norm_num)] at hcon
    exact ⟨h, hh, e, he, hcon⟩
  · obtain ⟨h3, h1, hc, hle, hn, hcen⟩ := caseA prepXA
    have hP : co2XA ∈ co2P := by
      rw [co2XA_eq']
      exact (CertificateChecks.KernelCo2Three.kdGen_facts 1 (by norm_num)).2.1
    rw [RA_eq]
    exact ⟨h3, h1, hP, hc, hle, hn, hcen⟩
  · obtain ⟨h3, h1, hP, hc, hle, hn, hcen, hrel⟩ := caseB prepXB
    rw [Lsub_eq_Lg, uvGen_eq]
    exact ⟨h3, h1, hP, hc, hle, hn, hcen, hrel⟩

end CertificateChecks.KernelCo2Cent

end
