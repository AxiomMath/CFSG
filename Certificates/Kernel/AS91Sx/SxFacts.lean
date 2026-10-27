module

public import Certificates.Kernel.AS91Sx.SxX
public import Certificates.Kernel.AS91Sx.SxY
public import Certificates.Kernel.AS91Sx.SxCls
public import CFSG.Certificates.Kernel.SporSch.MathieuClsSound
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Sporadic.SmallOddCore.CentSpec
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS91Sx.Sx664OC

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.Quasithin.H13.AS91.M24G
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem bindA : bindListK 24 5 (Sx664Q.S 0) tA = true := by quickRfl

theorem bindB : bindListK 24 5 (Sx664Q.S 1) tB = true := by quickRfl

theorem cA : canonK 24 5 (mask 5) (24 * 5) (Sx664Q.S 0) = true := by quickRfl

theorem cB : canonK 24 5 (mask 5) (24 * 5) (Sx664Q.S 1) = true := by quickRfl

theorem cOne : canonK 24 5 (mask 5) (24 * 5) One = true := by quickRfl

theorem ordA : ordIs 24 5 (mask 5) (pidn 24 5) (Sx664Q.S 0) (5 - 1) = true := by quickRfl

theorem ordB : ordIs 24 5 (mask 5) (pidn 24 5) (Sx664Q.S 1) (4 - 1) = true := by quickRfl

theorem wordsAB : wordOrdK 24 5 (mask 5) (pidn 24 5) 5 4 sxAutWords (Sx664Q.S 0) (Sx664Q.S 1) =
    true := by quickRfl

theorem repCK : Nat.beq (Sx664CK.getD 0 clsD0).R R0 = true := by quickRfl

theorem szOK' : szOK 24 5 = true := by quickRfl

theorem tA_eq : tA = imageList sxAT := by
  rw [sxAT_eq]
  decide

theorem tB_eq : tB = imageList sxBT := by
  rw [sxBT_eq]
  decide

theorem img_of_bind {g : Equiv.Perm (Fin 24)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 24 5 P l = true) : imageList g = (unpack 24 5 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgA : imageList sxAT = (unpack 24 5 (Sx664Q.S 0)).toList := img_of_bind tA_eq bindA

theorem imgB : imageList sxBT = (unpack 24 5 (Sx664Q.S 1)).toList := img_of_bind tB_eq bindB

theorem imgOne : imageList (1 : Equiv.Perm (Fin 24)) = (unpack 24 5 One).toList := by
  decide

theorem elems_of_blocks {f : Nat → Bool} {c nb : Nat} (hc : c ≤ nb * 256)
    (h : ∀ s < nb, allBlk (s * 256) f 256 = true) : ∀ k < c, f k = true := by
  intro k hk
  have hs : k / 256 < nb := by omega
  have := allBlk_spec (h (k / 256) hs) (k % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (k / 256 * 256) (k % 256) = k := by
    change k / 256 * 256 + k % 256 = k
    omega
  rwa [e] at this

theorem clsOK5 : ClsOK 24 5 tA tB 5 40000 Sx664CK := by
  intro j hj
  have hj1 : j < 1 := by simpa [Sx664CK] using hj
  interval_cases j
  exact ⟨Sx664CK.h0, elems_of_blocks (by decide) Sx664CK.hb0, fun i hi => absurd hi (by omega)⟩

theorem chainQ : ChainK 24 5 [sxAT, sxBT] sxChainWords sxBase
    Sx664Q.S Sx664Q.SI Sx664Q.LR Sx664Q.TR Sx664Q.TRI 10 Sx664Q.BP 2 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, Sx664Q.head, Sx664Q.hl,
    by norm_num, Sx664Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · exact imgA
  · exact imgB

def wv (l : List Bool) : Equiv.Perm (Fin 24) := (l.map fun c => if c then sxB else sxA).prod

def wq : Fin 24 → List Bool :=
  ![[false, false], [true, false, false, false, true], [false, true, false], [true],
    [false, true, true], [false, true, false, false], [false, false, false, true, false],
    [false, false, true], [true, true, true], [true, false, false, true, false],
    [true, true, false, false], [true, false, true], [true, false, false],
    [false, false, true, false], [true, true], [false, true], [false, false, false, false, true],
    [false, true, true, false, true], [false], [true, false], [false, false, false, true],
    [true, true, false, true], [], [true, true, true, false, false]]

theorem wv_fix : ∀ y : Fin 24, wv [false, false, true, true] y = y → y = 22 := by
  decide +kernel

theorem wv_wq : ∀ q : Fin 24, wv (wq q) 22 = q := by
  decide +kernel

theorem center_eq_one {x : Equiv.Perm (Fin 24)} (ha : Commute x sxA) (hb : Commute x sxB) :
    x = 1 := by
  have hw : ∀ l : List Bool, Commute x (wv l) := fun l => by
    refine Commute.list_prod_right _ _ fun y hy => ?_
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hy
    cases c
    · exact ha
    · exact hb
  have h22 : x 22 = 22 := by
    apply wv_fix
    rw [← Equiv.Perm.mul_apply, ← (hw _).eq, Equiv.Perm.mul_apply]
    exact congrArg x (by decide +kernel)
  ext q
  rw [← wv_wq q, ← Equiv.Perm.mul_apply, (hw _).eq, Equiv.Perm.mul_apply, h22]
  rfl

theorem centerOK : sxCenterOK = true := by
  simp only [sxCenterOK, List.all_eq_true]
  intro T hT
  obtain ⟨x, -, hx⟩ := exists_mem_of_forall₂_right (forall₂_allTables (by norm_num) sxCert) T hT
  rw [commT_eq hx (rep_toTable (by norm_num) sxAT), commT_eq hx (rep_toTable (by norm_num) sxBT)]
  by_cases h1 : x * sxAT = sxAT * x
  · by_cases h2 : x * sxBT = sxBT * x
    · rw [sxAT_eq] at h1
      rw [sxBT_eq] at h2
      have := (CFSG.Sporadic.SmallOddCore.tblEq_idT_iff (by norm_num) hx).2 (center_eq_one h1 h2)
      simp [this]
    · simp [h2]
  · simp [h1]

theorem cosetX : (cosetOrderTables sxCert 1 5).length = (Sx664X.CS.map List.sum).sum :=
  chainK_cosetCount2 (by decide) (by decide) chainQ imgOne cOne (by norm_num) (by norm_num) Sx664X.hc

theorem hR : [sxAT].length = Sx664CK.length ∧ ∀ j < Sx664CK.length,
    imageList ([sxAT].getD j 1) = (unpack 24 5 (Sx664CK.getD j clsD0).R).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj1 : j < 1 := by simpa [Sx664CK] using hj
  interval_cases j
  rw [Nat.eq_of_beq_eq_true repCK]
  exact imgA

theorem facts :
    (sxCert.check = true ∧ sxCert.orderCertificate = 138240)
    ∧ (sxCenterOK = true)
    ∧ (ordTest 24 5 (toTable sxAT) = true ∧ ordTest 24 4 (toTable sxBT) = true)
    ∧ (wordsTest 24 5 4 sxAutWords (toTable sxAT) (toTable sxBT) = true)
    ∧ (repsOK 24 (pairTables sxAT sxBT) (pairTables sxAT⁻¹ sxBT⁻¹)
          (cosetOrderTables sxCert 1 5) [toTable sxAT] 40000 = true ∧
        repsTotal 24 (pairTables sxAT sxBT) (pairTables sxAT⁻¹ sxBT⁻¹) [toTable sxAT]
            (orderTables sxCert 4) 40000 (wordsTest 24 5 4 sxAutWords) = 138240) := by
  obtain ⟨q1, q2⟩ := chainK_check (by decide) (by decide) chainQ
  obtain ⟨r1, -, -⟩ := chainK_reps3 tA_eq tB_eq szOK' clsOK5 hR (by norm_num)
    (X := cosetOrderTables sxCert 1 5) (by rw [cosetX]; decide)
  have h := chainK_repsTotal3 (mx := 5) (my := 4) (by decide) (by decide) chainQ tA_eq tB_eq
    (by norm_num) clsOK5 hR (by norm_num) (by norm_num) (CW := [Sx664Y0.CS])
    ⟨rfl, fun j hj => by
      have hj1 : j < 1 := by simpa [Sx664CK] using hj
      interval_cases j
      exact Sx664Y0.hc⟩
  exact ⟨⟨q1, q2.trans (by decide)⟩, centerOK,
    ⟨ordTest_of_ordIs szOK' imgA cA (by norm_num) ordA,
      ordTest_of_ordIs szOK' imgB cB (by norm_num) ordB⟩,
    wordsTest_of_wordOrdK szOK' imgA imgB wordsAB, r1, h.trans (by decide)⟩

end CertificateChecks.KernelAS91Sx.Sx664OC

end
