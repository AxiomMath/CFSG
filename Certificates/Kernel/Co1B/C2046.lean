
module

public import CFSG.Sporadic.Co1Block.TwoBExtraCheckInputs
public meta import CFSG.Sporadic.Co1Block.ConjBData
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1.Module.InvDataBase
public meta import CFSG.Sporadic.Co1.Module.FormsBase
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Kernel.Co1B.Iota
public import Certificates.Kernel.Co1B.Data2046
public import CFSG.Certificates.Kernel.Co1BWordSound
public import CFSG.Certificates.Kernel.Co1BTabSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1B

open CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KD.Co1B CFSG.KLie.CT CFSG.Sporadic.SmallF2.Native
  CertificateChecks.KernelCo1Cover

theorem nGens_chk : andB (Nat.beq (wordABFrom R0 R1 CFSG.Sporadic.Co1.Module.nWord1 oneK) N1)
    (andB (Nat.beq (wordABFrom R0 R1 CFSG.Sporadic.Co1.Module.nWord2 oneK) N2)
      (Nat.beq (powWK (gwordFrom [N1, N2] CFSG.Sporadic.Co1.Module.wordB oneK) 6) SBK)) = true := by
  quickRfl

theorem dag2046_chk : dagOK [R0, R1] CFSG.Sporadic.Co1Block.conjBDerivs CRS CRIS = true := by quickRfl

theorem conj2046_chk : Nat.beq (mulWK (getL oneK CRS 10) R0) (mulWK SBK (getL oneK CRS 10)) = true := by
  quickRfl

theorem wordB_lt : ∀ l ∈ CFSG.Sporadic.Co1.Module.wordB, l < 2 := by decide +kernel

theorem idRows_eq : idRows 24 = unpackR 24 oneK := one_eq.symm

theorem wordRows_eq (w : List Bool) :
    CFSG.Sporadic.Co1.Module.wordRows w = unpackR 24 (wordABFrom R0 R1 w oneK) := by
  have hl : CFSG.Sporadic.Co1.Module.letterRows = fun b =>
      if b then CFSG.Sporadic.Co1Schreier.Native.aR else CFSG.Sporadic.Co1Schreier.Native.bR := rfl
  rw [CFSG.Sporadic.Co1.Module.wordRows, idRows_eq]
  simp only [hl]
  exact foldl_wordAB aR_eq bR_eq w oneK

theorem rowsSB_eq : CFSG.Sporadic.Co1.Module.rowsSB = unpackR 24 SBK := by
  have h := nGens_chk
  simp only [andB_eq_and, Bool.and_eq_true] at h
  have hG : ∀ l < [N1, N2].length, CFSG.Sporadic.Co1.Module.nGens[l]! = unpackR 24 (getL 0 [N1, N2] l) := by
    intro l hl
    rcases l with _ | _ | l
    · change CFSG.Sporadic.Co1.Module.wordRows CFSG.Sporadic.Co1.Module.nWord1 = _
      rw [wordRows_eq, Nat.eq_of_beq_eq_true h.1]
      rfl
    · change CFSG.Sporadic.Co1.Module.wordRows CFSG.Sporadic.Co1.Module.nWord2 = _
      rw [wordRows_eq, Nat.eq_of_beq_eq_true h.2.1]
      rfl
    · simp at hl
  rw [CFSG.Sporadic.Co1.Module.rowsSB, genWordRows_eq hG wordB_lt idRows_eq, powRows_eq _ idRows_eq,
    Nat.eq_of_beq_eq_true h.2.2]

theorem conjB_ok : CFSG.Sporadic.Co1Block.conjBCheckOf [CFSG.Sporadic.Co1Schreier.Native.aR,
    CFSG.Sporadic.Co1Schreier.Native.bR] CFSG.Sporadic.Co1Block.conjBDerivs
    CFSG.Sporadic.Co1.Module.rowsSB = true := by
  have hd := dag_sound dag2046_chk
  rw [List.map_cons, List.map_cons, List.map_nil] at hd
  rw [CFSG.Sporadic.Co1Block.conjBCheckOf, aR_eq, bR_eq, rowsSB_eq, hd]
  dsimp only
  rw [← one_eq, getD_map_u, List.getD_cons_zero, CFSG.KC.F2W.mul_unpackW, CFSG.KC.F2W.mul_unpackW]
  change (true && (unpackR 24 (mulWK (getL oneK CRS 10) R0) == unpackR 24 (mulWK SBK (getL oneK CRS 10)))) = true
  rw [Nat.eq_of_beq_eq_true conj2046_chk, beq_self_eq_true, Bool.true_and]

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native in
open CFSG.Monster.B.Co2.Native in
theorem c2046 : (conjBCheckOf [aR, bR] conjBDerivs CFSG.Sporadic.Co1.Module.rowsSB = true)
    ∧ (tabSoundOf (Native.triTable twoBTris) twoBTris.toArray = true) :=
  ⟨conjB_ok, CFSG.KC.Co1B.tabSoundOf_triTable _⟩

end CertificateChecks.KernelCo1B

end
