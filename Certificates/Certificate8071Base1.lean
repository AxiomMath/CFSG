
module

public import Certificates.Certificate8071Base
import all Certificates.Certificate8071Base

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs
import Certificates.Certificate8072Base
import Certificates.Kernel.Misc.Tits.Chain8071
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Certificates.Certificate8072

@[expose] public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelMisc CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2264

namespace CertificateChecks.Batch8071

private theorem gen_eq₁ : titsArray CFSG.Open.quasithinTitsData2 = unpack 1755 11 (TitsD.S 1) := by
  rw [Certificates.certificate8072.2, der_eq (by norm_num)]

private theorem gen_eq₀ : titsArray CFSG.Open.quasithinTitsData1 = unpack 1755 11 (TitsD.S 0) := by
  rw [Certificates.certificate8072.1, der_eq (by norm_num)]

private theorem gens_get : titsGens.size = 2 ∧ ∀ j < 2, titsGens[j]! = unpack 1755 11 (TitsCh.S j) := by
  refine ⟨rfl, fun j hj => ?_⟩
  rw [sEq hj]
  interval_cases j
  · exact gen_eq₀
  · exact gen_eq₁

private theorem strong_get : titsStrong.size = 14 ∧
    ∀ j < 14, titsStrong[j]! = unpack 1755 11 (TitsCh.S j) := by
  rw [strong_eq]
  exact strongOf_bind gens_get TitsCh.head

private theorem binds : Binds 1755 11 TitsCh.S 14 7 TitsCh.BP titsStrong
    (titsBase.map Fin.val).toArray :=
  ⟨by norm_num, by norm_num, by norm_num, strong_get.1, strong_get.2, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOK t ht)⟩

private theorem orbits : rawOrbitSizes 1755 titsStrong (titsBase.map Fin.val).toArray =
    [1755, 10, 8, 8, 2, 4, 2] := by
  have h := rawOrbitSizesK_orb (NS := 28) (CH := 64) (LR := TitsCh.LR) (PSI := TitsCh.SI) binds
    perms TitsCh.ho (by norm_num)
  have e : (List.range 7).map (fun i => rcnt (TitsCh.LR i)) = [1755, 10, 8, 8, 2, 4, 2] := by
    decide +kernel
  exact h.trans e

private theorem closure_eq : Subgroup.closure (Set.range fun j : Fin 2 =>
    permOfArr 1755 titsStrong[j.val]!) = T := by
  have e : (fun j : Fin 2 => permOfArr 1755 titsStrong[j.val]!) = fun j => d j.val := by
    funext j
    rw [strong_get.2 j.val (by omega), sEq j.2, ← der_eq (by omega)]
    rfl
  rw [e]
  rfl

private theorem chain : rawChainOK 1755 (titsStrong.extract 0 titsGens.size) titsStrong
    (titsBase.map Fin.val).toArray titsRawWords 4 = true := by
  rw [gens_get.1, words_raw]
  refine rawChainK_of_card_orb 4 binds TitsCh.head TitsCh.ho (by norm_num : 1755 ≤ 28 * 64) ?_
  rw [orbits, closure_eq]
  exact card_T.trans (by norm_num)

end CertificateChecks.Batch8071

end
