module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLCheckInputs
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import Certificates.Kernel.Sporadic.McLC.Syl

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSpor.McLC in
open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.McLProof in
open CFSG.Sporadic.SmallOddCore in
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.ClassicalInvolution.McLData in
theorem certificate9314 : (CFSG.Sporadic.SmallOddCore.permOK 275 Ta = true ∧ CFSG.Sporadic.SmallOddCore.permOK 275 Tb = true ∧ involOK 275 Ta = true ∧
      CFSG.Sporadic.Th.Native.invOK 275 Ta (invT 275 Ta) = true)
    ∧ (Nat.card (genOf 275 kgens) = 40320 ∧ kgens.all (CFSG.Sporadic.SmallOddCore.permOK 275) = true ∧
      kgens.all (fun g => CFSG.Sporadic.Th.Native.invOK 275 g (invT 275 g)) = true ∧
      kgens.all (fun g => commTT 275 g Ta) = true ∧ kgens.length = 2 ∧
      (tblEq 275 Ta (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true ∧
        CFSG.Sporadic.SmallOddCore.permOK 275 (wordTbl 275 kgens [1, 1, 1, 1, 1, 1, 1]) = true))
    ∧ ((∀ w ∈ kWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧ (∀ w ∈ sWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ w ∈ conjWords, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 2) ∧
      (∀ p ∈ repData, (∀ l ∈ p.1, 1 ≤ l ∧ l ≤ 2) ∧ ∀ cw ∈ p.2, ∀ l ∈ cw, 1 ≤ l ∧ l ≤ 2) ∧
      sgens.all (CFSG.Sporadic.SmallOddCore.permOK 275) = true ∧ repTbls.all (CFSG.Sporadic.SmallOddCore.permOK 275) = true ∧
      (conjWords.map (wordTbl 275 abT)).all (fun c => CFSG.Sporadic.SmallOddCore.permOK 275 c && CFSG.Sporadic.Th.Native.invOK 275 c (invT 275 c)) =
        true ∧
      (repData.all fun p => p.2.all fun cw => CFSG.Sporadic.SmallOddCore.permOK 275 (wordTbl 275 kgens cw) &&
        CFSG.Sporadic.Th.Native.invOK 275 (wordTbl 275 kgens cw) (invT 275 (wordTbl 275 kgens cw))) = true ∧
      (repGens.all fun gs => gs.all (CFSG.Sporadic.SmallOddCore.permOK 275)) = true)
    ∧ (CFSG.Sporadic.SmallOddCore.enumOK 275 capK 128 sgens = true ∧ sylowCoverOK = true)
    ∧ (translatesOK abArr fixZ orbZ.1 orbZ.2.1 orbZ.2.2 = true ∧ keysSortedOK orbZ.1 = true ∧
      orbZ.1.size = 22275)
    ∧ (∀ x ∈ genOf 275 kgens, x = 1 ∨ x = tp 275 Ta ∨
      ∃ r ∈ repTbls.map (tp 275), ∃ c ∈ genOf 275 kgens, x = c * r * c⁻¹)
    ∧ (∀ gs ∈ repGens, genOf 275 kgens ≤ genOf 275 gs)
    ∧ (CFSG.ClassicalInvolution.McLProof.commOK = true ∧ kx ∈ kgens ∧ ky ∈ kgens) :=
  ⟨tables_ok, ⟨card_K, kgens_ok⟩, words_ok, sylow_ok, orbit_K, cover_K, gen_K, comm_ok⟩

end Certificates
