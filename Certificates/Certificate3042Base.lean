
module

public import CFSG.Monster.B.TwoA.Unitary.WStabInputs
public import Certificates.Kernel.MonsterB.Chain3042
public import CFSG.Certificates.Kernel.MonsterB.PermGroupBfs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawSound

@[expose] public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Unitary CFSG.KC.Bfs CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Certificates.Native

namespace CertificateChecks.Batch3042

set_option maxRecDepth 100000

open CertificateChecks.Chain3042

theorem perm : allN 10 (fun j => permOK 24 5 (mask 5) (24 * 5) (P2C.S j) (P2C.SI j)) = true := by
  quickRfl

@[expose] noncomputable def SA : Array (Array Nat) :=
  Array.ofFn (n := 10) fun j => unpack 24 5 (P2C.S j.val)

theorem SA_size : SA.size = 10 := by simp [SA]

theorem binds : Binds 24 5 P2C.S 10 5 P2C.BP SA p2Base := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [SA], fun j hj => ?_, rfl, ?_⟩
  · rw [SA, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  · intro t ht
    interval_cases t <;> rfl

theorem raw : rawChainOK 24 (SA.extract 0 6) SA p2Base
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 6 10 p2Der) 1 = true :=
  rawChainK_sound (NS := 1) (CH := 24) binds P2C.head P2C.hl (by norm_num) P2C.hs

theorem orbits : rawOrbitSizes 24 SA p2Base = [2, 21, 20, 16, 3] := by
  rw [rawOrbitSizesK_sound binds perm P2C.hl]
  decide

theorem gens_eq : ∀ i < 6, SA[i]! = permGens[i]! := by decide +kernel

theorem gens_perm : ∀ k < permGens.size, PermArr permGens[k]! = true := by decide +kernel

theorem card_genH : Nat.card (genH permGens) = 40320 := by
  have hb : ([0, 3, 4, 8, 5] : List (Fin 24)).Nodup := by decide
  have hbase : (([0, 3, 4, 8, 5] : List (Fin 24)).map Fin.val).toArray = p2Base := rfl
  have hs : permGens.size = 6 := rfl
  rw [card_genH_of_rawChainOK gens_perm hb (by rw [hs, SA_size]; norm_num)
    (fun i hi => gens_eq i (hs ▸ hi)) (by rw [hs, hbase]; exact raw), hbase, orbits]
  rfl

theorem p2 : certOK amul permGens idArr p2Cert = true ∧ p2Cert.pts.size = 40320 := by
  have h := bfsCert_amul_card (fuel := 41000) gens_perm (by rw [card_genH]; norm_num)
  rw [card_genH] at h
  exact h

end CertificateChecks.Batch3042

namespace Certificates

end Certificates
