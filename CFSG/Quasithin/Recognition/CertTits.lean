
module

public import CFSG.Quasithin.Recognition.CertTitsBase
import all CFSG.Quasithin.Recognition.CertTitsBase

public import CFSG.Open.QuasithinDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertDataTits
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertDataTits
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsInputs
public import Certificates.Certificate8071

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem titsChain_check :
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData1)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData1)) = true ∧
    isInvA 1755 (titsArray CFSG.Open.quasithinTitsData2)
      (invCand 1755 (titsArray CFSG.Open.quasithinTitsData2)) = true ∧
    titsGens.size ≤ titsStrong.size ∧ (∀ i < titsGens.size, titsStrong[i]! = titsGens[i]!) ∧
    rawChainOK 1755 (titsStrong.extract 0 titsGens.size) titsStrong
      (titsBase.map Fin.val).toArray titsRawWords 4 = true ∧
    rawOrbitSizes 1755 titsStrong (titsBase.map Fin.val).toArray = [1755, 10, 8, 8, 2, 4, 2] :=
  Certificates.certificate8071

theorem card_closure_tits_perm :
    Nat.card (Subgroup.closure {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
      permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} :
        Subgroup (Equiv.Perm (Fin 1755))) = 17971200 := by
  obtain ⟨-, -, hOS, hSO, hchain, horb⟩ := titsChain_check
  have hc := card_closure_permOfArr_of_rawChainOK (n := 1755) (by norm_num) (O := titsGens)
    (S := titsStrong) (W := titsRawWords) titsBase_nodup (chunks := 4) (by norm_num) hOS hSO hchain
  have hset : {g | ∃ k < titsGens.size, permOfArr 1755 titsGens[k]! = g} =
      {permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData1),
        permOfArr 1755 (titsArray CFSG.Open.quasithinTitsData2)} := by
    ext g
    rw [Set.mem_ofPred_eq, titsGens_size, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · exact Or.inl (by rw [titsGens_zero])
      · exact Or.inr (by rw [titsGens_one])
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by rw [titsGens_zero]⟩
      · exact ⟨1, by norm_num, by rw [titsGens_one]⟩
  rw [hset] at hc
  rw [hc, horb]
  norm_num

theorem card_quasithinTits :
    Nat.card CFSG.Open.quasithinTits = 17971200 := by
  obtain ⟨hp1, hp2, -⟩ := titsChain_check
  rw [← card_closure_tits_perm]
  exact card_units_closure_pair _ _ _ _
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData1 hp1)
    (coe_permOfArr_titsArray CFSG.Open.quasithinTitsData2 hp2)

end CFSG.Quasithin
