module

public import Certificates.Kernel.CertF8.Om9558Small
public import Certificates.Kernel.CertF8.Om9558Forest0
public import Certificates.Kernel.CertF8.Om9558Forest1
public import Certificates.Kernel.CertF8.Om9558Forest2
public import Certificates.Kernel.CertF8.Om9558Forest3
public import Certificates.Kernel.CertF8.Om9558Sorted0
public import Certificates.Kernel.CertF8.Om9558Sorted1
public import CFSG.Certificates.Kernel.CertF8.OmSound
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartTwo.Sec5.Hyp
public import CFSG.RankThree.PartTwo.Sec5.Tools
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.KC.CertF8.Om9558

open CFSG.KC.CertF8.Om

#kc_forall_chunks ch9558fAll
  (fun k => CFSG.KC.CertF8.Om.allFrom (Nat.mul 511 k) 511
    (CFSG.KC.CertF8.Om.forestAt CFSG.KC.CertF8.Om9558.F) = true) 256
  CFSG.KC.CertF8.Om9558.ch9558f.c 1

#kc_forall_chunks ch9558sAll
  (fun k => CFSG.KC.CertF8.Om.allFrom (Nat.mul 511 k) 511
    (CFSG.KC.CertF8.Om.sortAt CFSG.KC.CertF8.Om9558.F CFSG.KC.CertF8.Om9558.S 130816) = true) 256
  CFSG.KC.CertF8.Om9558.ch9558s.c 1

theorem ch9558htree : ∀ n < 1024, hAt H n = true := by
  intro n hn
  by_cases h : n < 512
  · have := (allFrom_iff _ _ _).1 ch9558h0 n h
    rwa [Nat.zero_add] at this
  · have := (allFrom_iff _ _ _).1 ch9558h1 (n - 512) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

theorem ch9558hsorted : ∀ i < 1024, sortAt H HS 1024 i = true := by
  intro i hi
  have := (allFrom_iff _ _ _).1 ch9558hs i hi
  rwa [Nat.zero_add] at this

theorem ch9558checks : OmChecks F S H HS where
  gens j hj := ch9558gens ⟨j, hj⟩
  hgens t ht := ch9558hgens ⟨t, ht⟩
  root0 := ch9558root0
  roots k hk := ch9558roots ⟨k, hk⟩
  quad := ch9558quad
  eps j hj := ch9558eps ⟨j, hj⟩
  seedrev k hk := ch9558seedrev ⟨k, hk⟩
  letters := ch9558letters
  hroot := ch9558hroot
  fix := ch9558fix
  forest := all_of_chunks (c := 511) (m := 256) (by norm_num) (by norm_num) ch9558fAll
  sorted := all_of_chunks (c := 511) (m := 256) (by norm_num) (by norm_num) ch9558sAll
  htree := ch9558htree
  hsorted := ch9558hsorted

theorem om9558OK : (omCodesOf F H).OK := omCodes_ok ch9558checks

end CFSG.KC.CertF8.Om9558
