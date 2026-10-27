module

public import Certificates.Kernel.D4Syl.Checks
public import CFSG.Certificates.Kernel.D4SylSound
public import CFSG.Certificates.Kernel.D4SylRank

public section

namespace CertificateChecks.KernelD4Syl

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.KC.D4SylK CFSG.KC.D42K CFSG.Open

theorem check_parts : enumCheckK (encM genA) (encM genB) bfsPar nxtTab = true ∧
    witCheckK nxtTab witWords = true := by
  have h := checkK
  unfold d4SylCheckK at h
  rwa [Bool.and_eq_true, aK_eq, bK_eq] at h

theorem enum_parts : sylowElems.length = 81 ∧ sylowElems.Nodup ∧
    IsNxtTable sylowElems genA genB nxtTab :=
  enum_spec check_parts.1

theorem closed_parts :
    ∀ x ∈ sylowElems, mulArr x genA ∈ sylowElems ∧ mulArr x genB ∈ sylowElems :=
  closed_of_table enum_parts.1 enum_parts.2.2

theorem card_closure_eq :
    Nat.card (Subgroup.closure ({wordGL wordA, wordGL wordB} : Set (GL (Fin 8) GF8))) = 81 := by
  rw [← enum_parts.1]
  exact card_closure (coe_wordGL wordA) (coe_wordGL wordB) enum_parts.2.1 closed_parts

theorem exists_mem_sylowElems (g : GL (Fin 8) GF8)
    (hg : g ∈ Subgroup.closure ({wordGL wordA, wordGL wordB} : Set (GL (Fin 8) GF8))) :
    ∃ x ∈ sylowElems, ((g : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = toMat x :=
  mem_of_mem_closure (coe_wordGL wordA) (coe_wordGL wordB) closed_parts g hg

theorem card_le_nine (E : Subgroup (GL (Fin 8) GF8))
    (hE : E ≤ Subgroup.closure ({wordGL wordA, wordGL wordB} : Set (GL (Fin 8) GF8)))
    (hEA : IsElemAbelian 3 E) : Nat.card E ≤ 9 := by
  obtain ⟨w1, w2, w3, w4⟩ := wit_spec (coe_wordGL wordA) (coe_wordGL wordB) enum_parts.1
    enum_parts.2.1 enum_parts.2.2 check_parts.2
  exact card_le_nine_of_witnesses _ _ card_closure_eq w1 w2 w3 w4 E hE hEA

end CertificateChecks.KernelD4Syl

end
