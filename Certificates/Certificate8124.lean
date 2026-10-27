module

public import CFSG.RankThree.Native.Fi22FiveDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import Certificates.Kernel.Sporadic.Fi22.Five8124S
public import CFSG.Monster.B.Fischer.Fi22GraphBase

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Fischer in
theorem certificate8124 :
    ((fi22FiveQ ≤ fi22P ∧ IsElementaryAbelian 5 fi22FiveQ ∧ Nat.card fi22FiveQ = 25 ∧
      ∃ S : Sylow 5 fi22P, (S : Subgroup fi22P) = fi22FiveQ.subgroupOf fi22P) ∧
    ({H : Subgroup (Equiv.Perm (Fin 3510)) | H ≤ fi22FiveQ ∧ Nat.card H = 5} =
        Set.range (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i)) ∧
      Function.Injective (fun i : Fin 6 => Subgroup.zpowers (fi22FiveLine i))) ∧
    (fi22FiveW ∈ fi22R ∧ fi22FiveW ∉ fi22P ∧ orderOf fi22FiveW = 2) ∧
    ∀ i : Fin 6,
      fi22FiveC i = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22R ∧
      Nat.card (fi22FiveC i) = 1200 ∧
      fi22FiveC i ⊓ fi22P = Subgroup.centralizer {fi22FiveLine i} ⊓ fi22P ∧
      Nat.card (fi22FiveC i ⊓ fi22P : Subgroup (Equiv.Perm (Fin 3510))) = 600 ∧
      fi22FiveD i ≤ fi22P ∧ IsSimpleGroup (fi22FiveD i) ∧
      (∃ g ∈ fi22FiveD i, ∃ h ∈ fi22FiveD i, g * h ≠ h * g) ∧ Nat.card (fi22FiveD i) = 60 ∧
      fi22FiveW ∈ (Subgroup.center (fi22FiveC i)).map (fi22FiveC i).subtype ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i =
        Subgroup.zpowers (fi22FiveLine i) ⊔ Subgroup.zpowers fi22FiveW ∧
      Subgroup.zpowers (fi22FiveLine i) ⊓ Subgroup.zpowers fi22FiveW = ⊥ ∧
      Commute (fi22FiveLine i) fi22FiveW ∧
      Nat.card (Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ fi22FiveC i :
        Subgroup (Equiv.Perm (Fin 3510))) = 10 ∧
      Subgroup.centralizer (fi22FiveD i : Set (Equiv.Perm (Fin 3510))) ⊓ (fi22FiveC i ⊓ fi22P) =
        Subgroup.zpowers (fi22FiveLine i)) ∧
    (∀ i : Fin 6, permOfArr 3510 (fi22FiveHArr i) ∈ fi22P ∧
      permOfArr 3510 (fi22FiveHArr i) * fi22FiveLine i * (permOfArr 3510 (fi22FiveHArr i))⁻¹ =
        fi22FiveLine 0) ∧
    (∀ k < 2, Rep 3510 fi22FiveQGenArrs[k]! (permOfArr 3510 fi22FiveQGenArrs[k]!)) ∧
    ∀ i : Fin 6,
      (∀ k < 4, Rep 3510 (fi22FiveCGenArrs i)[k]! (permOfArr 3510 (fi22FiveCGenArrs i)[k]!)) ∧
      (∀ k, 1 ≤ k → k < 3 → permOfArr 3510 (fi22FiveCGenArrs i)[k]! ∈ fi22P) ∧
      fi22FiveD i = Subgroup.closure (permsA 3510 (fi22FiveDGenArrs i)) := KernelSpor.Fv8124.holds

end Certificates
