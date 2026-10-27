module

public import CFSG.RankThree.Co2.JFacts
import Certificates.Kernel.Co2J.Facts
import Certificates.Kernel.Co2Fuse.Final

public section

namespace Certificates

open CertificateChecks.KernelSpor

open CFSG.RankThree.Co2 in
theorem certificate8106 : (∀ i < 10, wordMat jWords[i]! * wordMat jWords[i]! = 1) ∧
    (∀ i < 10, ∀ k < 10,
      wordMat jWords[i]! * wordMat jWords[k]! = wordMat jWords[k]! * wordMat jWords[i]!) ∧
    Set.BijOn jMat (Set.Iio 1024) (matGrp jWords) ∧
    matGrp jWords ≤ matGrp sylWords ∧
    (∀ t ∈ matGrp sylWords, ∀ x ∈ matGrp jWords, ∃ y ∈ matGrp jWords, t * x = y * t) ∧
    (∀ t ∈ matGrp sylWords, (∀ x ∈ matGrp jWords, t * x = x * t) → t ∈ matGrp jWords) ∧
    (∀ A : Set (Matrix (Fin 22) (Fin 22) (ZMod 2)), A ⊆ matGrp sylWords → 1 ∈ A →
      (∀ x ∈ A, ∀ y ∈ A, x * y ∈ A) → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      (∀ x ∈ A, x * x = 1) → Nat.card A = 1024 → A = matGrp jWords) :=
  ⟨Co2J.jFacts.sq, Co2J.jFacts.comm, Co2J.jFacts.bij, Co2J.jFacts.le, Co2J.jFacts.norm,
    Co2J.jFacts.cent Co2Fuse.T_card_le, Co2J.jFacts.ea Co2Fuse.T_card_le⟩

end Certificates
