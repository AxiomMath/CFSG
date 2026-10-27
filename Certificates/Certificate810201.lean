module

public import Certificates.Data.HuppertU38Three.Data
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
import Certificates.Kernel.U38Three.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 in
theorem certificate810201 :
    (permOfArr 513 U38Three.d0 0 = 0 ∧ permOfArr 513 U38Three.d0 1 = 1) ∧
    permOfArr 513 U38Three.d0 ^ 3 = 1 ∧ permOfArr 513 U38Three.d0 ≠ 1 ∧
    permOfArr 513 U38Three.d0 ∈ U38G ∧
    Subgroup.closure (permsA 513 U38Three.hGens) ≤
      U38G ⊓ MulAction.stabilizer (Equiv.Perm (Fin 513)) (0 : Fin 513) ⊓
        MulAction.stabilizer (Equiv.Perm (Fin 513)) (1 : Fin 513) ∧
    Nat.card (Subgroup.closure (permsA 513 U38Three.hGens)) = 378 ∧
    (∀ x ∈ Subgroup.closure (permsA 513 U38Three.hGens), x ^ 3 = 1 → x ≠ 1 →
      x ≠ permOfArr 513 U38Three.d0 → x ≠ permOfArr 513 U38Three.d0 * permOfArr 513 U38Three.d0 →
      x * permOfArr 513 U38Three.d0 = permOfArr 513 U38Three.d0 * x ∧
        {y | y ∈ Subgroup.closure (permsA 513 U38Three.hGens) ∧ y ^ 3 = 1 ∧ x * y = y * x}.ncard ≤ 9) ∧
    Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb]) ≤
      Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ∧
    Nat.card (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb])) = 504 ∧
    IsSimpleGroup (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb])) ∧
    Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X' ≤
      Subgroup.normalizer (Subgroup.closure (permsA 513 #[U38Three.la, U38Three.lb]) :
        Set (Equiv.Perm (Fin 513))) ∧
    Nat.card ↥(Subgroup.centralizer ({permOfArr 513 U38Three.d0} : Set (Equiv.Perm (Fin 513))) ⊓ X') =
      1512 := KernelU38Three.facts

end Certificates
