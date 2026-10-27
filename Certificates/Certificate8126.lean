
module

public import CFSG.RankThree.Native.Fi22UCheckInputs
import Certificates.Kernel.Fi22U.C8126

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.Fi22U CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Fischer in
theorem certificate8126 :
    rawChainOK 693 ((fi22OuterStrong693 2).extract 0 fi22OuterUnitaryGenCount)
      (fi22OuterStrong693 2) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations) 4 = true ∧
    rawOrbitSizes 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] ∧
    (∀ k < 693, fi22UnitaryPoint k ≠ 0 ∧
      fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 ∧
      fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k) ∧
    (∀ j < 693, ∀ k < 693, j < k → fi22LexLt (fi22UnitaryPoint j) (fi22UnitaryPoint k)) ∧
    (Finset.univ.filter fun v : Fin 6 → F4 =>
      v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = 693 ∧
    (∀ v : Fin 6 → F4, fi22Normalize (fi22Normalize v) = fi22Normalize v) ∧
    (∀ (c : F4) (v : Fin 6 → F4), c ≠ 0 → fi22Normalize (c • v) = fi22Normalize v) ∧
    (∀ k < 46, fi22Herm (fi22TransvectionVector k) (fi22TransvectionVector k) = 0) ∧
    (∀ k < 46, ∀ j < 693, fi22UnitaryPoint ((fi22OuterArr693 (15 + k))[j]!) =
      fi22Normalize (fi22Tv (fi22TransvectionVector k) (fi22UnitaryPoint j))) ∧
    eqA 693 (compA 693 (fi22OuterArr693 15) (fi22OuterArr693 16))
      (compA 693 (fi22OuterArr693 16) (fi22OuterArr693 15)) = false := KernelFi22U.C8126.facts8126

end Certificates
