module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternating

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

public abbrev ASevenCertificateGroup := alternatingGroup (Fin 7)

@[expose] public def a7t : ASevenCertificateGroup :=
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3, by
    simp [Equiv.Perm.sign_mul]⟩

@[expose] public def a7a : ASevenCertificateGroup :=
  ⟨Equiv.swap (4 : Fin 7) 5 * Equiv.swap 5 6, by
    simp [Equiv.Perm.sign_mul]⟩

@[expose] public def a7u : ASevenCertificateGroup :=
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap 1 3, by
    simp [Equiv.Perm.sign_mul]⟩

@[expose] public def a7v : ASevenCertificateGroup :=
  ⟨Equiv.swap (0 : Fin 7) 2 * Equiv.swap 2 1 *
      Equiv.swap 1 3 * Equiv.swap 4 5, by
    simp [Equiv.Perm.sign_mul]⟩

@[expose] public def a7CentralizerGenerators :
    Finset ASevenCertificateGroup := {a7t, a7a, a7u, a7v}

@[expose] public def fixedSpanPow
    (n : Nat) (x z : ASevenCertificateGroup) : Prop :=
  ∃ i : Fin n, z = x ^ (i : Nat)

@[expose] public def fixedSpanThree
    (x y z : ASevenCertificateGroup) : Prop :=
  ∃ i : Fin 3, ∃ j : Fin 3,
    z = x ^ (i : Nat) * y ^ (j : Nat)

public abbrev A7OrderThree :=
  {x : ASevenCertificateGroup // x ≠ 1 ∧ x ^ 3 = 1}

end CFSG.GorensteinWalter
