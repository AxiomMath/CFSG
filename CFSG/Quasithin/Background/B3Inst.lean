module

public import Certificates.Certificate8063

public section

namespace CFSG.Quasithin.B3

theorem propB32A_of {n : ℕ} {k : Mod} (hn : SQTKn n)
    (hA : CaseA n k) : PropB32A n k :=
  Certificates.certificate8063.1 n k hn hA

theorem propB32B5_of {n : ℕ} {k : Mod} (hn : SQTKn n)
    (hB : CaseB n k) (hexc : ¬ (n = 8 ∧ k = Mod.ut0)) : PropB32B5 n k :=
  Certificates.certificate8063.2.1 n k hn hB hexc

theorem propB32B6_eight : PropB32B6 8 Mod.ut0 :=
  Certificates.certificate8063.2.2.1

theorem strongTl6_of {k : Mod} (hk : k = Mod.u0 ∨ k = Mod.ut0) :
    StrongTl6 k := by
  rcases hk with rfl | rfl
  · exact Certificates.certificate8063.2.2.2.1
  · exact Certificates.certificate8063.2.2.2.2

end CFSG.Quasithin.B3
