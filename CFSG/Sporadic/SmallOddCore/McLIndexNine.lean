module

public import Certificates.Certificate744101
public import Certificates.Certificate744105
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Sporadic.SmallOddCore

theorem mcl_index_nine_package :
    ∃ U P Q : Subgroup ↥CFSG.Sporadic.Schreier.mclP, CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧
      Nat.card P = 9 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      Q ≤ P ∧ Nat.card Q = 9 ∧ ∀ q ∈ Q, q ^ 3 = 1 :=
  Certificates.certificate744101

theorem mcl_index_three_package :
    ∃ (U P : Subgroup ↥CFSG.Sporadic.Schreier.mclP)
      (a g : ↥CFSG.Sporadic.Schreier.mclP),
      CFSG.QuasithinUnique.IsSylowTwoOf U ⊤ ∧ U ≤ P ∧ Nat.card P = 3 * Nat.card U ∧
      (∀ α : MulAut ↥CFSG.Sporadic.Schreier.mclP,
        U.map α.toMonoidHom = U → P.map α.toMonoidHom = P) ∧
      a ∈ P ∧ a ≠ 1 ∧ a ^ 3 = 1 ∧ g * a * g⁻¹ = a⁻¹ :=
  Certificates.certificate744105

end CFSG.Sporadic.SmallOddCore
