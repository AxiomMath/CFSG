module

public import CFSG.Sporadic.HNSchreier.FullAut
public import Certificates.Certificate2096
public import Certificates.Certificate2097
public import Certificates.Certificate2098
public import Certificates.Certificate2099
public import Certificates.Certificate2100
public import Certificates.Certificate2102
public import Certificates.Certificate2103
public import Certificates.Certificate2104
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate16041
public import Certificates.Certificate2107

public noncomputable section

namespace CFSG.Sporadic.HNSchreier

open CFSG.ComponentClassification.OuterAutomorphisms

instance outer_HN_isCyclic :
    IsCyclic (Outer Blueprint.NativeSporadic.HN) :=
  ctuc_hn_full_automorphism_group.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem ctuc_hn_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.HN) ∧
    IsCyclic (Outer Blueprint.NativeSporadic.HN) ∧
    Nat.card (Outer Blueprint.NativeSporadic.HN) = 2 ∧
    Subgroup.zpowers (QuotientGroup.mk hnOuterC : Outer Blueprint.NativeSporadic.HN) = ⊤ :=
  ⟨inferInstance, outer_HN_isCyclic, card_outer_HN, outer_HN_zpowers⟩

theorem AT_HN_Schreier :
    Group.IsSolvable (Outer Blueprint.NativeSporadic.HN) :=
  ctuc_hn_Schreier.1

end CFSG.Sporadic.HNSchreier
