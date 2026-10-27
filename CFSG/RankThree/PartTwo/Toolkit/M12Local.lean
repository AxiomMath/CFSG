
module

public import CFSG.RankThree.PartTwo.Toolkit.M12LocalBase

public import Certificates.Certificate8174

public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint CFSG.RankThree.Asc83Table Subgroup
open CFSG.RankThree.PartTwo.Toolkit (toP3 toP4)
open scoped commutatorElement

namespace Enum

variable {H : Subgroup G12} (E : Enum H)

end Enum

theorem card_normalizer_P0_eq :
    Nat.card (normalizer (P0 : Set G12)) = 108 :=
  Certificates.certificate8174.1

theorem mem_normalizer_P0_facts {g : G12}
    (hg : g ∈ normalizer (P0 : Set G12)) : g ^ 2 ∈ P0 ∧ g ∈ normalizer (basisE.sub : Set G12) ∧
      g ∈ normalizer (basisF.sub : Set G12) :=
  Certificates.certificate8174.2.1 g hg

theorem card_centralizer_basisE :
    Nat.card (centralizer (basisE.sub : Set G12)) = 9 :=
  Certificates.certificate8174.2.2.1

theorem card_centralizer_basisF :
    Nat.card (centralizer (basisF.sub : Set G12)) = 9 :=
  Certificates.certificate8174.2.2.2.1

theorem card_normalizer_basisA :
    Nat.card (normalizer (basisA.sub : Set G12)) = 54 :=
  Certificates.certificate8174.2.2.2.2.1

theorem card_centralizer_basisA :
    Nat.card (centralizer (basisA.sub : Set G12)) = 9 :=
  Certificates.certificate8174.2.2.2.2.2.1

theorem card_normalizer_xy :
    Nat.card (normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) = 72 :=
  Certificates.certificate8174.2.2.2.2.2.2.1

theorem psiT_mul_of_mem {g h : G12}
    (hg : g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12))
    (hh : h ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) :
    psiT (tbl (g * h).1) = psiT (tbl g.1) * psiT (tbl h.1) :=
  Certificates.certificate8174.2.2.2.2.2.2.2.1 g hg h hh

theorem psiT_inj_of_mem {g h : G12}
    (hg : g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12))
    (hh : h ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12))
    (e : psiT (tbl g.1) = psiT (tbl h.1)) : g = h :=
  Certificates.certificate8174.2.2.2.2.2.2.2.2.1 g hg h hh e

theorem sign_psiT_of_mem {g : G12}
    (hg : g ∈ normalizer ((zpowers (x * y) : Subgroup G12) : Set G12)) :
    Equiv.Perm.sign (psiT (tbl g.1)).2 = 1 :=
  Certificates.certificate8174.2.2.2.2.2.2.2.2.2 g hg

end CFSG.RankThree.PartTwo.Toolkit.M12
