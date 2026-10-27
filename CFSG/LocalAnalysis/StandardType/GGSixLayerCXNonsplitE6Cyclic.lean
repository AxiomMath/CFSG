module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Dvd
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Arith
public import CFSG.RankThree.PartOne.KE.CTCasesE6Eight
public import CFSG.RankThree.PartOne.KE.CTCasesE6Nine
public import CFSG.RankThree.PartOne.KE.CTCasesE6Twelve
public import CFSG.RankThree.PartOne.KE.CTMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

namespace E6Nonsplit

section Regular


theorem not_isComponentOf_centralizer_of_dvd_phi_regular {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {m : ℕ} (hm : m = 8 ∨ m = 9 ∨ m = 12)
    (hpm : (p : ℤ) ∣ (exhaustionPhi m).eval (Nat.card K : ℤ))
    {a : ↥(adjointGroup .E6 K)} (ha : orderOf a = p) {X : Subgroup ↥(adjointGroup .E6 K)} :
    ¬ IsComponentOf X (Subgroup.centralizer ({a} : Set ↥(adjointGroup .E6 K))) := by
  rcases hm with rfl | rfl | rfl
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_eight_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_nine_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg
  · obtain ⟨-, -, T, hT, -, -, -, -, -, hcent⟩ :=
      E6_twelve_cyclic_sylow cyclic_torus_prime_centralizers K hp hp3 hpm
    obtain ⟨g, -, hg⟩ := hcent a ha
    exact F4Nonsplit.not_isComponentOf_of_conj_centralizer_cyclic hT hg

end Regular

end E6Nonsplit

end CFSG.StandardType
