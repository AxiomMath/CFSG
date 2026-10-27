module

public import CFSG.RankThree.PartTwo.Census.CarrierCases
import CFSG.RankThree.PartTwo.Census.Carrier.G2Prime
import CFSG.RankThree.PartTwo.Census.Carrier.G2Three
import CFSG.RankThree.PartTwo.Census.Carrier.ReeG2One
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
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
public import Certificates.Certificate8150
public import Certificates.Certificate8151
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartTwo.Census

open TauCeti

theorem carrierCases433_of_spin
    (g2Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.G2 q).Valid), q.p = 2 →
      Excluded433 (.lie ⟨.G2 q, hv⟩))
    (trialityD4Even : ∀ (q : PrimePower) (hv : (LieTypeIndex.trialityD4 q).Valid), q.p = 2 →
      Excluded433 (.lie ⟨.trialityD4 q, hv⟩))
    (reeF4 : ∀ (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid), Excluded433 (.lie ⟨.reeF4 m, hv⟩))
    (tits : ∀ hv : LieTypeIndex.tits.Valid, Excluded433 (.lie ⟨.tits, hv⟩)) :
    CarrierCases433 :=
  { sp8Two := bridgeSp8Two,
    sp6Four := bridgeSp6Four,
    omega8PlusTwo := bridgeOmega8PlusTwo,
    omega8MinusTwo := bridgeOmega8MinusTwo,
    b3Two := excluded433_B_three_two,
    g2Even := g2Even,
    g2Three := excluded433_G2_three,
    g2Prime := excluded433_G2_prime,
    trialityD4Even := trialityD4Even,
    reeG2One := excluded433_reeG2_one,
    reeF4 := reeF4,
    tits := tits }

end CFSG.RankThree.PartTwo.Census
