module

public import CFSG.Sporadic.HNOddCore.XCheck
public import CFSG.Sporadic.HNOddCore.SCheck
public import CFSG.Sporadic.HNOddCore.FiveData
public import CFSG.Sporadic.HNSchreier.FALocalCheck
public import CFSG.Sporadic.HNOddCore.FiveCheckInputs
public import CFSG.Sporadic.HNOddCore.FiveGens
public import Certificates.Certificate2085

public section

namespace CFSG.Sporadic.HNOddCore.Native

open CFSG.Sporadic.HNSchreier

theorem five_fix (x : X) : fJ • x = x ↔ x.val ∈ FAData.fFixed :=
  Certificates.certificate2085.1 x

theorem five_comm_aGen {j : ℕ} (hj : j < 5) :
    fJ * aGenJ j = aGenJ j * fJ :=
  Certificates.certificate2085.2.1 j hj

theorem five_comm_g5 : fJ * g5J = g5J * fJ :=
  Certificates.certificate2085.2.2.1

theorem five_iGen_omega {k t : ℕ} (hk : k < 6) (ht : t < 50)
    {x : X} (hx : x.val = FAData.fFixed.getD t 0) :
    (iGen k • x).val = FAData.fFixed.getD ((FAData.iSmall[k]!).getD t 0) 0 :=
  Certificates.certificate2085.2.2.2.1 k hk t ht x hx

theorem five_a6Gen_omega {k t : ℕ} (hk : k < 4) (ht : t < 50)
    {x : X} (hx : x.val = FAData.fFixed.getD t 0) :
    (a6Gen k • x).val = FAData.fFixed.getD ((FAData.a6Small[k]!).getD t 0) 0 :=
  Certificates.certificate2085.2.2.2.2.1 k hk t ht x hx

theorem five_stab {g : JH}
    (hg : g ∈ Subgroup.closure (Set.range fun k : Fin 6 => iGen k)) (hfix : g • x0 = x0) :
    g ∈ Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j) :=
  Certificates.certificate2085.2.2.2.2.2.1 g hg hfix

theorem five_small_cert : fiveSmallChecks = true :=
  Certificates.certificate2085.2.2.2.2.2.2

end CFSG.Sporadic.HNOddCore.Native
