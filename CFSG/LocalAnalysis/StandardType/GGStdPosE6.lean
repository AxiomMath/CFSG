module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
import CFSG.LocalAnalysis.StandardType.GGStdPosE6Core
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Basic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosStdPosE6 :
    GGKGPosStdPosCase .E6 (fun p _ => p ≠ 3) := by
  rintro G _ _ p Bs X n f ψ h hp3
  obtain ⟨⟨hp, hp2, hadm, -⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, hBN, -⟩, hinn, hc, -⟩ := h
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpq
  have hT6 : ¬ GGKGPosTorsion p .E6 n := by
    rintro (⟨h', -⟩ | ⟨-, h'⟩)
    · cases h'
    · exact hp3 h'
  subst hX
  exact StdPosExc.exists_stdPos_e6 hker ((Nat.coprime_primes hp Nat.prime_three).2 hp3) hBs hBN
    hinn (hc hT6) (TableBExc.ggExcToralRankInput_E6_of_ne_three hp hp2 hp3 hpF)

end CFSG.StandardType

end
