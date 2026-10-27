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
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
import CFSG.LocalAnalysis.StandardType.GGStdPosE8Core
import CFSG.LocalAnalysis.StandardType.GGTableBExcSplit
import CFSG.LocalAnalysis.StandardType.GGTableBExcThreeE8

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPosStdPosE8 :
    GGKGPosStdPosCase .E8 (fun _ _ => True) := by
  rintro G _ _ p Bs X n f ψ h -
  obtain ⟨⟨hp, hp2, hadm, -⟩, ⟨hker, hX, -, hpq⟩, ⟨hBs, -, -⟩, hinn, hc, -⟩ := h
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hF]; exact hpq
  have hT : GGExcToralRankInput .E8 (GaloisField 2 f) p := by
    by_cases hp3 : p = 3
    · subst hp3
      exact TableBExc.Three.ggExcToralRankInput_E8_three hpF
    · exact ggExcToralRankInput_E8_of_ne_three hp hp2 hp3 hpF
  have hT8 : ¬ GGKGPosTorsion p .E8 n := by
    rintro (⟨h', -⟩ | ⟨h', -⟩) <;> cases h'
  subst hX
  exact StdPosExc.exists_stdPos_e8 hker hBs hinn (hc hT8) hT

end CFSG.StandardType

end
