module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthInputs
public import Certificates.Certificate45
public import Certificates.Certificate49
public import Certificates.Certificate53
public import Certificates.Certificate59
public import Certificates.Certificate68
public import Certificates.Certificate72
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
import CFSG.LocalAnalysis.StandardType.GGTBJD4Frame
import CFSG.LocalAnalysis.StandardType.GGTBJD4Spin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggSecFiveTBJTypeD4Input_holds
    : GGSecFiveTBJTypeD4Input := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL f ψ hadm hker hrange
  obtain ⟨hp, hp2, hpf, ψ', hinj, u, hu, hup, hu1, J', hJ', hmap, hcount⟩ :=
    ggTBJD4_frame hcfg hL ψ hadm hker hrange
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by have := hadm.2.1; omega)
  exact ggTBJD4_spin (F := GaloisField 2 f) hF hp hp2 hpf hu hup hu1 hJ' hcount
    ((J'.equivMapOfInjective ψ' hinj).trans (MulEquiv.subgroupCongr hmap)).symm

end CFSG.StandardType

end
