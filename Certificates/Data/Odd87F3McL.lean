module

public import Certificates.Data.Odd87F3CC
public import CFSG.Sporadic.SmallOddCore.McLData
public meta import Certificates.Data.Odd87F3CC
public meta import CFSG.Sporadic.SmallOddCore.McLData

public section

namespace Certificates.Odd87F3.McL

open CFSG.Sporadic.SmallOddCore

@[expose] def orb0 : Orb where
  base := 0
  y0 := 109
  sg := decodeWords ("ABCddcaC dBAbD")
  ns := decodeWords ("a A b c C d D ba ca Ca da Da bA cA CA dA DA Ab cb Cb db Db ac Ac bc cc dc aC AC bC CC dC ad Ad " ++
    "aD bD cD aba cba Cba dba Dba aca bca aCa ACa CCa dCa DCa ada bda Cda aDa bDa CDa abA AbA CbA dbA " ++
    "ccA ACA CCA DCA adA AdA CdA bDA cDA CDA bAb DAb Acb ccb dcb CCb bdb Cdb bac dac bAc dAc DAc abc " ++
    "Abc cbc Acc ccc baC caC CaC DbC ACC CCC cdC CdC bAd cbD ccD dcD DcD daba Daba Acba Dcba CCba " ++
    "adba cdba Cdba aDba Abca Dbca cACa adCa aDCa AbDa CCDa DCDa cabA dabA DAbA dCbA dccA dACA CDCA " ++
    "CDAb dAcb dccb Dccb DCCb Adaba bdaba")

@[expose] def orb1 : Orb where
  base := 1
  y0 := 142
  sg := decodeWords ("aCABdba")
  ns := decodeWords ("a A b c C d D ba ca Ca da Da bA cA CA dA DA ab Ab cb Cb db Db ac Ac bc cc dc AC bC CC dC ad Ad " ++
    "bd cd Cd aD cba Cba dba Dba aca Dca aCa ACa bCa dCa DCa ada Ada cda aDa CDa abA CbA dbA DbA acA " ++
    "dcA ACA CCA DCA AdA bdA cdA bDA bab Cab dab CAb dAb Acb dcb bdb aDb CDb bac Dac Dbc ccc Cdc dAC " ++
    "DAC ACC dCC bAd dAd abd dbd DaD Acba dcba Dcba dCba cDca dACa AdCa cAda CAda baDa DaDa AdbA cDbA " ++
    "DACA abdA AbdA cdAb Dbac")

@[expose] def orb2 : Orb where
  base := 13
  y0 := 25
  sg := decodeWords ("Adccd BCdcd")
  ns := decodeWords ("a A b C d Ca da Da bA cb Cb db Db aC dC DC cd Cd bDa DCb ADb")

@[expose] def orb3 : Orb where
  base := 37
  y0 := 37
  sg := decodeWords ("CdCD CADac CCad")
  ns := decodeWords ("b c d D ab Ab ac cc dc Dc")

@[expose] def orbs : List Orb := [orb0, orb1, orb2, orb3]

@[expose] def cov : List (ℕ × List ℤ) :=
  decodeCov ("0 1 0DCA 1cda 0caC 0DA 1Acb 1Cb 0cD 0ccD 1CAda 0cabA 0cDA 2 1ac 0ccA 0ACC 1cc 1aDa 0Abc 1da 1CCA " ++
    "0Cb 1dC 0CDAb 2Da 1dCba 1aDb 0aCa 2d 1bA 1Db 1dcba 1abd 1aD 0bca 1dbA 3 0ACa 1cdA 0bdb 0C 1CA 0D " ++
    "1Acba 0ccc 1cba 0a 1ACC 1dc 0Dccb 0adA 1bac 0dc 0Acc 0aca 0CDa 0CDA 1bab 0ca 0CCA 1Cba 1AbdA " ++
    "0Dba 1AC 0DCDa 0bdaba 0dC 0AC 0dbA 1c 3D 0c 0Acb 1d 0CDCA 2ADb 0dac 2aC 0dACA 1ACa 0Dcba 1Cd " ++
    "0dccA 1abA 0daba 1bd 1Dcba 1Cab 2da 2b 0bC 1DaD 0abc 0CdC 1dcb 1ab 1CC 0dAcb 0aDa 0bDa 1db 3b " ++
    "0Db 1dACa 0Cda 1DbA 1AdCa 1CDa 0Daba 1bCa 1aca 1Dba 1Dca 0dcD 0DCCb 1cdAb 0da 0abA 0ba 2DCb 0CC " ++
    "0adba 0dcb 1Ab 2a 0CCb 0cbc 3Ab 0cdC 1Ad 0AbDa 1cAda 0CCba 0Ab 2C 1bdb 0Adaba 0CA 1baDa 3dc 1Dac " ++
    "1cDbA 2cd 0Acba 2db 0dCbA 1cd 1dcA 0dabA 0dA 0Cdb 0cba 1CAb 0Dbca 0adCa 1cDca 1DCa 1bC 0Ca 1DCA " ++
    "0d 1bDA 1dCC 0A 1DaDa 0CCa 0DcD 0Ad 0DAb 1ca 0cbD 0ad 0bD 0b 0CaC 1ACA 1D 0Ac 0baC 1AdbA 1a 3Dc " ++
    "0DbC 0bDA 2Db 0aDCa 1cb 0aba 1A 1ccc 2Ca 1dCa 1Ca 0bc 1ada 0CdA 0aDba 0cACa 1dAb 0cdba 0CCC 1bc " ++
    "1DACA 2bDa 0bAb 1acA 3ab 0bac 0CCDa 0bAd 0dccb 1dba 0bda 1bAd 0AbA 0dCa 1C 1Ac 0ACA 2dC 0DAbA 3d " ++
    "0cA 2Cb 1b 3ac 1Cdc 0Cdba 1dAd 2A 1ad 0ccb 0aC 1AdA 0Cba 1Ada 2cb 1cA 0DCa 0dAc 0aD 0db 1abdA " ++
    "1CbA 1dA 0AdA 1aCa 0Abca 1dab 1ba 0ac 0dba 0cb 0CbA 1dAC 0ada 3cc 2bA 1Dbac 0bA 1bdA 0DAc 1DAC " ++
    "0Da 1Dbc 1Da 1CDb 2Cd 0bAc 2DC 1dbd 3c 1DA 0cc")

@[expose] def mclCCOK : Bool :=
  ccOK 275 [mclCentTbl 18, mclCentTbl 19, mclCentTbl 20, mclCentTbl 21] orbs cov

end Certificates.Odd87F3.McL
