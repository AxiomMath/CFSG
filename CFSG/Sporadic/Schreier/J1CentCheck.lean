module

public import CFSG.Sporadic.Schreier.J1CentData
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.J1CentData
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Certificate2163

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

theorem j1_inv_class :
    repsOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) [j1ATbl] 2000 = true ∧
      (conjClosure 3080 j1GenTbls j1GenInvTbls j1ATbl 2000).1.size = 1463 :=
  Certificates.certificate2163.1

theorem j1_cent_checks :
    j1CentTables.length = 120 ∧ oddWitnessOK 3080 15 j1CentTables = true :=
  Certificates.certificate2163.2.1

theorem j1_c_checks :
    (List.range 4).all (fun i => invOK 3080 (j1CTbl i) (j1CInvTbl i)) = true :=
  Certificates.certificate2163.2.2.1

theorem j1_d_checks :
    (List.range 3).all (fun j => invOK 3080 (j1DTbl j) (invT 3080 (j1DTbl j)) &&
      commT 3080 (j1DTbl j) j1ATbl) = true ∧ commT 3080 (j1DTbl 0) (j1DTbl 2) = false :=
  Certificates.certificate2163.2.2.2.1

theorem j1_D_closure :
    mulTreeOK 3080 j1DGens j1DElts j1DClo.2.1 j1DClo.2.2 = true ∧
      mulClosedOK 3080 j1DGens j1DGensInv j1DElts = true ∧
      keysDistinct 3080 j1DElts.toList = true ∧ j1DElts.size = 60 :=
  Certificates.certificate2163.2.2.2.2.1

theorem j1_D_labels :
    j1DClasses.1.size = 5 ∧
      classLabelsOK 3080 j1DElts j1DClasses.1 j1DClasses.2.1 j1DClasses.2.2 = true :=
  Certificates.certificate2163.2.2.2.2.2.1

theorem j1_D_subsets : ∀ b : Fin 5 → Bool, b ⟨0, by norm_num⟩ = true →
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) ∣ 60 →
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 1 ∨
    ((List.range 60).countP fun k =>
      if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 60 :=
  Certificates.certificate2163.2.2.2.2.2.2

end CFSG.Sporadic.Schreier
