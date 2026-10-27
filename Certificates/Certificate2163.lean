module

public import CFSG.Sporadic.Schreier.J1CentData
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public meta import CFSG.Sporadic.Schreier.J1CentData
public meta import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.SporSch.J1.Cent2163B
public meta import CFSG.Sporadic.Schreier.J1CountCheck
public import CFSG.Sporadic.Schreier.J1CountCheck
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelSporSch.J1

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native in
theorem certificate2163 : (repsOK 3080 j1GenTbls j1GenInvTbls (j1OrderTables 2) [j1ATbl] 2000 = true ∧
      (conjClosure 3080 j1GenTbls j1GenInvTbls j1ATbl 2000).1.size = 1463
    )
    ∧ (j1CentTables.length = 120 ∧ oddWitnessOK 3080 15 j1CentTables = true)
    ∧ ((List.range 4).all (fun i => invOK 3080 (j1CTbl i) (j1CInvTbl i)) = true)
    ∧ ((List.range 3).all (fun j => invOK 3080 (j1DTbl j) (invT 3080 (j1DTbl j)) &&
      commT 3080 (j1DTbl j) j1ATbl) = true ∧ commT 3080 (j1DTbl 0) (j1DTbl 2) = false
    )
    ∧ (mulTreeOK 3080 j1DGens j1DElts j1DClo.2.1 j1DClo.2.2 = true ∧
      mulClosedOK 3080 j1DGens j1DGensInv j1DElts = true ∧
      keysDistinct 3080 j1DElts.toList = true ∧ j1DElts.size = 60
    )
    ∧ (j1DClasses.1.size = 5 ∧
      classLabelsOK 3080 j1DElts j1DClasses.1 j1DClasses.2.1 j1DClasses.2.2 = true
    )
    ∧ (∀ b : Fin 5 → Bool, b ⟨0, by norm_num⟩ = true →
      ((List.range 60).countP fun k =>
        if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) ∣ 60 →
      ((List.range 60).countP fun k =>
        if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 1 ∨
      ((List.range 60).countP fun k =>
        if h : j1DClasses.2.1[k]! < 5 then b ⟨j1DClasses.2.1[k]!, h⟩ else false) = 60
    ) :=
  ⟨reps_facts, cent_facts', c_checks, d_checks, d_closure, d_labels, d_subsets⟩

end Certificates
