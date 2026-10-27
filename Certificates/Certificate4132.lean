module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKTitsInputs
import Certificates.Kernel.SporSch.Tits.Exam4132

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.TitsExam in
open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.Schreier.TitsQT in
theorem certificate4132 : (isInvA 1755 conjFArr conjFInvArr = true ∧
          siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjWArr = true ∧
          (compA 1755 conjWArr conjXArr)[12]! = 78 ∧ (compA 1755 conjXArr conjWArr)[12]! = 101 ∧
          (compA 1755 conjWArr conjYArr)[12]! = 38 ∧ (compA 1755 conjYArr conjWArr)[12]! = 34) := KernelSporSch.TitsExam.facts

end Certificates
