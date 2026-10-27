module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ4Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Sporadic.J4.QTRankInvNative
public import Certificates.Certificate8024Base

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Lin2
open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT
open CFSG.Blueprint.NativeSporadic (Carrier)

private theorem invGens_check :
    (∀ j < 4, invEs.getD j 0 < 1024 ∧ isInvE (invEs.getD j 0) = true ∧ invCs.getD j 0 < 2048 ∧
          ∃ x ∈ invData, x.1 = invEs.getD j 0 ∧
            invCs.getD j 0 ^^^ actT (tabE (invEs.getD j 0)) (invCs.getD j 0) = x.2.1) ∧
        (∀ i < 4, (∀ j ∈ invWords.getD i [], j < 4) ∧
          compT (kInvTab i)
            (((invWords.getD i []).map fun j => tabE (invEs.getD j 0)).foldr compT idT) = idT) := by
  decide +kernel

end CFSG.QuasithinUnique.Lin2

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 in
open CFSG.Open CFSG.QuasithinUnique CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
open CFSG.Blueprint.NativeSporadic (Carrier) in
theorem certificate4077 : ((∀ j < 4, invEs.getD j 0 < 1024 ∧ isInvE (invEs.getD j 0) = true ∧ invCs.getD j 0 < 2048 ∧
            ∃ x ∈ invData, x.1 = invEs.getD j 0 ∧
              invCs.getD j 0 ^^^ actT (tabE (invEs.getD j 0)) (invCs.getD j 0) = x.2.1) ∧
          (∀ i < 4, (∀ j ∈ invWords.getD i [], j < 4) ∧
            compT (kInvTab i)
              (((invWords.getD i []).map fun j => tabE (invEs.getD j 0)).foldr compT idT) = idT)) :=
  CFSG.QuasithinUnique.Lin2.invGens_check

end Certificates
