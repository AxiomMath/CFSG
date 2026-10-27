
module

public import Certificates.Certificate4033Base
import all Certificates.Certificate4033Base

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHeKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import CFSG.Quasithin.EmptyFaithful.S151S9TThreeDFact
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBase
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.He
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHeInputs
import Certificates.Kernel.HeDc.Final
import Certificates.Kernel.HeIdx.Final
import Certificates.Kernel.HeIdx.ThreeD

namespace CertificateChecks.He4033

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

section Congr

variable {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]
  {act : Array ℕ → Lab → Lab} {D D' : LatData Lab}

end Congr

end CertificateChecks.He4033

public section

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He in
open CFSG.QuasithinUnique.K1.SporadicPerm in
theorem certificate4033 : 
    (MembersOK ptAct 8330 heTa heTb heDelta CFSG.QuasithinUnique.Ch1.SporLat.He.heLatK ∧ O2OK ptAct CFSG.QuasithinUnique.Ch1.SporLat.He.heLatK CFSG.QuasithinUnique.Ch1.SporLat.He.heOtK ∧
      (∀ j < 11, ∀ jj < 11,
        (Subgroup.closure {x | x ∈ heSgK ++
            (heMwLit[j]!).map (wordElt CFSG.Sporadic.He.a CFSG.Sporadic.He.b)} ≤
          Subgroup.closure {x | x ∈ heSgK ++
            (heMwLit[jj]!).map (wordElt CFSG.Sporadic.He.a CFSG.Sporadic.He.b)} ↔
          jj ∈ heIncl[j]!)) ∧
      (∀ g : CFSG.Sporadic.He.J, lab 8330 ptLab heDelta g = heDelta ↔
        g ∈ Subgroup.closure {x | x ∈ heSgK}) ∧
      (∀ Z : Subgroup CFSG.Sporadic.He.J, Subgroup.closure {x | x ∈ heSgK} ≤ Z → ∃ j ≤ 11,
        Z = memberOrTop 11 (fun j => Subgroup.closure {x | x ∈ heSgK ++
          (heMwLit[j]!).map (wordElt CFSG.Sporadic.He.a CFSG.Sporadic.He.b)}) j)) ∧
    CFSG.Quasithin.S151S9T.ThreeDLocFor .He := by
  have hL : He.HeOverFacts :=
    ⟨He4033.membersOK_of rfl rfl He4033.om_eq.symm rfl CFSG.KD.HeDc.heK_membersOK,
      He4033.o2OK_of rfl He4033.om_eq.symm rfl He4033.ot_eq CFSG.KD.HeDc.heK_o2OK,
      fun _ hj _ hjj => CFSG.KD.HeDc.heK_Y_le_iff hj hjj, CFSG.KD.HeDc.dc_facts.1,
      CFSG.KD.HeDc.dc_facts.2⟩
  exact ⟨hL.facts, CFSG.Quasithin.S151S9T.he_threeD_of_checks CFSG.KD.HeIdx.he_idx_ok⟩

end Certificates
