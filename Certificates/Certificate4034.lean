module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuDcInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRuKInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatCore
public import Certificates.Certificate3172
public import Certificates.Certificate4143
import Certificates.Kernel.RuDc.Final
import Certificates.Kernel.RuDc.Facts

public section

namespace Certificates

open CFSG.QuasithinUnique.Ch1.SporLat

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.RuCert in
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.SmallF2 in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate4034 : 
    MembersOK ptAct ruData.n ruTaL ruTbL ruDelta ruLatK ∧ O2OK ptAct ruLatK ruOtK ∧
      (∀ j < 5, ∀ jj < 5, (GensIn ptAct ruDelta ruLatK j jj ↔ jj ∈ ruIncl[j]!)) ∧
      (∀ g : J ruData, lab ruData.n ptLab ruDelta g = ruDelta ↔
        g ∈ Subgroup.closure {x | x ∈ ruSgK}) ∧
      ∀ Z : Subgroup (J ruData), Subgroup.closure {x | x ∈ ruSgK} ≤ Z → ∃ j ≤ 5,
        Z = memberOrTop 5 (fun j => Subgroup.closure {x | x ∈ ruSgK ++
          (ruMw[j]!).map (wordElt (a ruData) (b ruData))}) j := by
  have h := CFSG.KD.RuDc.facts
  exact ⟨RuK.ruK_membersOK h, RuK.ruK_o2OK h, fun _ hj _ hjj => RuK.incl_iff h hj hjj,
    (RuK.dc_facts h).1, (RuK.dc_facts h).2⟩

end Certificates
