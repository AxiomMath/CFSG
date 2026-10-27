module

public import CFSG.Timmesfeld.Moufang.J2Certificate15953Inputs
public import CFSG.Timmesfeld.Moufang.LinePres
public import CFSG.Timmesfeld.Moufang.J2Data

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open CFSG.Sporadic.Bridge.J2 (seedGroup natU idL wfM mulL toM unitL lwordL uA uB wfM_idL natX_wf
  natXi_wf natU_val natU_inv natU_mem val_natWord natWord_mem val_wordProd_of_lwordL
  wordProd_eq_one_of_lwordL le_card_seedGroup nativeEquiv)

namespace J2

private theorem cert15953_0 :
    ∀ w ∈ lineRels 2 false, (w.map fun l => (emb l.1, l.2)) ∈ lineRels 5 true := by
  decide +kernel

private theorem cert15953_1 :
    derivedOK (2 * (5 + 2)) (invLetter (5 + 2)) (codes (lineRels 5 true)) J2Data.words = true := by
  decide +kernel

end J2

end CFSG.Timmesfeld.Moufang

namespace Certificates

open CFSG.Certificates CFSG.Certificates.CosetEnumeration in
open CFSG.Timmesfeld.Moufang CFSG.Timmesfeld.Moufang.J2 in
theorem certificate15953 : (
    ∀ w ∈ lineRels 2 false, (w.map fun l => (emb l.1, l.2)) ∈ lineRels 5 true
  ) ∧ (
    derivedOK (2 * (5 + 2)) (invLetter (5 + 2)) (codes (lineRels 5 true)) J2Data.words = true
  ) := by
  exact ⟨CFSG.Timmesfeld.Moufang.J2.cert15953_0, CFSG.Timmesfeld.Moufang.J2.cert15953_1⟩

end Certificates
