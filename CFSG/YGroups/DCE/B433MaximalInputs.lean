module

public import CFSG.YGroups.DCE.B433Check

public section

namespace CFSG.YGroups.DCE.B433

open CFSG.YGroups.DCE.B433Native

@[expose] def b433Vals : List ℕ :=
  [1, 86316516, 33816182400, 504245392560, 12678169870080, 50712679480320, 23478092352,
    283991005089792, 5282570779200, 195747435, 1044084577536, 262954634342400, 43028940165120,
    190172548051200, 133120783635840, 7888639030272, 21514470082560, 113778447552, 1152560897280,
    1584771233760, 8537488128, 412896, 160533964800]

@[expose] def Checked.vals
    {L : Array ByteArray} {O : BigOmega} {cert : B.Cert}
    (S : Checked L O cert) : List ℕ :=
  let E := env S.good S.ctxGood S.pt S.pt_zero S.actSpec S.nodesOK
  let st := B.replay E cert.prog
  (List.range cert.fins.size).map fun l => 4089470473293004800 / E.chainBound st cert.fins[l]!.2

@[expose] def b433ValsCheck :
    
    Bool :=
  let L := lettersB ()
  let O := omegaB433 L
  let cert := certB433 ()
  if h : bigOK O L fixB = true ∧ smallOK O L cert = true then
    Checked.vals (⟨rfl, rfl, h.1, h.2⟩ : Checked L O cert) == b433Vals
  else false

end CFSG.YGroups.DCE.B433
