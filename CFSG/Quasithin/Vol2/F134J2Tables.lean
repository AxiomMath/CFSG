module

public import CFSG.Quasithin.Vol2.F134J2Data
public import CFSG.Quasithin.Vol2.F134MatCode
public import CFSG.Sporadic.Bridge.J2Native

public section

namespace CFSG.Quasithin.F134

open CFSG.Sporadic.Bridge.J2

@[expose] def j2aC : ℕ := ofDigs (2 ^ 112) j2aR

@[expose] def j2bC : ℕ := ofDigs (2 ^ 112) j2bR

@[expose] def j2oneC : ℕ := ofDigs (2 ^ 112) j2oneR

@[expose] def j2TelB : ℕ := ofDigs (2 ^ 1568) (j2TelR.map (ofDigs (2 ^ 112)))

@[expose] def j2Tel (i : ℕ) : ℕ := digW 1568 j2TelB i

@[expose] def j2TGB : ℕ := ofDigs (2 ^ 1568) (j2TGenR.map (ofDigs (2 ^ 112)))

@[expose] def j2TG (k : ℕ) : ℕ := digW 1568 j2TGB k

@[expose] def j2DB : ℕ := ofDigs (2 ^ 1568) (j2DR.map (ofDigs (2 ^ 112)))

@[expose] def j2D (j : ℕ) : ℕ := digW 1568 j2DB j

@[expose] def j2NxtB : ℕ := ofDigs (2 ^ 7) j2NxtL

@[expose] def j2Nxt (i : ℕ) : ℕ := digW 7 j2NxtB i

@[expose] def j2ParB : ℕ := ofDigs (2 ^ 9) j2ParL

@[expose] def j2Par (i : ℕ) : ℕ := digW 9 j2ParB i

@[expose] def j2DecB (j : ℕ) : ℕ := ofDigs (2 ^ 21) (j2DecRows.getD j [])

@[expose] def j2Dec (j i : ℕ) : ℕ := digW 21 (j2DecB j) i

@[expose] def j2BadB : ℕ := ofDigs (2 ^ 16) j2BadL

@[expose] def j2Bad (j : ℕ) : ℕ := digW 16 j2BadB j

@[expose] def j2CosB (j : ℕ) : ℕ := ofDigs (2 ^ 8) (j2CosRows.getD j [])

@[expose] def j2Cos (j i : ℕ) : ℕ := digW 8 (j2CosB j) i

@[expose] noncomputable def j2Word : List ℕ → GL (Fin 14) (ZMod 5)
  | [] => 1
  | c :: w => (if c = 0 then uA else uB) * j2Word w

@[expose] def j2WordC : List ℕ → ℕ
  | [] => j2oneC
  | c :: w => mul14 (if c = 0 then j2aC else j2bC) (j2WordC w)

end CFSG.Quasithin.F134
