module

public import Certificates.Data.SmithB45HM22Std

public section

namespace CFSG.KD.C260416

open CFSG.Quasithin.HM22

@[expose] noncomputable def powOK (n : ℕ) (A B : PM) : Bool :=
  A.length == n && B.length == n && PM.eqm n (PM.mul A A) (PM.idm n) &&
    PM.eqm n (PM.mul B (PM.mul B (PM.mul B B))) (PM.idm n)

theorem pow_all : powOK 6 n1P n2P = true ∧ powOK 15 std15A std15B = true ∧
    powOK 45 std45A std45B = true ∧ powOK 45 std45cA std45cB = true ∧
    powOK 84 std84A std84B = true := by
  decide +kernel

end CFSG.KD.C260416

end
