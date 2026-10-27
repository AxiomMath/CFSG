module

import all CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9

public import Certificates.Data.ExceptionalF9

public section

open CFSG.Glauberman.Dickson
open QuadraticAlgebra

namespace Certificates

open CFSG.Glauberman.Dickson in
open QuadraticAlgebra in
theorem certificate8 : ∀ g : ExceptionalSL5,
      let code := exceptionalWordCode (exceptionalMatrixKey g)
      evalExceptionalCode exceptionalX5 exceptionalY5 code.1 code.2 = g := by
  decide +kernel

end Certificates
