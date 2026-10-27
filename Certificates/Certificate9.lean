module

import all CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonExceptionalF9

public import Certificates.Data.ExceptionalF9

public section

open CFSG.Glauberman.Dickson
open QuadraticAlgebra

namespace Certificates

open CFSG.Glauberman.Dickson in
open QuadraticAlgebra in
theorem certificate9 : ∀ g : ExceptionalSL5,
      exceptionalFn (g * exceptionalX5) = exceptionalFn g * exceptionalX9 ∧
      exceptionalFn (g * exceptionalY5) = exceptionalFn g * exceptionalY9 ∧
      (exceptionalFn g = 1 ↔ g = 1) := by
  decide +kernel

end Certificates
