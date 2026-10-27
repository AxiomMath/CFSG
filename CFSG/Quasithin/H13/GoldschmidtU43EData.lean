module

public import CFSG.Quasithin.H13.GoldschmidtU43CRel

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

structure JWSetup (z : G) where
  t : G
  w : G
  a : G
  a' : G
  e : Two z t w a a'
  R : Subgroup ↥(Hz z)
  hR : SylR e.swap.hyp R
  A : ↥(Hz z)
  σ₁ : ↥(Hz z)
  u : ↥(Hz z)
  v : ↥(Hz z)
  jw : JW13 A σ₁ u v
  gen : Subgroup.closure ({A, σ₁, u, v} : Set ↥(Hz z)) = ⊤
  hAA : A * A = zK z
  hσR : σ₁ ∈ R
  hu : u ∈ Subgroup.normalizer (R : Set ↥(Hz z))
  huv : u * v ∈ Subgroup.normalizer (R : Set ↥(Hz z))
  huE : (u : G) ∈ Eg z t w a
  huvE : ((u * v : ↥(Hz z)) : G) ∈ Eg z t w a'

end CFSG.Quasithin.H13.U43
