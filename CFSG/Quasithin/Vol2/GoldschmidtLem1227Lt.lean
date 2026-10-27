module

public import CFSG.Quasithin.Vol2.GoldschmidtLem1227LtFinish

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.Lem1227Eq
open CFSG.QuasithinUnique.Vol2Native.A312L
open scoped IsMulCommutative

namespace Lem1227Lt

theorem exists_nu {G : Type} [Group G] [Finite G] {Y : Subgroup G} {X : Type} [Group X]
    [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a) (φ : ↥Y →* X)
    (hφs : Function.Surjective φ) :
    ∃ ν : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* X, Function.Surjective ν := by
  have hle := pCore_le_ker_of_surjective_simple hX φ hφs
  have : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  exact ⟨QuotientGroup.lift _ φ hle, QuotientGroup.lift_surjective_of_surjective _ φ hφs hle⟩

end Lem1227Lt

end CFSG.Quasithin.H13
