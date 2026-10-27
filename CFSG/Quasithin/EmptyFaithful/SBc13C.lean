module

public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem Z_le_pCoreOf_mcOf (S : Setting146 G T M) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 (mcOf T) := by
  have hZT : quasithinOmegaOneCenter T ≤ T :=
    (quasithinOmegaOneCenter_le_center T).trans inf_le_left
  have hZG : quasithinOmegaOneCenter T ≤ mcOf T :=
    hZT.trans (le_centralizer_quasithinOmegaOneCenter T)
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) := S.hyp.sylow.1.to_le hZT
  exact le_pCoreOf_of_le_normalizer 2 hZG (le_of_eq S.normalizer_Z.symm) hZ2

end SBc13

end CFSG.Quasithin
