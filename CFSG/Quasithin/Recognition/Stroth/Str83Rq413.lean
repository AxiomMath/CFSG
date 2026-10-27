module

import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Exists
import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Odd
public import CFSG.Quasithin.Recognition.Stroth.Str83RqTrack

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem false_of_GT_eq_K {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) (hO4 : t.GT = t.K) : False := by
  obtain ⟨ε, n, b₀, b₁, h, h₀, h₁, hb₁, hcomm⟩ :=
    Track.exists_isMaxArc_commutator_eq_bot t hfr hrq hO4
  exact Track.IsMaxArc.false_of_odd_of_commutator_eq_bot t hfr hrq h h₀ h₁ hb₁ hcomm

end Track

end CFSG.Quasithin.Stroth.Rq
