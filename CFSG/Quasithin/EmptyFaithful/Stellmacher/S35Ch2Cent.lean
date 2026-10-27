module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Std S35.Fin S35.Ch S35.II
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

omit [Finite G] in
theorem secIdx_eq_two_iff {x : G} (hx : x ∈ stab δ) :
    secIdx (Subgroup.zpowers x) (Cb δ) (Vn δ) = 2 ↔ (c.θ ⟨x, hx⟩).IsSwap := by
  rw [c.secIdx_eq_idx hx, idx_orth_eq_two_iff]

omit [Finite G] in
theorem rk_eq_idx {x : G} (hx : x ∈ stab δ) : S34.rk δ x = idx orth (c.θ ⟨x, hx⟩) :=
  c.secIdx_eq_idx hx

omit [Finite G] in
theorem rk_eq_two_iff {x : G} (hx : x ∈ stab δ) :
    S34.rk δ x = 2 ↔ (c.θ ⟨x, hx⟩).IsSwap := c.secIdx_eq_two_iff hx

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
