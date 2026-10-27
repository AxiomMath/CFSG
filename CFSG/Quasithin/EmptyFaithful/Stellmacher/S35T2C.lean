module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2CLink
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2L

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2C

open S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem step2C (hS : Sit H M S) : S35.II.Step2C H M := by
  intro hN β hβ hWab Zt hZ hZW hZV l hl x hx hxN _ hcomm
  have hP : ∀ P : Subgroup G, stab β ⊓ stab l ≤ P → P ≤ stab β →
      P = stab β ∨ P ≤ Subgroup.normalizer (Zv l : Set G) := fun P h1 h2 =>
    (S35.T2L.inputs_of_sit hS).maximal β l hβ hl P h2 h1
  obtain ⟨hlink, hK⟩ := link_of_transv hS hβ hl hP hWab hZ hZW hZV hx hxN hcomm
  exact ⟨_, S35.T2L.commonHyp_of_link hS hN hβ hl hx hxN hlink, hK⟩

end S35.T2C

end F53.Stellmacher

end CFSG.Quasithin
