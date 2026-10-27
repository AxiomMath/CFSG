module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even13
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even16D
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even18
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenEndgame

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem false_of_even (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (he : Even (bMin H M)) : False := by
  have hb : 4 ≤ bMin H M := claim13 hA h26 hs he
  have h14 : ∀ {γ : Geo H M}, Sit43 γ → Claim14 γ := fun hγ => claim14 hA h26 hγ he hb
  have h15 : ∀ {γ : Geo H M}, Sit43 γ → Claim15 γ := fun hγ => claim15 hA h26 hγ he hb
  have h17 : Claim17 α :=
    claim17 hA h26 hs he hb h14 h15 fun h6 => claim16 hA h26 hs he h6 h14 h15
  obtain ⟨β, hβ⟩ := hs.exists_adj hA
  exact endgame hA h26 hs (by omega) hβ (claim18 hA h26 hs he hb h17 hβ)

theorem false_of_transvec (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 4 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hD4 : Nat.card (Vn β) = 2 ^ 6) (hWQ : ⁅Wn α, Qv α⁆ ≤ Zv α) {x : G} (hx : x ∈ stab α)
    (hxt : IsTransvec 1 x (Zv α) (Wn α)) : False :=
  endgame hA h26 hs (by omega) hβ (hyp18_of_transvec hA h26 hs hb hβ hD4 hWQ hx hxt)

end CFSG.Quasithin.F53.Stellmacher.S43.Even
