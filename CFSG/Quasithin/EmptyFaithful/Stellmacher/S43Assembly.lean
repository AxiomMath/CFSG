module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Hss43OddAt (H M : Subgroup G) : Prop :=
  ∀ α : Geo H M, S43.Sit43 α → Odd (bMin H M) → False

theorem hss43At_of_odd (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hodd : Hss43OddAt H M) :
    Hss43At H M := by
  intro α hα hb hlt horth
  by_contra hne
  have hb1 : 1 < bMin H M := lt_of_le_of_ne (bMin_pos hA) (Ne.symm hne)
  have hs : S43.Sit43 α := ⟨hα, hb, hlt, horth, hb1⟩
  rcases Nat.even_or_odd (bMin H M) with he | ho
  · exact S43.Even.false_of_even hA h26 hs he
  · exact hodd α hs ho

end F53.Stellmacher

@[expose] def F53.Stellmacher.Hss43Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    F53.Stellmacher.Hss43OddAt H M

theorem F53.Stellmacher.Hss43_of_odd (h26 : F53.Stellmacher.Hss26A)
    (hodd : F53.Stellmacher.Hss43Odd) : F53.Stellmacher.Hss43 :=
  fun G _ _ H M S hA =>
    F53.Stellmacher.hss43At_of_odd hA (h26 G H M S hA) (hodd G H M S hA)

end CFSG.Quasithin
