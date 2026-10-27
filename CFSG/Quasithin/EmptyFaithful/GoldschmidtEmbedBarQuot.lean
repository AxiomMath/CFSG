module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtEmbedLocA7Aut
public import CFSG.Quasithin.Vol2.Ch3xC58NSPair

public section

namespace CFSG.Quasithin.C58NS

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.EmbedLoc

variable {G : Type} [Group G] [Finite G]

theorem exists_noncomm_of_simple_of_not_prime {X : Type} [Group X] (hs : IsSimpleGroup X)
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { ‹Group X› with mul_comm := fun a b => hc a b }
  exact h IsSimpleGroup.prime_card

end CFSG.Quasithin.C58NS
