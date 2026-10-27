module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem relIndex_Ebar_eq (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {X Y : Subgroup G} (hsplit : HS9.Split95 M Q Z B t X Y) :
    (LB M Q B ⊓ X).relIndex (LB M Q B) = Nat.card Z := by
  have hhead := (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).2
  have hrel := HS9.relIndex_LB_CN h34 hs
  have hCNX : LB M Q B ⊓ hc.CN t ≤ LB M Q B ⊓ X :=
    inf_le_inf_left _ (sec97Head_of h34 h311a G M Q Z B hc n t hs X Y hsplit).1
  have hmul := Subgroup.relIndex_mul_relIndex (LB M Q B ⊓ hc.CN t) (LB M Q B ⊓ X) (LB M Q B)
    hCNX inf_le_left
  have h1 : (LB M Q B ⊓ hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
    exact hrel
  rw [hhead, h1] at hmul
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have : Nat.card Z * (LB M Q B ⊓ X).relIndex (LB M Q B) = Nat.card Z * Nat.card Z := by
    rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

end CFSG.RankThree.GF2n.Stroth80
