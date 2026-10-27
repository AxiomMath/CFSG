module

public import CFSG.OddTranspositions.PartThree.Twelve.FiveDefs
public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
public import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour.TableE1Five

theorem eq_or_neg_of_eq_or_neg {M : Type*} [AddGroup M] {a b c : M} (hac : c = a ∨ c = -a)
    (hbc : c = b ∨ c = -b) : a = b ∨ a = -b := by
  rcases hac with rfl | rfl
  · exact hbc
  · rcases hbc with h | h
    · exact Or.inr (by rw [← h, neg_neg])
    · exact Or.inl (neg_inj.1 h)

variable {G : Type} [Group G] {D : Set G} {hC : HypothesisC D} {n : ℕ}

namespace FiveChart

theorem b_vec_eq_zero_iff (c : FiveChart hC n) {a : G} {u w : Fin n → ZMod 5}
    (hva : c.vec a = u ∨ c.vec a = -u) : c.b (c.vec a) w = 0 ↔ c.b u w = 0 := by
  rcases hva with h | h <;> simp [h]

theorem vec_conj_eq_act (c : FiveChart hC n) {x y : G} (hx : x ∈ commSet D hC.d)
    (hy : y ∈ commSet D hC.d) :
    c.vec (x * y * x⁻¹) = act (refl c.b (c.vec x)) (c.vec y) ∨
      c.vec (x * y * x⁻¹) = -act (refl c.b (c.vec x)) (c.vec y) := by
  rcases c.vec_conj x hx y hy with h | h
  · left
    rw [h, act_refl (c.norm_vec x hx)]
    module
  · right
    rw [h, act_refl (c.norm_vec x hx)]
    module

end FiveChart

end CFSG.OddTranspositions.PartThree

end
