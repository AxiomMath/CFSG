module

public import CFSG.Monster.Tri.LeechModelEight
public import CFSG.Monster.GMS.S365Basic

public section

namespace CFSG.Monster.Tri.Leech

open CFSG.Monster.GMS

variable {G : Type*} [Group G]

theorem twoBInEight_of_twoBCount {a z₀ : G}
    (h : ∀ x y t : G, IsLineTriple a x y → IsEightExt x y t →
      twoBCount z₀ x y t = 1 ∨ twoBCount z₀ x y t = 3 ∨ twoBCount z₀ x y t = 4) :
    TwoBInEight a z₀ := by
  intro x y t hx hy hxy ht2 htx hty ht1 htx' hty' htxy
  have hc := h x y t ⟨hx, hy, hxy⟩ ⟨ht2, htx, hty, ht1, htx', hty', htxy⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have h0 : twoBCount z₀ x y t = 0 := by
    classical
    unfold twoBCount
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro w hw hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact h1 (of_decide_eq_true hd)
    · exact h2 (of_decide_eq_true hd)
    · exact h3 (of_decide_eq_true hd)
    · exact h4 (of_decide_eq_true hd)
  omega

theorem twoBInEight_of_gmsF1Type {G : Type} [Group G] [Finite G]
    {d₀ : CFSG.Blueprint.NativeSporadic.B} {a z₀ : G} (I : GMSInterfaces d₀ G)
    (hG : GMSF1Type d₀ a z₀) : TwoBInEight a z₀ :=
  twoBInEight_of_twoBCount (S365.twoBCount_cases I hG)

end CFSG.Monster.Tri.Leech
