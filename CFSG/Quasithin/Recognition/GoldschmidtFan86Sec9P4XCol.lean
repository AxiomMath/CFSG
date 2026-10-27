module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4XArc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P4X

theorem exists_arc_through (F : FanTree Γ G) {α β ξ a : V} {x : G} (hαβ : Γ.Adj α β)
    (hαξ : Γ.Adj α ξ) (hξa : Γ.Adj ξ a) (hαa : α ≠ a) (hξβ : ξ ≠ β) (hxβ : x • β = β)
    (hxα : x • α ≠ α) :
    ∃ Q : Arc Γ 4, Q.vert 0 = α ∧ Q.vert 1 = β ∧ Q.vert 2 = x • α ∧ Q.vert 3 = x • ξ ∧
      Q.vert 4 = x • a := by
  have h2 : Γ.Adj β (x • α) := by
    have := (F.adj_smul x α β).2 hαβ
    rw [hxβ] at this
    exact this.symm
  refine ⟨mkArc4 α β (x • α) (x • ξ) (x • a) hαβ h2 ((F.adj_smul x _ _).2 hαξ)
    ((F.adj_smul x _ _).2 hξa) hxα.symm ?_ (fun h => hαa (MulAction.injective x h)),
    mkArc4_vert_zero, mkArc4_vert_one, mkArc4_vert_two, mkArc4_vert_three, mkArc4_vert_four⟩
  intro h
  exact hξβ (MulAction.injective x (h.symm.trans hxβ.symm))

theorem isBetaSet_of_collar {L : ZLab Γ G} {α : V} (D : D10Set L α) {x : G} {η' : V}
    (hβ : x • D.beta 2 = D.beta 2) (h3 : orderOf x = 3) (hY : D.IsYPair η')
    (hinv : (D.y η' 0)⁻¹ * x * D.y η' 0 = x⁻¹)
    (hc : ∀ m, m ≤ 2 → (D.P 2).vert (m + 2) = x • (D.P 0).vert m) : IsBetaSet D x η' := by
  refine ⟨hβ, h3, hY, hinv, fun m hm => ?_⟩
  have hx3 : x ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hx2 : (x ^ 2)⁻¹ = x := by
    have : x ^ 2 * x = 1 := by rw [← pow_succ]; exact hx3
    exact inv_eq_of_mul_eq_one_right this
  show (x ^ 2)⁻¹ • (if m = 0 then D.beta 2 else (D.P 0).vert (m - 1)) = (D.P 2).vert (m + 1)
  rw [hx2]
  by_cases h0 : m = 0
  · subst h0
    simp only [↓reduceIte]
    exact hβ
  · simp only [h0, ↓reduceIte]
    have := hc (m - 1) (by omega)
    rw [show m - 1 + 2 = m + 1 by omega] at this
    exact this.symm

end P4X

end CFSG.Quasithin.Fan86
