module

public import CFSG.Quasithin.Vol2.GoldschmidtF45RuLoc

public section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

theorem encard_neighborSet_smul {V : Type*} {H : Type*} [Group H] [MulAction H V]
    {Γ : SimpleGraph V} [GraphAction H Γ] (g : H) (v : V) :
    (Γ.neighborSet (g • v)).encard = (Γ.neighborSet v).encard := by
  have : Γ.neighborSet (g • v) = (fun w : V => g • w) '' Γ.neighborSet v := by
    ext w
    constructor
    · intro h
      refine ⟨g⁻¹ • w, ?_, smul_inv_smul g w⟩
      have := (GraphAction.adj_smul g⁻¹ (g • v) w).mpr h
      simpa using this
    · rintro ⟨w', hw', rfl⟩
      exact (GraphAction.adj_smul g v w').mpr hw'
  rw [this]
  exact Function.Injective.encard_image (f := fun w : V => g • w) (MulAction.injective g) _

theorem two_le_encard {V : Type*} {Γ : SimpleGraph V} {a w₀ w₁ : V} (h0 : Γ.Adj a w₀)
    (h1 : Γ.Adj a w₁) (hne : w₀ ≠ w₁) : 2 ≤ (Γ.neighborSet a).encard := by
  have : ({w₀, w₁} : Set V) ⊆ Γ.neighborSet a := by
    intro x hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  have h2 := Set.encard_le_encard this
  rwa [Set.encard_pair hne] at h2

theorem ofCode_zero : ofCode 0 = (Sum.inl 0 : Vtx) := ofCode_inl (by norm_num)

theorem ofCode_1755 : ofCode 1755 = (Sum.inr 0 : Vtx) := ofCode_inr (by norm_num) (by norm_num)

end CFSG.Quasithin.H13.F45Ru
