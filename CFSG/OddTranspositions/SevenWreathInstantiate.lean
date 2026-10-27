module

public import CFSG.OddTranspositions.SevenWreathHelpers
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_localSecond_of_wreathData (hS : Setup G D) {M : Subgroup G}
    (W : WreathData G D M) {u : G} (hu : u ∈ D) {i j : Fin W.r} (hij : i ≠ j)
    (hπ : W.π u = Equiv.swap i j)
    {s₁ s₂ s₃ : G} (hs1 : s₁ ∈ W.S i) (hs2 : s₂ ∈ W.S i) (hs3 : s₃ ∈ W.S i)
    (hs1sq : s₁ * s₁ = 1) (hs2sq : s₂ * s₂ = 1) (hs3sq : s₃ * s₃ = 1)
    (hs12 : Commute s₁ s₂) (hne12 : s₁ ≠ s₂)
    (hodd13 : Odd (orderOf (s₁ * s₃))) (hgt13 : 1 < orderOf (s₁ * s₃))
    (hodd23 : Odd (orderOf (s₂ * s₃))) (hgt23 : 1 < orderOf (s₂ * s₃))
    (hoddg : Odd (orderOf (s₁ * s₂ * s₃))) (hgtg : 1 < orderOf (s₁ * s₂ * s₃)) :
    ¬ LocalSecond D := by
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hAB : ∀ a ∈ W.S i, u * a * u ∈ W.S j := by
    intro a ha
    have h := W.conj_mem u ha
    simpa [hπ, huinv] using h
  exact not_localSecond_of_wreath_data hS hu hAB (W.inf_eq_bot hij)
    (fun a ha b hb => W.commute_of_ne hij ha hb)
    hs1 hs2 hs3 hs1sq hs2sq hs3sq hs12 hne12 hodd13 hgt13 hodd23 hgt23 hoddg hgtg

end CFSG.OddTranspositions
