module

public import CFSG.Milestones.ASVolI.A3Spor.Core
public import CFSG.Quasithin.H13.NQCatT513Lat
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4SpA
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

theorem burnsideA315s_false_of_list {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤) {Y : ℕ → Subgroup Γ} {L : Array ℕ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ L.size, Z = memberOrTop L.size Y j)
    (hcard : ∀ j < L.size, Nat.card ↥(Y j) = L[j]! * Nat.card ↥S)
    (hL : ∀ j < L.size, L[j]! = 1 ∨ 3 ∣ L[j]!) {N : ℕ} (hΓ : Nat.card Γ = N * Nat.card ↥S)
    (hN : 3 ∣ N) : ∀ S' B : Subgroup Γ, ¬ burnsideA315x_Config Γ S' B := by
  intro S' B hc
  refine burnsideA315s_false_of_overgroups hS (fun Z hZ _ m hm => ?_) hc
  rcases CFSG.Quasithin.H13.NQCat.T513P.index_of_list hall hcard hZ hm with ⟨j, hj, rfl⟩ | h
  · exact hL j hj
  · have hpos : 0 < Nat.card ↥S := Nat.card_pos
    rw [hΓ] at h
    rw [← Nat.eq_of_mul_eq_mul_right hpos h]
    exact Or.inr hN

theorem burnsideA315s_false_of_indexThree {Γ : Type} [Group Γ] [Finite Γ]
    (h : CFSG.Quasithin.H.NPrimeHall.IndexThree (⊤ : Subgroup Γ)) :
    ∀ S B : Subgroup Γ, ¬ burnsideA315x_Config Γ S B := by
  intro S B hc
  refine burnsideA315s_false_of_overgroups hc.sylow (fun Z hZ _ m hm => ?_) hc
  have hS : CFSG.Quasithin.IsSylowIn 2 S ⊤ := ⟨hc.sylow.1, hc.sylow.2.1, hc.sylow.2.2⟩
  have hpos : 0 < Nat.card ↥S := Nat.card_pos
  rcases h S Z hS hZ le_top with h1 | h1
  · left
    rw [hm] at h1
    have : m * Nat.card ↥S = 1 * Nat.card ↥S := by rw [h1, one_mul]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  · right
    rw [hm] at h1
    exact Nat.dvd_of_mul_dvd_mul_right hpos h1

end CFSG.ASVolI
