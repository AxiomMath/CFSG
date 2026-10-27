module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F1Cartan

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SzN20

section Rank2

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem rank_two_false {Hs Ls Ts Ys Ms S : Subgroup Ω}
    (hLH : Ls ≤ Hs) (hTH : Ts ≤ Hs) (hO2 : pCoreOf 2 Hs = ⊥)
    (hS : IsSylowTwoOf S Ls) (hS1 : S ≠ ⊥) (hTS : Ts ≤ Subgroup.normalizer (S : Set Ω))
    (hYL : Ys ≤ Ls) (hSY : S ≤ Subgroup.normalizer (Ys : Set Ω)) (hYs : Group.IsSolvable ↥Ys)
    (hmin : ∀ K' : Subgroup Ω, Ys ⊔ Ts ≤ K' → K' ≤ Hs → K' ≠ Hs → K' ≤ Ms)
    (hθ : ∀ x ∈ Ms, orderOf x = 3 → x ∈ Ys)
    (hY3 : ∀ E : Subgroup Ω, E ≤ Ys → IsPGroup 3 E → Nat.card E ≤ 3)
    (hex : ∃ y ∈ Ys, orderOf y = 3)
    (ha : ∀ R : Subgroup Ω, S ≤ R → R ≤ Ls → Group.IsSolvable ↥R →
      R ≤ Subgroup.normalizer (S : Set Ω))
    (hb : (∃ y ∈ Subgroup.normalizer (S : Set Ω) ⊓ Ls, orderOf y = 3) →
      ∃ E : Subgroup Ω, E ≤ Subgroup.normalizer (S : Set Ω) ⊓ Ls ∧ IsPGroup 3 E ∧
        (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9) : False := by
  obtain ⟨y, hyY, hy3⟩ := hex
  have hSs : Group.IsSolvable ↥S := F1.isSolvable_of_isPGroup_two hS.2.1
  have hRs : Group.IsSolvable ↥(Ys ⊔ S) := F1.isSolvable_sup_of_le_normalizer hYs hSs hSY
  have hRB : Ys ⊔ S ≤ Subgroup.normalizer (S : Set Ω) :=
    ha _ le_sup_right (sup_le hYL hS.1) hRs
  have hYB : Ys ≤ Subgroup.normalizer (S : Set Ω) ⊓ Ls := le_inf (le_sup_left.trans hRB) hYL
  have hPH : Subgroup.normalizer (S : Set Ω) ⊓ Ls ⊔ Ts ≤ Hs :=
    sup_le (inf_le_right.trans hLH) hTH
  have hPYT : Ys ⊔ Ts ≤ Subgroup.normalizer (S : Set Ω) ⊓ Ls ⊔ Ts :=
    sup_le_sup_right hYB Ts
  have hPne : Subgroup.normalizer (S : Set Ω) ⊓ Ls ⊔ Ts ≠ Hs := by
    intro hP
    apply hS1
    have hnorm : Hs ≤ Subgroup.normalizer (S : Set Ω) := by
      rw [← hP]
      exact sup_le inf_le_left hTS
    have := le_pCoreOf_of_le_normalizer 2 (hS.1.trans hLH) hnorm hS.2.1
    rw [hO2] at this
    exact le_bot_iff.mp this
  have hPM := hmin _ hPYT hPH hPne
  have hyB : y ∈ Subgroup.normalizer (S : Set Ω) ⊓ Ls := hYB hyY
  obtain ⟨E, hEB, hE3, hEexp, hEcard⟩ := hb ⟨y, hyB, hy3⟩
  have hF3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEY : E ≤ Ys := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Ys.one_mem
    · have hxo : orderOf x = 3 := orderOf_eq_prime (hEexp x hx) hx1
      exact hθ x (hPM (Subgroup.mem_sup_left (hEB hx))) hxo
  have := hY3 E hEY hE3
  omega

end Rank2

end SzN20

end CFSG.Quasithin
