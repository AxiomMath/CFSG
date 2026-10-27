module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.PartOne.FourSeed

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_eq_bot_of_double {E Y : Subgroup G} (hE : ⁅E, E⁆ = E)
    (h : ⁅⁅Y, E⁆, E⁆ = ⊥) : ⁅Y, E⁆ = ⊥ := by
  have h1 : ⁅⁅E, Y⁆, E⁆ = ⊥ := by rw [Subgroup.commutator_comm E Y]; exact h
  have h2 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := Y) h1 h
  rwa [hE, Subgroup.commutator_comm] at h2

theorem mem_normalizer_commutator {X Y : Subgroup G} {g : G} (hX : g ∈ normalizer (X : Set G))
    (hY : g ∈ normalizer (Y : Set G)) : g ∈ normalizer (⁅X, Y⁆ : Subgroup G) := by
  rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    (mem_normalizer_iff_map_conj_eq).mp hX, (mem_normalizer_iff_map_conj_eq).mp hY]

theorem exists_stable_commutator [Finite G] {E A : Subgroup G} (hE : ⁅E, E⁆ = E)
    (hAE : A ≤ normalizer (E : Set G)) :
    ∀ Y : Subgroup G, E ≤ normalizer (Y : Set G) → A ≤ normalizer (Y : Set G) → ⁅Y, E⁆ ≠ ⊥ →
      ∃ S : Subgroup G, S ≤ Y ∧ S ≠ ⊥ ∧ E ≤ normalizer (S : Set G) ∧
        A ≤ normalizer (S : Set G) ∧ ⁅S, E⁆ = S := by
  intro Y
  induction Y using WellFoundedLT.induction with
  | _ Y ih =>
    intro hEY hAY hne
    have hle : ⁅Y, E⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_left.mp hEY
    by_cases heq : ⁅Y, E⁆ = Y
    · exact ⟨Y, le_rfl, fun h => hne (heq.trans h), hEY, hAY, heq⟩
    have hlt : ⁅Y, E⁆ < Y := lt_of_le_of_ne hle heq
    have hES : E ≤ normalizer ((⁅Y, E⁆ : Subgroup G) : Set G) := fun e he =>
      mem_normalizer_commutator (hEY he) (Subgroup.le_normalizer he)
    have hAS : A ≤ normalizer ((⁅Y, E⁆ : Subgroup G) : Set G) := fun a ha =>
      mem_normalizer_commutator (hAY ha) (hAE ha)
    by_cases h2 : ⁅⁅Y, E⁆, E⁆ = ⊥
    · exact absurd (commutator_eq_bot_of_double hE h2) hne
    obtain ⟨S, hSY, hS1, hSE, hSA, hSS⟩ := ih ⁅Y, E⁆ hlt hES hAS h2
    exact ⟨S, hSY.trans hle, hS1, hSE, hSA, hSS⟩

end CFSG.RankThree.PartOne.FourSeed
