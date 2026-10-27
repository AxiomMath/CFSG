module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.A1cKlein

public section

namespace CFSG.Quasithin

open Equiv

namespace F53.Stellmacher

namespace S35.N9

@[expose] def step (gens : List (Perm (Fin 5))) (S : Finset (Fin 5)) : Finset (Fin 5) :=
  S ∪ S.biUnion fun s => (gens.map fun g => g s).toFinset

@[expose] def reach (gens : List (Perm (Fin 5))) : ℕ → Finset (Fin 5)
  | 0 => {0}
  | n + 1 => step gens (reach gens n)

theorem reach_mem {H : Subgroup (Perm (Fin 5))} {gens : List (Perm (Fin 5))}
    (hg : ∀ g ∈ gens, g ∈ H) :
    ∀ n, ∀ r ∈ reach gens n, ∃ h ∈ H, h 0 = r := by
  intro n
  induction n with
  | zero =>
    intro r hr
    simp only [reach, Finset.mem_singleton] at hr
    exact ⟨1, one_mem H, by simp [hr]⟩
  | succ n ih =>
    intro r hr
    simp only [reach, step, Finset.mem_union, Finset.mem_biUnion, List.mem_toFinset,
      List.mem_map] at hr
    rcases hr with hr | ⟨s, hs, g, hgm, rfl⟩
    · exact ih r hr
    · obtain ⟨h, hh, rfl⟩ := ih s hs
      exact ⟨g * h, mul_mem (hg g hgm) hh, rfl⟩

theorem isPretransitive_of_reach {H : Subgroup (Perm (Fin 5))} {gens : List (Perm (Fin 5))}
    (hg : ∀ g ∈ gens, g ∈ H) {n : ℕ} (hr : reach gens n = Finset.univ) :
    MulAction.IsPretransitive H (Fin 5) := by
  have key : ∀ a : Fin 5, ∃ h ∈ H, h 0 = a := fun a =>
    reach_mem hg n a (hr ▸ Finset.mem_univ a)
  refine ⟨fun a b => ?_⟩
  obtain ⟨h1, hh1, e1⟩ := key a
  obtain ⟨h2, hh2, e2⟩ := key b
  refine ⟨⟨h2 * h1⁻¹, mul_mem hh2 (inv_mem hh1)⟩, ?_⟩
  show (h2 * h1⁻¹) a = b
  rw [← e1, ← e2]
  simp

theorem eq_top_of_reach {H : Subgroup (Perm (Fin 5))} {gens : List (Perm (Fin 5))}
    (hg : ∀ g ∈ gens, g ∈ H) {n : ℕ} (hr : reach gens n = Finset.univ) {a b : Fin 5}
    (hab : a ≠ b) (hs : swap a b ∈ H) : H = ⊤ := by
  have := isPretransitive_of_reach hg hr
  have : MulAction.IsPreprimitive H (Fin 5) :=
    MulAction.IsPreprimitive.of_prime_card (by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem this _
    (Perm.swap_isSwap_iff.mpr hab) hs

end S35.N9

end F53.Stellmacher

end CFSG.Quasithin
