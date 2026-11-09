module

public import CFSG.Quasithin.H13.U3S1347Q
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.VolIH5

public section

namespace CFSG.Quasithin.H13.U3

namespace L32Mod

open CFSG.Quasithin.H6

theorem core_fix_three : ∀ g : Γ, g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun f : Fin 8 → ZMod 2 =>
      (f 0 = 0 ∧ ∑ i, f i = 0) ∧ actF g f = f).card ≤ 4 := by
  decide +kernel

theorem sum_fix_three : ∀ g : Γ, g ^ 3 = 1 → g ≠ 1 →
    (Finset.univ.filter fun p : V3 × V3 => g • p.1 = p.1 ∧ graph g • p.2 = p.2).card ≤ 4 := by
  decide +kernel

end L32Mod

open Equiv CFSG.Quasithin.H13.A6 S6Out

@[expose] def a6SwapWord (l : List (Fin 6 × Fin 6)) : Perm (Fin 6) :=
  l.foldr (fun p r => swap p.1 p.2 * r) 1

@[expose] def a6ConjC3a : Perm (Fin 6) := swap 0 2 * swap 0 1

@[expose] def a6ConjC3b : Perm (Fin 6) := swap 0 2 * swap 0 1 * swap 3 5 * swap 3 4

@[expose] def a6ConjT3a : List (Perm (Fin 6)) := List.map a6SwapWord [
  [],
  [(2, 3)],
  [(2, 4), (3, 4)],
  [(2, 5), (3, 5), (4, 5)],
  [(1, 2)],
  [(1, 2), (2, 3)],
  [(1, 2), (2, 4), (3, 4)],
  [(1, 2), (2, 5), (3, 5), (4, 5)],
  [(1, 3), (2, 3)],
  [(1, 3)],
  [(1, 3), (2, 4)],
  [(1, 3), (2, 5), (4, 5)],
  [(1, 4), (2, 4), (3, 4)],
  [(1, 4), (3, 4)],
  [(1, 4), (2, 3), (3, 4)],
  [(1, 4), (2, 5), (3, 4), (4, 5)],
  [(1, 5), (2, 5), (3, 5), (4, 5)],
  [(1, 5), (3, 5), (4, 5)],
  [(1, 5), (2, 3), (3, 5), (4, 5)],
  [(1, 5), (2, 4), (3, 5)],
  [(0, 1), (1, 2), (2, 3)],
  [(0, 1), (1, 2), (2, 4), (3, 4)],
  [(0, 1), (1, 2), (2, 5), (3, 5), (4, 5)],
  [(0, 1), (1, 3)],
  [(0, 1), (1, 3), (2, 4)],
  [(0, 1), (1, 3), (2, 5), (4, 5)],
  [(0, 1), (1, 4), (3, 4)],
  [(0, 1), (1, 4), (2, 3), (3, 4)],
  [(0, 1), (1, 4), (2, 5), (3, 4), (4, 5)],
  [(0, 1), (1, 5), (3, 5), (4, 5)],
  [(0, 1), (1, 5), (2, 3), (3, 5), (4, 5)],
  [(0, 1), (1, 5), (2, 4), (3, 5)],
  [(0, 2), (1, 3), (2, 4), (3, 4)],
  [(0, 2), (1, 3), (2, 5), (3, 5), (4, 5)],
  [(0, 2), (1, 4), (2, 3)],
  [(0, 2), (1, 4), (2, 5), (3, 5)],
  [(0, 2), (1, 5), (2, 3), (4, 5)],
  [(0, 2), (1, 5), (2, 4), (3, 4), (4, 5)],
  [(0, 3), (1, 4), (2, 5)],
  [(0, 3), (1, 5), (2, 4), (4, 5)]]

@[expose] def a6ConjT3b : List (Perm (Fin 6)) := List.map a6SwapWord [
  [],
  [(4, 5)],
  [(2, 3)],
  [(2, 3), (4, 5)],
  [(2, 4), (3, 4)],
  [(2, 4), (3, 4), (4, 5)],
  [(2, 5), (3, 5), (4, 5)],
  [(2, 5), (3, 5)],
  [(1, 2)],
  [(1, 2), (4, 5)],
  [(1, 2), (2, 3)],
  [(1, 2), (2, 3), (4, 5)],
  [(1, 2), (2, 4), (3, 4)],
  [(1, 2), (2, 4), (3, 4), (4, 5)],
  [(1, 2), (2, 5), (3, 5), (4, 5)],
  [(1, 2), (2, 5), (3, 5)],
  [(1, 3), (2, 3)],
  [(1, 3), (2, 3), (4, 5)],
  [(1, 3)],
  [(1, 3), (4, 5)],
  [(1, 3), (2, 4)],
  [(1, 3), (2, 4), (4, 5)],
  [(1, 3), (2, 5), (4, 5)],
  [(1, 3), (2, 5)],
  [(1, 4), (2, 4), (3, 4)],
  [(1, 4), (2, 4), (3, 4), (4, 5)],
  [(1, 4), (3, 4)],
  [(1, 4), (3, 4), (4, 5)],
  [(1, 4), (2, 3), (3, 4)],
  [(1, 4), (2, 3), (3, 4), (4, 5)],
  [(1, 4), (2, 5), (3, 4), (4, 5)],
  [(1, 4), (2, 5), (3, 4)],
  [(1, 5), (2, 5), (3, 5), (4, 5)],
  [(1, 5), (2, 5), (3, 5)],
  [(1, 5), (3, 5), (4, 5)],
  [(1, 5), (3, 5)],
  [(1, 5), (2, 3), (3, 5), (4, 5)],
  [(1, 5), (2, 3), (3, 5)],
  [(1, 5), (2, 4), (3, 5)],
  [(1, 5), (2, 4), (3, 5), (4, 5)]]

theorem a6_three_conj : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → σ ≠ 1 →
    (∃ τ ∈ a6ConjT3a, σ = τ * a6ConjC3a * τ⁻¹) ∨ ∃ τ ∈ a6ConjT3b, σ = τ * a6ConjC3b * τ⁻¹ := by
  decide +kernel

theorem fixCount_singleton_conj (τ x : Perm (Fin 6)) : fixCount [τ * x * τ⁻¹] = fixCount [x] := by
  have hinj : ∀ a b : P6, InW4 a → InW4 b → act4f τ a = act4f τ b → a = b := by
    intro a b ha hb hab
    rw [← act4f_one a ha, ← act4f_one b hb, ← inv_mul_cancel τ, act4f_mul, act4f_mul, hab]
  have hperm : (w4List.map (act4f τ)).Perm w4List := by
    refine (List.perm_ext_iff_of_nodup (w4List_nodup.map_on fun a ha b hb hab =>
      hinj a b ((mem_w4List a).2 ha) ((mem_w4List b).2 hb) hab) w4List_nodup).2 fun a => ?_
    rw [List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (mem_w4List _).1 (act4f_mem τ ((mem_w4List b).2 hb))
    · intro ha
      have ha' := (mem_w4List a).2 ha
      refine ⟨act4f τ⁻¹ a, (mem_w4List _).1 (act4f_mem _ ha'), ?_⟩
      rw [← act4f_mul, mul_inv_cancel, act4f_one a ha']
  unfold fixCount
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter, ← hperm.countP_eq,
    List.countP_map]
  refine List.countP_congr fun w hw => ?_
  have hw' := (mem_w4List w).2 hw
  have hτ : act4f τ⁻¹ (act4f τ w) = w := by rw [← act4f_mul, inv_mul_cancel, act4f_one w hw']
  simp only [Function.comp_apply, List.mem_singleton, forall_eq, decide_eq_true_eq]
  rw [act4f_mul, act4f_mul, hτ]
  exact ⟨hinj _ _ (act4f_mem x hw') hw', fun h => by rw [h]⟩

theorem a6_fix_three : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → σ ≠ 1 → Perm.sign σ = 1 →
    fixCount [σ] * fixCount [phi (cc⁻¹ * σ * cc)] ≤ 4 := by
  have hb : fixCount [a6ConjC3a] * fixCount [phi (cc⁻¹ * a6ConjC3a * cc)] ≤ 4 ∧
      fixCount [a6ConjC3b] * fixCount [phi (cc⁻¹ * a6ConjC3b * cc)] ≤ 4 := by
    decide +kernel
  have hc : ∀ τ t : Perm (Fin 6), fixCount [τ * t * τ⁻¹] *
      fixCount [phi (cc⁻¹ * (τ * t * τ⁻¹) * cc)] = fixCount [t] * fixCount [phi (cc⁻¹ * t * cc)] := by
    intro τ t
    have e : cc⁻¹ * (τ * t * τ⁻¹) * cc =
        (cc⁻¹ * τ * cc) * (cc⁻¹ * t * cc) * (cc⁻¹ * τ * cc)⁻¹ := by group
    rw [e, map_mul, map_mul, map_inv, fixCount_singleton_conj, fixCount_singleton_conj]
  intro σ h3 h1 _
  rcases a6_three_conj σ h3 h1 with ⟨τ, _, rfl⟩ | ⟨τ, _, rfl⟩
  · rw [hc]
    exact hb.1
  · rw [hc]
    exact hb.2

end CFSG.Quasithin.H13.U3
