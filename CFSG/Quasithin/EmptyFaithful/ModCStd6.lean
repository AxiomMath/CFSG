module

public import CFSG.Quasithin.EmptyFaithful.ModCModel6

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

theorem std_position6 (D : Subgroup (Perm (Fin 6))) (hDe : ∀ d ∈ D, sign d = 1) (hD8 : Nat.card D = 8)
    (z v : PermMod 6) (hz : ∑ i, Multiplicative.toAdd z i = 0) (hz1 : z ≠ 1)
    (hv : ∑ i, Multiplicative.toAdd v i = 0) (hv1 : v ≠ 1) (hvz : v ≠ z)
    (hDV : ∀ d ∈ D, permAct 6 d z = z ∧ (permAct 6 d v = v ∨ permAct 6 d v = z * v))
    (hwt : wt v = wt z ∨ wt (z * v) = wt z) :
    ∃ τ : Perm (Fin 6), permAct 6 τ z = M6.a ∧
      (permAct 6 τ v = M6.w ∨ permAct 6 τ v = M6.a * M6.w) := by
  have hD0le : M6.D0 ≤ alternatingGroup (Fin 6) := fun s hs =>
    Perm.mem_alternatingGroup.mpr (M6.D0_even s hs)
  have hDle : D ≤ alternatingGroup (Fin 6) := fun d hd => Perm.mem_alternatingGroup.mpr (hDe d hd)
  obtain ⟨τ, hτ⟩ := exists_conj_sylow fac_alt6 hDle hD0le hD8 M6.D0_card
  have hgens : ∀ s ∈ M6.gens, τ⁻¹ * s * τ ∈ D := fun s hs =>
    (hτ s).1 (Subgroup.subset_closure hs)
  have hconj : ∀ (s : Perm (Fin 6)) (y : PermMod 6),
      permAct 6 s (permAct 6 τ y) = permAct 6 τ (permAct 6 (τ⁻¹ * s * τ) y) := by
    intro s y
    rw [permAct_conj_inv_apply, permAct_inv_apply_self']
  have hinj := (permAct 6 τ).injective
  have hz' : M6.CondZ (permAct 6 τ z) := by
    refine ⟨by rw [sum_permAct]; exact hz, fun h => hz1 (hinj (by rw [h, map_one])), fun s hs => ?_⟩
    rw [hconj, (hDV _ (hgens s hs)).1]
  have hv' : M6.CondV (permAct 6 τ z) (permAct 6 τ v) := by
    refine ⟨by rw [sum_permAct]; exact hv, fun h => hv1 (hinj (by rw [h, map_one])),
      fun h => hvz (hinj h), fun s hs => ?_, ?_⟩
    · rw [hconj, ← map_mul]
      rcases (hDV _ (hgens s hs)).2 with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rw [h])
    · rw [wt_permAct, wt_permAct, ← map_mul, wt_permAct]
      exact hwt
  exact ⟨τ, M6.classify _ hz' _ hv'⟩

end CFSG.Quasithin.ModC
