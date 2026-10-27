module

public import CFSG.Sporadic.Co1Patterson.GlueFiber

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

theorem additive_eq_sum {n : ℕ} {D : (Fin n → ZMod 2) → ZMod 2}
    (hD : ∀ u v, D (u + v) = D u + D v) (v : Fin n → ZMod 2) :
    D v = ∑ j, v j * D (Pi.single j 1) := by
  have h := ((AddMonoidHom.mk' D hD).toZModLinearMap 2).pi_apply_eq_sum_univ v
  simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  funext i
  rw [Pi.single_apply]
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [h, h.symm]

theorem bil₀_apply (u v : Fin 8 → ZMod 2) :
    bil₀ u v = ∑ i : Fin 4, (u (Fin.castAdd 4 i) * v (Fin.natAdd 4 i) +
      v (Fin.castAdd 4 i) * u (Fin.natAdd 4 i)) := by
  simp only [bil₀, q₀, QuadraticMap.polar, sum_apply,
    QuadraticMap.linMulLin_apply, LinearMap.proj_apply, Pi.add_apply]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem nondeg_bil₀ : Nondeg bil₀ where
  exists_eq_one := ⟨Pi.single 0 1, Pi.single 4 1, by
    rw [bil₀_apply, Fin.sum_univ_four]
    decide⟩
  exists_eq D hD := by
    refine ⟨![D (Pi.single 4 1), D (Pi.single 5 1), D (Pi.single 6 1), D (Pi.single 7 1),
      D (Pi.single 0 1), D (Pi.single 1 1), D (Pi.single 2 1), D (Pi.single 3 1)],
      fun v => ?_⟩
    rw [additive_eq_sum hD v, bil₀_apply, Fin.sum_univ_eight, Fin.sum_univ_four]
    simp only [Fin.castAdd, Fin.natAdd, Fin.castLE]
    norm_num
    ring

end CFSG.Sporadic.Co1Patterson
