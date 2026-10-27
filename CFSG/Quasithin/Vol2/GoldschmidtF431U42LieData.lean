module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42A0Set
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AgMem
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Equiv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv2

public section

namespace CFSG.Quasithin.H13.F431.U42

open CFSG.Quasithin CFSG.Open U42F431
open scoped Pointwise


instance : Finite u42Setting.ι.G0 := Finite.of_injective eG.symm eG.symm.injective

theorem map_T_isPGroup : IsPGroup 2 (T.map eG.toMonoidHom) :=
  (isSylowTwoOf_top_map' eG isSylow_T).2.1

theorem comap_le_T {D : Subgroup u42Setting.ι.G0} (h : D ≤ T.map eG.toMonoidHom) :
    D.comap eG.toMonoidHom ≤ T := by
  intro d hd
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 (h (show eG d ∈ D from hd))
  exact (eG.injective hse) ▸ hs

theorem f431Lie_u42 :
    F431Lie (T.map eG.toMonoidHom) u42Setting.Mb1 u42Setting.Mb2 (eG xY) (eG tY) where
  sylow := isSylowTwoOf_top_map' eG isSylow_T
  T_le₁ := by
    rw [Mb1_eq]
    exact Subgroup.map_mono (T_le_B0.trans B0_le_P1)
  T_le₂ := by
    rw [Mb2_eq]
    exact Subgroup.map_mono (T_le_B0.trans B0_le_P2)
  z_mem := Subgroup.mem_map_of_mem _ xY_mem_T
  t_mem := Subgroup.mem_map_of_mem _ tY_mem_T
  hz := (MulEquiv.orderOf_eq eG xY).trans orderOf_xY
  ht := (MulEquiv.orderOf_eq eG tY).trans orderOf_tY
  not_conj := fun h => not_isConj_x_t ((isConj_map_iff eG).1 h)
  classes := by
    intro x hx
    have hy : orderOf (eG.symm x) = 2 := (MulEquiv.orderOf_eq eG.symm x).trans hx
    rcases classes hy with h | h
    · left
      simpa using (isConj_map_iff eG).2 h
    · right
      simpa using (isConj_map_iff eG).2 h
  cent_z := by
    rw [centralizer_map, centralizer_x, Mb1_eq]
  cent_t := by
    rw [centralizer_map, Mb2_eq]
    exact Subgroup.map_mono centralizer_t_le
  center_T := by
    intro w hw hc hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.1 hw
    have hcT : ∀ s ∈ T, s * w₀ = w₀ * s := by
      intro s hs
      apply eG.injective
      simpa using hc (eG s) (Subgroup.mem_map_of_mem _ hs)
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by simp [h])
    have hx := center_T_eq hw₀ hcT hw₀1
    refine ⟨1, ?_, ?_⟩
    · rw [Mb1_eq, Mb2_eq]
      exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩
    · simp [hx]
  ag := by
    intro D hD
    have hcen := centric_of_isAGMember map_T_isPGroup hD
    have hcen' : ∀ t ∈ T, (∀ d ∈ D.comap eG.toMonoidHom, t * d = d * t) →
        t ∈ D.comap eG.toMonoidHom := by
      intro t ht hc
      show eG t ∈ D
      refine hcen (eG t) (Subgroup.mem_map_of_mem _ ht) fun d' hd' => ?_
      have := congrArg eG (hc (eG.symm d') (show eG (eG.symm d') ∈ D by simpa using hd'))
      simpa using this
    rcases ag_of_centric (comap_le_T hD.1) hcen' with h | h
    · left
      intro n hn
      rw [Mb1_eq]
      exact ⟨eG.symm n, h (map_mem_normalizer eG hn), by simp⟩
    · right
      intro n hn
      rw [Mb2_eq]
      exact ⟨eG.symm n, h (map_mem_normalizer eG hn), by simp⟩

end CFSG.Quasithin.H13.F431.U42
