module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameReal
import TauCeti.LinearAlgebra.Reflection

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

theorem coroot_ne_zero (m : Fin 6) (t : Root m) : coroot m t ≠ 0 := by
  intro h
  have h2 := root_coroot m t
  rw [h, map_zero] at h2
  exact absurd h2 (by decide)

theorem reflection_coroot (m : Fin 6) (t : Root m) :
    reflection m t (coroot m t) = -coroot m t :=
  Module.reflection_apply_self (root_coroot m t)

theorem reflection_reflection (m : Fin 6) (t : Root m) (v : V m) :
    reflection m t (reflection m t v) = v :=
  Module.involutive_reflection (root_coroot m t) v

theorem det_reflection (m : Fin 6) (t : Root m) : LinearEquiv.det (reflection m t) = -1 :=
  Module.det_reflection (root_coroot m t)

private theorem eq_zero_of_neg_eq {m : Fin 6} {v : V m} (h : -v = v) : v = 0 := by
  funext k
  have key : ∀ x : ZMod 3, -x = x → x = 0 := by decide
  exact key _ (congrFun h k)

private theorem coroot_zero_ne_smul :
    ∀ t u : Root 0, t ≠ u → ∀ b : ZMod 3, coroot 0 t ≠ b • coroot 0 u := by
  decide +kernel

theorem rawInsideMoved_excRaw (m : Fin 6) : RawInsideMoved (excRaw m) := by
  intro c hc
  obtain ⟨⟨U, ⟨t, ht⟩, -⟩, -⟩ := hc
  have hst : reflection m t ∈ weyl m c := Subgroup.subset_closure ⟨t, ht, rfl⟩
  have hvt : coroot m t ∈ inside m c := Submodule.subset_span ⟨t, ht, rfl⟩
  change ∃ g ∈ normalizerGroup m c, ∃ v ∈ inside m c, g v ≠ v
  unfold normalizerGroup
  split_ifs with hB
  · obtain ⟨hm0, hcard⟩ := hB
    obtain ⟨u, hu, hut⟩ := Finset.exists_mem_ne (by omega : 1 < Finset.card c) t
    have hsu : reflection m u ∈ weyl m c := Subgroup.subset_closure ⟨u, hu, rfl⟩
    refine ⟨reflection m t * reflection m u,
      Subgroup.mem_inf.mpr ⟨mul_mem hst hsu, ?_⟩, coroot m t, hvt, ?_⟩
    · have hd : LinearEquiv.det (reflection m t * reflection m u) = 1 :=
        calc LinearEquiv.det (reflection m t * reflection m u)
            = LinearEquiv.det (reflection m t) * LinearEquiv.det (reflection m u) :=
              map_mul _ _ _
          _ = (-1) * (-1) := congrArg₂ (· * ·) (det_reflection m t) (det_reflection m u)
          _ = 1 := by simp
      exact MonoidHom.mem_ker.mpr hd
    · intro h
      change reflection m t (reflection m u (coroot m t)) = coroot m t at h
      have h1 := congrArg (reflection m t) h
      rw [reflection_reflection, reflection_coroot, reflection_apply] at h1
      have h2 : coroot m t = (2 * root m u (coroot m t)) • coroot m u := by
        funext k
        have hk := congrFun h1 k
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hk ⊢
        have key : ∀ x a y : ZMod 3, x - a * y = -x → x = 2 * a * y := by decide
        exact key _ _ _ hk
      have hm : m = 0 := Fin.ext hm0
      subst hm
      exact coroot_zero_ne_smul t u (Ne.symm hut) _ h2
  · refine ⟨reflection m t, hst, coroot m t, hvt, ?_⟩
    rw [reflection_coroot]
    exact fun h => coroot_ne_zero m t (eq_zero_of_neg_eq h)

end CFSG.StandardType.GGQ2Frame.ExcRaw

end
