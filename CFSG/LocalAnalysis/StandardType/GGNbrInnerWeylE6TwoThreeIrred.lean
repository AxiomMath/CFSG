module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameIrred
import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open TableBExc.E6Three E6TwoPilot

theorem ggE6TwoIrred_normalizer_of_action {M : Type} [Group M] {G : Type} [Group G]
    (f : M →* G) (n : G) (φ : M ≃* M) (h : ∀ m, n * f m * n⁻¹ = f (φ m)) :
    n ∈ Subgroup.normalizer (f.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨φ v, (h v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨φ.symm v, ?_⟩
    have h1 := h (φ.symm v)
    rw [φ.apply_symm_apply] at h1
    rw [hv] at h1
    have h2 := congrArg (fun y => n⁻¹ * y * n) h1
    simpa [mul_assoc] using h2

theorem ggE6TwoIrred_refl_invol : ∀ (i : Fin 4) (v : Multiplicative (Fin 4 → ZMod 3)),
    reflE6Two i (reflE6Two i v) = v := by
  decide +kernel

@[expose] noncomputable def ggE6TwoIrred_reflEquiv (i : Fin 4) :
    Multiplicative (Fin 4 → ZMod 3) ≃* Multiplicative (Fin 4 → ZMod 3) :=
  MulEquiv.ofBijective (reflE6Two i) ⟨fun a b h => by
      have := congrArg (reflE6Two i) h
      simpa only [ggE6TwoIrred_refl_invol] using this,
    fun b => ⟨reflE6Two i b, ggE6TwoIrred_refl_invol i b⟩⟩

theorem ggE6TwoIrred_refl_eq_update (i : Fin 4) (v : Fin 4 → ZMod 3) :
    v - reflFunE6Two i v • Pi.single i 1 = Function.update v i (2 * v i) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, reflFunE6Two_apply,
      Function.update_self]
    generalize v j = a
    revert a
    decide
  · simp [reflFunE6Two_apply, Function.update_of_ne hj, Pi.single_eq_of_ne hj]

section Main


theorem ggSCWeylIrred_adjoint_E6_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    GGSCWeylIrred 3 4 (adjointGroup .E6 K) := by
  haveI : CharP K 2 := charP_two_of_card (K := K) (m := 1) (by rw [pow_one]; exact hK)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  intro E hE h4 _ _
  obtain ⟨c, hc⟩ := exists_conj_eq_range_torusE6Two h2 hK hE h4
  have hfull : ∀ i k : Fin 4, msCol i k ≠ 0 := by decide +kernel
  have hB : GGWeylIrred (torusE6Two (K := K) h2).range := by
    refine ggWeylIrred_range_of_frame (torusE6Two h2) (2 : ZMod 3) (by decide) (fun i => ?_) ?_
    · refine ⟨nE6Two i, ggE6TwoIrred_normalizer_of_action (torusE6Two h2) (nE6Two i)
        (ggE6TwoIrred_reflEquiv i) (fun m => ?_), fun v => ?_⟩
      · have h := nE6Two_conj_torus h2 i (Multiplicative.toAdd m)
        rwa [ofAdd_toAdd m] at h
      · rw [nE6Two_conj_torus h2 i v, ggE6TwoIrred_refl_eq_update]
    · intro T hTinv hscT ⟨i₀, hi₀⟩
      have hsN : sE6Two K ∈ Subgroup.normalizer ((torusE6Two (K := K) h2).range : Set _) :=
        ggE6TwoIrred_normalizer_of_action (torusE6Two h2) (sE6Two K) msAut
          (fun m => torusE6Two_msAut h2 m)
      have hmem := hTinv (sE6Two K) hsN _ hi₀ _
        (torusE6Two_msAut h2 (Multiplicative.ofAdd (Pi.single i₀ (1 : ZMod 3))))
      rw [msAut_ofAdd, msFun_single, one_smul] at hmem
      intro k
      exact frameTorus_single_mem_of_scaling (2 : ZMod 3) (by decide) T hscT hmem (i := k)
        (hfull i₀ k)
  have hEE : (torusE6Two (K := K) h2).range.map (MulAut.conj c).symm.toMonoidHom = E := by
    rw [← hc, Subgroup.map_map]
    have hcomp : (MulAut.conj c).symm.toMonoidHom.comp (MulAut.conj c).toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rw [← hEE]
  exact ggWeylIrred_map (MulAut.conj c).symm hB

end Main

end CFSG.StandardType

end
