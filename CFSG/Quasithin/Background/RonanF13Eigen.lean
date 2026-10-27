module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.RonanF13

theorem iSup_eigenspace_eq_top_of_pow {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {W : Type*} [AddCommGroup W] [Module F W] (g : Module.End F W)
    (hg : g ^ (Fintype.card F - 1) = 1) :
    ⨆ μ : F, Module.End.eigenspace g μ = ⊤ := by
  classical
  have hcard : 1 < Fintype.card F := Fintype.one_lt_card
  have hM : 0 < Fintype.card F - 1 := by omega
  have hmem : ∀ (a : Fˣ) (w : W),
      (∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) • g) ^ i : Module.End F W) w ∈
        Module.End.eigenspace g (a : F)⁻¹ := by
    intro a w
    have ha : (a : F) ≠ 0 := a.ne_zero
    have hx : ((a : F) • g) ^ (Fintype.card F - 1) = 1 := by
      rw [smul_pow, FiniteField.pow_card_sub_one_eq_one (a : F) ha, hg, one_smul]
    have hId : (1 - (a : F) • g) *
        (∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) • g) ^ i) = 0 := by
      rw [mul_neg_geom_sum, hx, sub_self]
    have h2 := LinearMap.congr_fun hId w
    rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.smul_apply, sub_eq_zero] at h2
    have key : ∀ v : W, v = (a : F) • g v → g v = (a : F)⁻¹ • v := by
      intro v hv
      calc g v = (a : F)⁻¹ • (a : F) • g v := (inv_smul_smul₀ ha _).symm
        _ = (a : F)⁻¹ • v := by rw [← hv]
    rw [Module.End.mem_eigenspace_iff]
    exact key _ h2
  have step : ∀ (a : Fˣ) (w : W),
      (∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) • g) ^ i : Module.End F W) w =
        ∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) ^ i) • (g ^ i) w := by
    intro a w
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, LinearMap.smul_apply]
  have hsum : ∀ w : W,
      (∑ a : Fˣ,
        (∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) • g) ^ i : Module.End F W) w) = w := by
    intro w
    simp only [step]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, FiniteField.sum_pow_units]
    rw [Finset.sum_eq_single 0]
    · simp [CharTwo.neg_eq]
    · intro b hb hb0
      have hnd : ¬ (Fintype.card F - 1 ∣ b) :=
        Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hb0) (Finset.mem_range.mp hb)
      simp [hnd]
    · intro h
      exact absurd (Finset.mem_range.mpr hM) h
  rw [Submodule.eq_top_iff']
  intro w
  have hmem' : (∑ a : Fˣ,
      (∑ i ∈ Finset.range (Fintype.card F - 1), ((a : F) • g) ^ i : Module.End F W) w) ∈
        ⨆ μ : F, Module.End.eigenspace g μ :=
    Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem (a : F)⁻¹ (hmem a w)
  rwa [hsum w] at hmem'

end CFSG.Quasithin.RonanF13
