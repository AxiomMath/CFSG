module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusMono
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpCurtisOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open CFSG.LieType.RootSystem

private theorem c2slomqrn_finrank_range_conj {G k V : Type*} [Group G] [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (g y : G) :
    Module.finrank k (LinearMap.range (ρ (g * y * g⁻¹) - 1)) =
      Module.finrank k (LinearMap.range (ρ y - 1)) := by
  have hconj : ρ (g * y * g⁻¹) - 1 = ρ g * (ρ y - 1) * ρ (g⁻¹) := by
    rw [map_mul, map_mul]
    have h2 : ρ g * ρ (g⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc ρ g * ρ y * ρ (g⁻¹) - 1 = (ρ g * ρ y - ρ g) * ρ (g⁻¹) := by rw [sub_mul, h2]
      _ = ρ g * (ρ y - 1) * ρ (g⁻¹) := by rw [mul_sub, mul_one]
  have hsurj : Function.Surjective (ρ (g⁻¹)) := fun b =>
    ⟨ρ g b, by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]⟩
  have hrange : LinearMap.range (ρ g * (ρ y - 1) * ρ (g⁻¹)) =
      (LinearMap.range (ρ y - 1)).map (ρ g) := by
    rw [show ρ g * (ρ y - 1) * ρ (g⁻¹) =
      (ρ g).comp ((ρ y - 1).comp (ρ (g⁻¹))) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  have hleft : Function.LeftInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ (g⁻¹)) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let e : V ≃ₗ[k] V := LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩
  rw [hconj, hrange]
  exact e.finrank_map_eq (LinearMap.range (ρ y - 1))

theorem omq_omPlus_four_le_rank_of_node {n : ℕ} (hn : 5 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {k V : Type} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    [Module.Finite k V] {σ : Representation k (spinGroup (quadPlus n F)) V}
    (hσ : IsSimpleRep σ) {y : V} {χ : spinGroup (quadPlus n F) → k} {μ : Fin n → k}
    (ht : (omPlusCurtisDatum n F (by omega)).IsCurtisType σ y χ μ) {j : Fin n}
    (hj : j.val ≠ 0) (hsep : μ j = (omPlusCurtisDatum n F (by omega)).dScalar χ j)
    {g : spinGroup (quadPlus n F)} (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    4 ≤ Module.finrank k (LinearMap.range (σ g - 1)) := by
  have hn3 : 3 ≤ n := by omega
  let D := omPlusCurtisDatum n F hn3
  obtain ⟨g', π, s, hs, hprod, hx, hg⟩ :=
    exists_conj_spinMatrix_eq_spMonoPerm hn3 hg2 hg1
  obtain ⟨x, hxr, hxw⟩ := exists_nW_eq_of_spinMatrix_eq hn3 hs hprod hg
  obtain ⟨v, hvfix, u, hu_mem, hu_inj, hu_move⟩ :=
    exists_four_orbit_omPlus_of_node hn hj hxr hs hx
  let cs := (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanD n)).Group (Fin n → ℤ) :=
    MulAction.compHom (Fin n → ℤ) (weylAction (isFiniteType_cartanD n))
  have hsepD : μ j = D.dScalar χ j := hsep
  have hv : ∀ t : Fin n, μ t ≠ D.dScalar χ t → cs.simple t • v = v := by
    intro t htne
    have htj : t ≠ j := fun htj => htne (by rw [htj]; exact hsepD)
    simpa [cs, MulAction.compHom_smul_def, Module.End.smul_def] using hvfix t htj
  have hu : ∀ i, u i ∈ MulAction.orbit
      (coxeterMatrix (isFiniteType_cartanD n)).Group v := by
    intro i
    obtain ⟨w, hw⟩ := hu_mem i
    exact MulAction.mem_orbit_iff.mpr ⟨w, by
      simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hw.symm⟩
  have h4 := le_finrank_range_sub_one_of_mem_orbit (D := D) hσ ht hv x u hu hu_inj
    (by simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hu_move)
  rw [hxw] at h4
  rw [← c2slomqrn_finrank_range_conj σ g' g]
  exact h4

end CFSG.LocalAnalysis.WeakClosure81
