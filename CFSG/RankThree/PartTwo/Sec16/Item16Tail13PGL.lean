module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Defs
import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613

open Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter
open CFSG.Assembly.RankThreeEven (projImage)

theorem exists_forall_pow_three_ne {M : Type*} [CommGroup M] [Finite M] {ω : M}
    (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : ∃ δ : M, ∀ u : M, u ^ 3 ≠ δ := by
  have hni : ¬ Function.Injective (fun u : M => u ^ 3) := fun hinj =>
    hω1 (hinj (by simp only [hω, one_pow]))
  rw [Finite.injective_iff_surjective] at hni
  simpa [Function.Surjective] using hni

theorem exists_cube_of_projImage_eq {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hπ : π = false → UnitaryFieldData p f K)
    (heq : projImage (Sec4.slPi π 3 (p ^ f) K) = projImage (Sec4.glPi π 3 (p ^ f) K))
    {g : GL (Fin 3) K} (hg : g ∈ Sec4.glPi π 3 (p ^ f) K) :
    ∃ u : Kˣ, u ^ 3 = GeneralLinearGroup.det g ∧
      GeneralLinearGroup.scalar (Fin 3) u ∈ Sec4.glPi π 3 (p ^ f) K := by
  have hmem : ProjGenLinGroup.mk g ∈ projImage (Sec4.slPi π 3 (p ^ f) K) := by
    rw [heq]
    exact Subgroup.mem_map_of_mem _ hg
  obtain ⟨s, hs, hsg⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hsg
  obtain ⟨hsG, hs1⟩ := (Sec4.mem_slPi_iff hπ).mp hs
  have hds : GeneralLinearGroup.det s = 1 :=
    Units.ext (by rw [GeneralLinearGroup.val_det_apply, hs1, Units.val_one])
  refine ⟨u, ?_, ?_⟩
  · rw [← hu, map_mul, hds, one_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin]
  · have e : GeneralLinearGroup.scalar (Fin 3) u = s⁻¹ * g := by rw [← hu, inv_mul_cancel_left]
    rw [e]
    exact mul_mem (inv_mem hsG) hg

theorem exists_units_pow_three {K : Type} [Field K] [Finite K] (h3 : 3 ∣ Nat.card Kˣ) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨ω, by rw [← hω]; exact pow_orderOf_eq_one ω, ?_⟩
  rintro rfl
  rw [orderOf_one] at hω
  norm_num at hω

theorem kSPGLProper : KSPGLProper := by
  intro π p f K _ hK hq heq
  have := hK.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hcard : Nat.card Kˣ = Sec4.piCard π (p ^ f) - 1 := by rw [Nat.card_units, hK.card]
  cases π
  ·
    have hU := hK.unitary
    change (p ^ f) % 3 = 2 at hq
    change Nat.card Kˣ = (p ^ f) ^ 2 - 1 at hcard
    have hq2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    obtain ⟨ω, hω3, hω1⟩ := exists_units_pow_three (K := K) (by rw [hcard]; omega)
    have hωμ : ω ∈ (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      obtain ⟨k, hk⟩ : 3 ∣ p ^ f + 1 := by omega
      rw [hk, pow_mul, hω3, one_pow]
    obtain ⟨δ, hδ⟩ := exists_forall_pow_three_ne
      (M := (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker) (ω := ⟨ω, hωμ⟩)
      (Subtype.ext (by simpa using hω3)) (fun h => hω1 (congrArg Subtype.val h))
    have hδq : ((δ : Kˣ) : K) ^ (p ^ f + 1) = 1 := by
      have h1 := δ.2
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at h1
      simpa using congrArg Units.val h1
    have hg : diagGL (δ : Kˣ) ∈ Sec4.glPi false 3 (p ^ f) K := by
      rw [Sec4.mem_glPi_false hU, coe_diagGL, diagonal_map (map_zero _), diagonal_transpose,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp [hU.bar_apply, ← pow_succ, hδq]
    obtain ⟨u, hu3, hu⟩ := exists_cube_of_projImage_eq hπ heq hg
    rw [det_diagGL] at hu3
    have huμ : u ∈ (powMonoidHom (p ^ f + 1) : Kˣ →* Kˣ).ker := by
      rw [Sec4.mem_glPi_false hU, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one] at hu
      have h0 := congrFun (diagonal_injective hu) 0
      rw [hU.bar_apply, ← pow_succ] at h0
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      exact Units.ext (by rw [Units.val_pow_eq_pow_val, h0, Units.val_one])
    exact hδ ⟨u, huμ⟩ (Subtype.ext hu3)
  ·
    change (p ^ f) % 3 = 1 at hq
    change Nat.card Kˣ = p ^ f - 1 at hcard
    obtain ⟨ω, hω3, hω1⟩ := exists_units_pow_three (K := K) (by rw [hcard]; omega)
    obtain ⟨δ, hδ⟩ := exists_forall_pow_three_ne hω3 hω1
    obtain ⟨u, hu3, -⟩ :=
      exists_cube_of_projImage_eq hπ heq (Sec4.mem_glPi_true _ (diagGL δ))
    rw [det_diagGL] at hu3
    exact hδ u hu3

end CFSG.RankThree.PartTwo.Sec16.Proof1613
