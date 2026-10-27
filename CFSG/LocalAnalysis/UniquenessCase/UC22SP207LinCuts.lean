module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinLevi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem uc22sp207_cuts {m : ℕ} (hm : m = 3 ∨ m = 4) {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : Type} [Group X] [Finite X] (α : SpecialLinearGroup (Fin m) K →* X)
    (hα : Function.Surjective α) {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < m) {Y : Subgroup X}
    (hY : Y.comap α = LinearFlag.flagStabilizer m K I) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hYp : IsStronglyPEmbedded p Y) : I = {1} ∨ I = {m - 1} := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hI1, hIm⟩ := hcon
  rcases I.eq_empty_or_nonempty with rfl | hI0
  · refine hYp.1 (eq_top_iff.2 fun y _ => ?_)
    obtain ⟨x, rfl⟩ := hα y
    have hx : x ∈ Y.comap α := by
      rw [hY, LinearFlag.flagStabilizer_empty]
      exact mem_top x
    exact hx
  obtain ⟨R, g, hR2, hRQ, hg, hgen⟩ :=
    uc22sp207_exists_levi_witness (K := K) hm hI hI0 hI1 hIm
  refine uc22sp207_not_isStronglyPEmbedded_of_subset_mul (U := R.map α) (hR2.map α)
    (map_le_iff_le_comap.2 (hY ▸ hRQ)) (g := α g) (fun h => hg (hY ▸ h)) (fun y hy => ?_) hp hp2
    hYp
  obtain ⟨x, rfl⟩ := hα y
  have hxQ : x ∈ LinearFlag.flagStabilizer m K I := hY ▸ hy
  obtain ⟨u, huR, hu⟩ := hgen x hxQ
  obtain ⟨q, hq, hqx⟩ := mem_map.1 hu
  have hqY : q ∈ Y.comap α := hY ▸ hq
  refine ⟨α u, ⟨u, huR, rfl⟩, α q, hqY, ?_⟩
  change α g * α q * (α g)⁻¹ = (α u)⁻¹ * α x
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg α (by simpa [MulAut.conj_apply] using hqx)

end CFSG.LocalAnalysis.UniquenessCase.UC22
