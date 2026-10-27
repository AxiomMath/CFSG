module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrEightD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_eight_W6_cost_ge_two (h : Cfg133 A t 3) {z : MulAut W} {N : Subgroup (MulAut W)}
    (hD : Data8 A t z N) :
    2 ≤ rk ↥(commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t)) := by
  classical
  obtain ⟨Δ, -, hind, hsum, hrk, -, -, i₀, -, hswap, -⟩ := s13_eight_components h hD
  have hne : i₀ + 1 ≠ i₀ + 2 := by fin_cases i₀ <;> decide
  have hdisj : Δ (i₀ + 1) ⊓ Δ (i₀ + 2) = ⊥ :=
    disjoint_iff.mp (hind.pairwiseDisjoint hne)
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have hcost : rk ↥(commSub (Δ (i₀ + 1) ⊔ Δ (i₀ + 2)) (Subgroup.zpowers t)) =
      rk ↥(Δ (i₀ + 1)) :=
    (rk_commSub_swap h.hW htt hswap.symm hdisj).2
  have hsum' : (⨆ i, Δ i) = commSub ⊤ (Subgroup.zpowers z) := hsum.trans hD.hNV
  have hle : Δ (i₀ + 1) ⊔ Δ (i₀ + 2) ≤ commSub ⊤ (Subgroup.zpowers z) := by
    refine sup_le ?_ ?_
    · exact le_trans (le_iSup Δ (i₀ + 1)) (le_of_eq hsum')
    · exact le_trans (le_iSup Δ (i₀ + 2)) (le_of_eq hsum')
  have hmono : commSub (Δ (i₀ + 1) ⊔ Δ (i₀ + 2)) (Subgroup.zpowers t) ≤
      commSub (commSub ⊤ (Subgroup.zpowers z)) (Subgroup.zpowers t) :=
    commSub_mono hle le_rfl
  have h2 := rk_mono hmono
  rw [hcost, hrk (i₀ + 1)] at h2
  exact h2

theorem w16g_normalizes_kerOn {X : Subgroup (MulAut W)} {s : MulAut W} (hs2 : s * s = 1)
    (hsX : ∀ x ∈ X, s * x * s⁻¹ ∈ X) {U : Subgroup W} (hsU : ∀ u ∈ U, s u ∈ U) :
    ∀ x ∈ s13KerOn X U, s * x * s⁻¹ ∈ s13KerOn X U := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  intro x hx
  rw [s13KerOn] at hx
  refine ⟨hsX x hx.1, mem_centSub.mpr ?_⟩
  intro u hu
  have hsu : s u ∈ U := hsU u hu
  have h1 : x (s u) = s u := mem_centSub.mp hx.2 (s u) hsu
  have h2 : s (s u) = u := by rw [← MulAut.mul_apply, hs2, MulAut.one_apply]
  calc (s * x * s⁻¹) u = s (x (s⁻¹ u)) := by simp only [MulAut.mul_apply]
    _ = s (x (s u)) := by rw [hsinv]
    _ = s (s u) := by rw [h1]
    _ = u := h2

end CFSG.LocalAnalysis.WeakClosure81
