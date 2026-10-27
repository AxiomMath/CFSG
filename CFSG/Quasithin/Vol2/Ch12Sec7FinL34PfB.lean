module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinL34PfA
public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2
public import CFSG.LocalAnalysis.ComponentInitial.FieldFourCoverSylowMatrices

public section

namespace CFSG.Quasithin.H13.L34Br

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover

section Model

variable {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
include hk

theorem le_or_le_projRad {F : Subgroup (projectiveSL 3 k)} (hF : F ≤ projUnitriangular 3 k)
    (hFe : IsElemAbelian 2 F) : F ≤ projRad k 0 ∨ F ≤ projRad k 1 := by
  have hF2 : ∀ x ∈ F, x ∈ projRad k 0 ∨ x ∈ projRad k 1 := fun x hx =>
    mem_projRad_of_sq_eq_one hk (by rw [projUnip_eq_projUnitriangular]; exact hF hx)
      (hFe.2 x hx)
  by_contra h
  rw [not_or] at h
  obtain ⟨h0, h1⟩ := h
  obtain ⟨x, hxF, hx0⟩ := Set.not_subset.1 h0
  obtain ⟨y, hyF, hy1⟩ := Set.not_subset.1 h1
  have hx1 : x ∈ projRad k 1 := (hF2 x hxF).resolve_left hx0
  have hy0 : y ∈ projRad k 0 := (hF2 y hyF).resolve_right hy1
  rcases hF2 (x * y) (F.mul_mem hxF hyF) with h | h
  · exact hx0 (by simpa using (projRad k 0).mul_mem h ((projRad k 0).inv_mem hy0))
  · exact hy1 (by simpa using (projRad k 1).mul_mem ((projRad k 1).inv_mem hx1) h)

theorem projRad_le_card (i : Fin 2) :
    projRad k i ≤ projUnitriangular 3 k ∧ Nat.card (projRad k i) = 16 := by
  refine ⟨?_, ?_⟩
  · rw [← projUnip_eq_projUnitriangular]
    exact projRad_le_projUnip i
  · rw [card_projRad, hk]

theorem eq_projRad_of_card {F : Subgroup (projectiveSL 3 k)} (hF : F ≤ projUnitriangular 3 k)
    (hFe : IsElemAbelian 2 F) (hc : Nat.card F = 16) : F = projRad k 0 ∨ F = projRad k 1 := by
  rcases le_or_le_projRad hk hF hFe with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (by rw [hc, (projRad_le_card hk 0).2]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (by rw [hc, (projRad_le_card hk 1).2]))

theorem exists_normalizer_projRad_conj (i : Fin 2) {r s : projectiveSL 3 k}
    (hr : r ∈ projRad k i) (hs : s ∈ projRad k i) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (projRad k i : Set (projectiveSL 3 k)), n * r * n⁻¹ = s := by
  fin_cases i
  · obtain ⟨B, hB⟩ := projRad_zero_transitive hr hs hr1 hs1
    refine ⟨_, ?_, hB⟩
    rw [normalizer_projRad hk]
    exact Subgroup.mem_sup_right ⟨B, rfl⟩
  · obtain ⟨B, hB⟩ := projRad_one_transitive hr hs hr1 hs1
    refine ⟨_, ?_, hB⟩
    rw [normalizer_projRad hk]
    exact Subgroup.mem_sup_right ⟨B, rfl⟩

end Model

theorem l34ParData_of {X : Type} [Group X] [Finite X]
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2) {S₀ : Subgroup X}
    (hS₀ : QuasithinUnique.IsSylowTwoOf S₀ ⊤) : L34ParData X S₀ := by
  obtain ⟨R₂, R₃, hne, hR, -, -⟩ := l34TwoParabolicFact X hX S₀ hS₀
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS₀
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have himg : ∀ R : Subgroup X, (R = R₂ ∨ R = R₃) →
      ∃ i : Fin 2, R.map e.toMonoidHom = projRad k i := by
    intro R hRR
    obtain ⟨hRS, -, hRe, hR16, -⟩ := hR R hRR
    have hle : R.map e.toMonoidHom ≤ projUnitriangular 3 k := by
      rw [← he]
      exact Subgroup.map_mono hRS
    rcases eq_projRad_of_card hk hle (isElemAbelian_map_mulEquiv e hRe)
      (by rw [Subgroup.card_map_of_injective e.injective, hR16]) with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i₂, hi₂⟩ := himg R₂ (Or.inl rfl)
  obtain ⟨i₃, hi₃⟩ := himg R₃ (Or.inr rfl)
  have hi : i₂ ≠ i₃ := by
    rintro rfl
    exact hne (Subgroup.map_injective e.injective (hi₂.trans hi₃.symm))
  have hcover : ∀ i : Fin 2, i = i₂ ∨ i = i₃ := by
    intro i
    fin_cases i <;> fin_cases i₂ <;> fin_cases i₃ <;> simp_all
  refine ⟨R₂, R₃, hne, fun R hRR => ?_, fun E hE hEe => ?_⟩
  · obtain ⟨hRS, hRN, hRe, hR16, hπ, -, -⟩ := hR R hRR
    obtain ⟨i, hi⟩ := himg R hRR
    refine ⟨hRS, hRN, hRe, hR16, hπ, fun r hr s hs hr1 hs1 => ?_⟩
    have her : e r ∈ projRad k i := by rw [← hi]; exact ⟨r, hr, rfl⟩
    have hes : e s ∈ projRad k i := by rw [← hi]; exact ⟨s, hs, rfl⟩
    obtain ⟨n, hn, hnrs⟩ := exists_normalizer_projRad_conj hk i her hes
      (fun h => hr1 (e.injective (by rw [h, map_one])))
      (fun h => hs1 (e.injective (by rw [h, map_one])))
    refine ⟨e.symm n, ?_, ?_⟩
    · have hN := Subgroup.map_equiv_normalizer_eq R e
      rw [← hi, ← hN] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      simpa using hm
    · apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hnrs]
  · have hle : E.map e.toMonoidHom ≤ projUnitriangular 3 k := by
      rw [← he]
      exact Subgroup.map_mono hE
    have hback : ∀ (i : Fin 2) (R : Subgroup X), R.map e.toMonoidHom = projRad k i →
        E.map e.toMonoidHom ≤ projRad k i → E ≤ R := by
      intro i R hR hER x hx
      have hex : e x ∈ R.map e.toMonoidHom := by rw [hR]; exact hER ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hex
      rwa [← e.injective hyx]
    rcases le_or_le_projRad hk hle (isElemAbelian_map_mulEquiv e hEe) with h | h
    · rcases hcover 0 with h0 | h0
      · exact Or.inl (hback 0 R₂ (h0 ▸ hi₂) h)
      · exact Or.inr (hback 0 R₃ (h0 ▸ hi₃) h)
    · rcases hcover 1 with h1 | h1
      · exact Or.inl (hback 1 R₂ (h1 ▸ hi₂) h)
      · exact Or.inr (hback 1 R₃ (h1 ▸ hi₃) h)

end CFSG.Quasithin.H13.L34Br
