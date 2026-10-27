module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelFixed
public import CFSG.Walter.PSL2Facts.FieldGenerator

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Walter CFSG.GorensteinWalter CFSG.ASVolI
open CFSG.SeitzReduction.LinearPilot

private theorem fieldGen_transport {X : Type} [Group X] {K : Type} [Field K]
    (φ : X ≃* PSL2 K) (θ₀ : MulAut X)
    (hgen : ∀ θ : MulAut (PSL2 K), ∃ j : ℕ, ∃ y : PSL2 K,
      θ = (MulAut.congr φ θ₀) ^ j * MulAut.conj y) :
    ∀ θ : MulAut X, ∃ j : ℕ, ∃ x : X, θ = θ₀ ^ j * MulAut.conj x := by
  intro θ
  obtain ⟨j, y, hy⟩ := hgen (MulAut.congr φ θ)
  refine ⟨j, φ.symm y, ?_⟩
  have hsymm : MulAut.congr φ.symm (MulAut.congr φ θ) = θ := by
    ext x
    simp [MulAut.congr_apply]
  have hsymmθ : MulAut.congr φ.symm (MulAut.congr φ θ₀) = θ₀ := by
    ext x
    simp [MulAut.congr_apply]
  have hpow : MulAut.congr φ.symm ((MulAut.congr φ θ₀) ^ j) = θ₀ ^ j := by
    rw [map_pow, hsymmθ]
  have hconj : MulAut.congr φ.symm (MulAut.conj y) = MulAut.conj (φ.symm y) :=
    CFSG.mulAut_congr_conj φ.symm y
  have hmap := congrArg (MulAut.congr φ.symm) hy
  rw [map_mul, hpow, hconj, hsymm] at hmap
  exact hmap

private theorem normalizer_transport {X : Type} [Group X] {K : Type} [Field K]
    (φ : X ≃* PSL2 K) (S : Sylow 2 X) (θ₀ : MulAut X) (S' : Sylow 2 (PSL2 K))
    (hS'coe : (S' : Subgroup (PSL2 K)) = S.map (φ : X →* PSL2 K))
    (hnorm : ∀ y ∈ Subgroup.normalizer ((S' : Subgroup (PSL2 K)) : Set (PSL2 K)),
      (MulAut.congr φ θ₀) y * y⁻¹ ∈ (S' : Subgroup (PSL2 K)) →
        y ∈ (S' : Subgroup (PSL2 K))) :
    ∀ h ∈ Subgroup.normalizer ((S : Subgroup X) : Set X),
      θ₀ h * h⁻¹ ∈ (S : Subgroup X) → h ∈ (S : Subgroup X) := by
  intro h hhN hcent
  have hhN' : φ h ∈ Subgroup.normalizer
      ((S' : Subgroup (PSL2 K)) : Set (PSL2 K)) := by
    have hmem := Subgroup.mem_map_of_mem (φ : X →* PSL2 K) hhN
    have hnormmap : (Subgroup.normalizer ((S : Subgroup X) : Set X)).map
        (φ : X →* PSL2 K) =
        Subgroup.normalizer ((S : Subgroup X).map (φ : X →* PSL2 K) :
          Set (PSL2 K)) :=
      Subgroup.map_equiv_normalizer_eq (S : Subgroup X) φ
    rw [hnormmap, ← hS'coe] at hmem
    exact hmem
  have hcent' : (MulAut.congr φ θ₀) (φ h) * (φ h)⁻¹ ∈ (S' : Subgroup (PSL2 K)) := by
    rw [hS'coe]
    have hθ : (MulAut.congr φ θ₀) (φ h) = φ (θ₀ h) := by
      simp [MulAut.congr_apply]
    rw [hθ]
    have hmul : φ (θ₀ h) * (φ h)⁻¹ = φ (θ₀ h * h⁻¹) := by
      rw [map_mul, map_inv]
    rw [hmul]
    exact Subgroup.mem_map_of_mem _ hcent
  have hmemS' : φ h ∈ (S' : Subgroup (PSL2 K)) := hnorm (φ h) hhN' hcent'
  have hmap := Subgroup.mem_map_of_mem (φ.symm : PSL2 K →* X) hmemS'
  rw [map_sylow_symm_of_map φ hS'coe] at hmap
  simpa using hmap

theorem fieldGen_of_isL2 {X : Type} [Group X] [Finite X] {e : ℕ} (hX : IsL2 X (2 ^ e))
    (he : 1 ≤ e) (S : Sylow 2 X) {θ₀ : MulAut X}
    (hθ₀S : ∀ x ∈ (S : Subgroup X), θ₀ x ∈ (S : Subgroup X))
    (hout : ∀ x : X, θ₀ ^ (2 ^ (e - 1)) ≠ MulAut.conj x) :
    (∀ θ : MulAut X, ∃ j : ℕ, ∃ x : X, θ = θ₀ ^ j * MulAut.conj x) ∧
    ∀ h ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), θ₀ h * h⁻¹ ∈ (S : Subgroup X) →
      h ∈ (S : Subgroup X) := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hX.statedClassicalModel_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
  let Ψ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
  let φ : X ≃* PSL2 K := e₀.trans Ψ.symm
  let S' : Sylow 2 (PSL2 K) :=
    Sylow.mapSurjective (f := (φ : X →* PSL2 K)) φ.surjective S
  have hS'coe : (S' : Subgroup (PSL2 K)) = S.map (φ : X →* PSL2 K) :=
    Sylow.coe_mapSurjective (f := (φ : X →* PSL2 K)) φ.surjective S
  let θ₀' : MulAut (PSL2 K) := MulAut.congr φ θ₀
  have hθ₀'S : ∀ y ∈ (S' : Subgroup (PSL2 K)), θ₀' y ∈ (S' : Subgroup (PSL2 K)) := by
    intro y hy
    rw [hS'coe] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hθx : θ₀' ((φ : X →* PSL2 K) x) = (φ : X →* PSL2 K) (θ₀ x) := by
      simp [θ₀', MulAut.congr_apply]
    rw [hθx]
    exact Subgroup.mem_map_of_mem _ (hθ₀S x hx)
  have hnot' : ∀ y : PSL2 K, θ₀' ^ (2 ^ (e - 1)) ≠ MulAut.conj y := by
    intro y hy
    apply hout (φ.symm y)
    apply (MulAut.congr φ).injective
    have hpow : MulAut.congr φ (θ₀ ^ (2 ^ (e - 1))) =
        θ₀' ^ (2 ^ (e - 1)) := by
      rw [← map_pow]
    have hconj : MulAut.congr φ (MulAut.conj (φ.symm y)) = MulAut.conj y := by
      rw [CFSG.mulAut_congr_conj]
      simp
    rw [hpow, hy, hconj]
  have hσ₀' : orderOf (psl2FieldPart K θ₀') = 2 ^ e :=
    CFSG.Walter.orderOf_psl2FieldPart_eq_of_pow_not_inner hK rfl he hnot'
  constructor
  · exact fieldGen_transport φ θ₀ (CFSG.Walter.psl2_fieldGen hK θ₀' hσ₀')
  · exact normalizer_transport φ S θ₀ S' hS'coe
      (CFSG.Walter.psl2_normalizer_fieldGen hK Nat.one_le_two_pow θ₀' hσ₀' S' hθ₀'S)

end CFSG.LocalAnalysis.UniquenessCase.UC22
