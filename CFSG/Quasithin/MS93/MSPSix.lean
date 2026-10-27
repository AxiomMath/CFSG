module

public import CFSG.Quasithin.MS93.MSPOpp
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.PresentationLocal CFSG.Timmesfeld.Transvection.QTwo
open CFSG.Quasithin

variable {K : Type} [Field K]

theorem theta_apply_coe (c : ZMod 2 ≃+* K) (σ : Equiv.Perm (Fin 6)) (i j : Fin 2 ⊕ Fin 2) :
    mat (B5FinSp.theta c σ) i j =
      c (Matrix.reindex fourIdx fourIdx
        (((B5FinSp.omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) i j) := by
  exact glSympRingEquiv_apply 2 c _ i j

theorem omegaEquiv_symm_swap : B5FinSp.omegaEquiv.symm (Equiv.swap 2 3) = rootInvolutionA := by
  rw [MulEquiv.symm_apply_eq, B5FinSp.omegaEquiv_apply, omegaPerm_rootInvolutionA]

theorem theta_swap (c : ZMod 2 ≃+* K) : B5FinSp.theta c (Equiv.swap 2 3) = transv (e₂ K) 1 := by
  refine mat_injective (Matrix.ext fun i j => ?_)
  rw [theta_apply_coe, omegaEquiv_symm_swap]
  rw [mat_apply_eq (transv (e₂ K) 1), transv_mulVec]
  change c (Matrix.reindex fourIdx fourIdx (1 + Matrix.single 1 2 1) i j) = _
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [form_apply, fourIdx]

theorem charP_of_ringEquiv (c : ZMod 2 ≃+* K) : CharP K 2 :=
  charP_of_injective_ringHom (f := c.toRingHom) c.injective 2

theorem eq_zero_or_eq_one_of_ringEquiv (c : ZMod 2 ≃+* K) (a : K) : a = 0 ∨ a = 1 := by
  obtain ⟨b, rfl⟩ := c.surjective a
  fin_cases b
  · left; exact map_zero c
  · right; exact map_one c

theorem exists_mulVec_e₂_eq (c : ZMod 2 ≃+* K) {v : V4 K} (hv : v ≠ 0) :
    ∃ g : Sp4 K, mat g *ᵥ e₂ K = v := by
  have := charP_of_ringEquiv c
  obtain ⟨g, hg⟩ := exists_map_pt₀_eq (isPoint_span hv)
  have he : mat g *ᵥ e₁ K ∈ K ∙ v := hg ▸ mulVec_mem_map g (by
    rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
  obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 he
  have hl1 : l = 1 := by
    rcases eq_zero_or_eq_one_of_ringEquiv c l with h | h
    · subst h
      rw [zero_smul] at hl
      exact absurd (mulVec_mat_injective g
        (show mat g *ᵥ e₁ K = mat g *ᵥ 0 by rw [← hl, mulVec_zero])) e₁_ne_zero
    · exact h
  have hw : mat (wAlpha K) *ᵥ e₂ K = e₁ K := by
    rw [wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  refine ⟨g * wAlpha K, ?_⟩
  rw [mat_mul_mulVec, hw, ← hl, hl1, one_smul]

theorem exists_theta_eq_transv (c : ZMod 2 ≃+* K) {σ : Equiv.Perm (Fin 6)} (hσ : σ.IsSwap) :
    ∃ v : V4 K, v ≠ 0 ∧ B5FinSp.theta c σ = transv v 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := hσ
  obtain ⟨g, hg⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap (show (2 : Fin 6) ≠ 3 by decide) hxy)
  refine ⟨mat (B5FinSp.theta c g) *ᵥ e₂ K, fun h => ?_, ?_⟩
  · exact e₂_ne_zero (mulVec_mat_injective (B5FinSp.theta c g)
      (show mat (B5FinSp.theta c g) *ᵥ e₂ K = mat (B5FinSp.theta c g) *ᵥ 0 by
        rw [h, mulVec_zero]))
  · rw [← hg, map_mul, map_mul, map_inv, theta_swap, transv_conj]

theorem isSwap_theta_symm_transv (c : ZMod 2 ≃+* K) {v : V4 K} (hv : v ≠ 0) :
    ((B5FinSp.theta c).symm (transv v 1)).IsSwap := by
  obtain ⟨g, rfl⟩ := exists_mulVec_e₂_eq c hv
  obtain ⟨σ, rfl⟩ := (B5FinSp.theta c).surjective g
  rw [← transv_conj, ← theta_swap c, ← map_inv, ← map_mul, ← map_mul, MulEquiv.symm_apply_apply]
  exact ⟨σ 2, σ 3, fun h => absurd (σ.injective h) (by decide),
    by rw [Equiv.swap_apply_apply]⟩

theorem transv_not_mem_commutator (c : ZMod 2 ≃+* K) {v : V4 K} (hv : v ≠ 0) :
    transv v 1 ∉ commutator (Sp4 K) := by
  intro h
  have hle := Abelianization.commutator_subset_ker
    (Equiv.Perm.sign.comp (B5FinSp.theta c).symm.toMonoidHom)
  have h1 := hle h
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
  change Equiv.Perm.sign ((B5FinSp.theta c).symm (transv v 1)) = 1 at h1
  rw [(isSwap_theta_symm_transv c hv).sign_eq] at h1
  exact absurd h1 (by decide)

theorem mem_commutator_iff_sign (c : ZMod 2 ≃+* K) (g : Sp4 K) :
    g ∈ commutator (Sp4 K) ↔ Equiv.Perm.sign ((B5FinSp.theta c).symm g) = 1 := by
  have hmap : (commutator (Equiv.Perm (Fin 6))).map (B5FinSp.theta c).toMonoidHom =
      commutator (Sp4 K) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.2 (B5FinSp.theta c).surjective]
    rfl
  rw [← hmap, Subgroup.mem_map_equiv, alternatingGroup.commutator_perm_eq (by simp),
    Equiv.Perm.mem_alternatingGroup]

theorem index_commutator (c : ZMod 2 ≃+* K) : (commutator (Sp4 K)).index = 2 := by
  have hker : (Equiv.Perm.sign.comp (B5FinSp.theta c).symm.toMonoidHom).ker =
      commutator (Sp4 K) := by
    ext g
    rw [MonoidHom.mem_ker, mem_commutator_iff_sign c]
    rfl
  have hsurj : Function.Surjective (Equiv.Perm.sign.comp (B5FinSp.theta c).symm.toMonoidHom) :=
    (Equiv.Perm.sign_surjective (Fin 6)).comp (B5FinSp.theta c).symm.surjective
  rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  rfl

theorem nonempty_ringEquiv_of_card_two (hK : Nat.card K = 2) : Nonempty (ZMod 2 ≃+* K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  exact ⟨ZMod.ringEquivOfPrime K Nat.prime_two (by rw [← Nat.card_eq_fintype_card, hK])⟩

theorem transv_not_mem_commutator_of_card_two (hK : Nat.card K = 2) {v : V4 K} (hv : v ≠ 0)
    (a : K) (ha : a ≠ 0) : transv v a ∉ commutator (Sp4 K) := by
  obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hK
  rcases eq_zero_or_eq_one_of_ringEquiv c a with rfl | rfl
  · exact absurd rfl ha
  · exact transv_not_mem_commutator c hv

end CFSG.Quasithin.MS93.MSP
