module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
import CFSG.RankThree.PartOne.K159.KleinNoInvForm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.PartOne.K159.Klein

private theorem hasGap_kleinCnt_sub_erase : ∀ i : Fin 4, ∀ s₁ s₂ : Fin 3 ⊕ Fin 3, s₁ ≠ s₂ →
    HasGap (kleinCnt s₁ - kleinCnt s₂) (Finset.univ.erase i) := by
  decide +kernel

private theorem hasGap_single_sub_zero : ∀ i : Fin 4,
    HasGap ((Pi.single i 1 : Fin 4 → ℤ) - 0) Finset.univ := by
  decide +kernel

theorem sl4HomW3_holds : SL4HomW3Statement := by
  intro K _ _ _ hK σ f hf
  classical
  have hentry : ∀ (i : Fin 4) (t : TwoPt K), ∃ c : K, ∀ s₁ s₂ : Fin 3 ⊕ Fin 3,
      σ (twoPtEntry t i) * f (Pi.single i 1) (Pi.single s₂ 1) s₁ =
        twoPtWt (kleinCnt s₁) t * (twoPtWt (kleinCnt s₂) t)⁻¹ *
          f (Pi.single i 1) (Pi.single s₂ 1) s₁ +
          c * (Pi.single s₂ 1 : Fin 3 ⊕ Fin 3 → K) s₁ := by
    intro i t
    obtain ⟨c, hc⟩ := hf (twoPtSL t) (Pi.single i 1)
    refine ⟨c, fun s₁ s₂ => ?_⟩
    have h := congrFun (LinearMap.congr_fun hc (Pi.single s₂ 1)) s₁
    rw [map_twoPtSL_smul_single, map_smul, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, RingEquiv.coe_toRingHom] at h
    rw [h, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, twoPtSL_inv, rho_twoPtSL_single, map_smul,
      map_smul, LinearMap.smul_apply, LinearMap.id_apply, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, smul_eq_mul, smul_eq_mul, rho_apply, coe_twoPtSL, cong_diagonal_apply,
      twoPtEntry_inv, twoPtEntry_inv, ← mul_inv, twoPtEntry_mul_twoPtEntry,
      twoPtEntry_mul_twoPtEntry]
    ring
  have hoff : ∀ i (s₁ s₂ : Fin 3 ⊕ Fin 3), s₁ ≠ s₂ →
      f (Pi.single i 1) (Pi.single s₂ 1) s₁ = 0 := by
    intro i s₁ s₂ hs
    obtain ⟨t, ht1, htw⟩ := exists_twoPtWt_ne hK (hasGap_kleinCnt_sub_erase i s₁ s₂ hs)
    have hEi : twoPtEntry t i = 1 := ht1 i (by simp)
    obtain ⟨c, hc⟩ := hentry i t
    have h := hc s₁ s₂
    rw [hEi, map_one, Pi.single_apply, if_neg hs, mul_zero, add_zero] at h
    have hw₂ : twoPtWt (kleinCnt s₂) t ≠ 0 := twoPtWt_ne_zero _ _
    have hinv := mul_inv_cancel₀ hw₂
    have h' : (twoPtWt (kleinCnt s₂) t - twoPtWt (kleinCnt s₁) t) *
        f (Pi.single i 1) (Pi.single s₂ 1) s₁ = 0 := by
      linear_combination twoPtWt (kleinCnt s₂) t * h +
        twoPtWt (kleinCnt s₁) t * f (Pi.single i 1) (Pi.single s₂ 1) s₁ * hinv
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr fun h'' => htw h''.symm)
  have hdiag : ∀ i, ∃ μ : K, ∀ s, f (Pi.single i 1) (Pi.single s 1) s = μ := by
    intro i
    obtain ⟨t, -, htw⟩ := exists_twoPtWt_ne hK (hasGap_single_sub_zero i)
    have hEi : twoPtEntry t i ≠ 1 := by
      rw [twoPtEntry_eq_twoPtWt]
      simpa [twoPtWt] using htw
    have hσ : σ (twoPtEntry t i) - 1 ≠ 0 := sub_ne_zero.mpr fun h =>
      hEi (σ.injective (h.trans (map_one σ).symm))
    obtain ⟨c, hc⟩ := hentry i t
    refine ⟨c / (σ (twoPtEntry t i) - 1), fun s => ?_⟩
    have h := hc s s
    rw [Pi.single_eq_same, mul_one, mul_inv_cancel₀ (twoPtWt_ne_zero _ _), one_mul] at h
    rw [eq_div_iff hσ]
    linear_combination h
  have hbasis : ∀ i, ∃ μ : K, f (Pi.single i 1) = μ • LinearMap.id := by
    intro i
    obtain ⟨μ, hμ⟩ := hdiag i
    refine ⟨μ, LinearMap.pi_ext fun s₂ x => ?_⟩
    rw [show (Pi.single s₂ x : Fin 3 ⊕ Fin 3 → K) = x • Pi.single s₂ 1 by
        ext s
        simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp, map_smul, map_smul]
    congr 1
    funext s₁
    rw [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hs : s₁ = s₂
    · subst hs
      rw [hμ, Pi.single_eq_same, mul_one]
    · rw [hoff i s₁ s₂ hs, Pi.single_apply, if_neg hs, mul_zero]
  choose μ hμ using hbasis
  intro v
  refine ⟨∑ i, v i * μ i, ?_⟩
  conv_lhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin 4 → K) by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hμ, smul_smul]

end CFSG.RankThree.GF2n.Stroth80
