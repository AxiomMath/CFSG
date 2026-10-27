module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23a.LineMinus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusFourRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.OmegaMinusFourIrr

open CFSG.Open Matrix

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

omit [Finite K] in
private lemma two_dvd_natCard_of_ne_bot_O01 {J : AddSubgroup (ιM → K)} (hJne : J ≠ ⊥) :
    2 ∣ Nat.card ↥J := by
  obtain ⟨v, hv⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hJne
  have h2 : (2 : ℕ) • v = 0 := by
    rw [two_nsmul]
    apply Subtype.ext
    funext i
    show (v : ιM → K) i + (v : ιM → K) i = 0
    exact CharTwo.add_self_eq_zero _
  have hord : addOrderOf v = 2 := addOrderOf_eq_prime h2 hv
  simpa [hord] using addOrderOf_dvd_natCard v

theorem exists_smul_e1M_mem (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {J : AddSubgroup (ιM → K)}
    (hJ : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v ∈ J, (γ : Matrix ιM ιM K) *ᵥ v ∈ J)
    (hJne : J ≠ ⊥) : ∃ a : K, a ≠ 0 ∧ a • KTabC.e1M K ∈ J := by
  classical
  obtain ⟨U, hU2, hUfix⟩ :=
    KTabA.exists_fixedLine_statedOmega_minus_single (m := 2) le_rfl hirr
  let σ : ↥U →* Matrix ιM ιM K :=
    (Units.coeHom (Matrix ιM ιM K)).comp
      ((StatedOmega (StatedQuadMinus 2 K b c)).subtype.comp U.subtype)
  let : MulAction ↥U ↥J :=
    { smul := fun u v =>
        ⟨σ u *ᵥ (v : ιM → K),
          hJ ((u : ↥U) : ↥(StatedOmega (StatedQuadMinus 2 K b c)))
            ((u : ↥U) : ↥(StatedOmega (StatedQuadMinus 2 K b c))).2 (v : ιM → K) v.2⟩
      one_smul := fun v => by
        apply Subtype.ext
        change σ 1 *ᵥ (v : ιM → K) = (v : ιM → K)
        rw [map_one, Matrix.one_mulVec]
      mul_smul := fun u u' v => by
        apply Subtype.ext
        change σ (u * u') *ᵥ (v : ιM → K) = σ u *ᵥ (σ u' *ᵥ (v : ιM → K))
        rw [map_mul, Matrix.mulVec_mulVec] }
  have h0 : (0 : ↥J) ∈ MulAction.fixedPoints ↥U ↥J :=
    MulAction.mem_fixedPoints.mpr fun u =>
      Subtype.ext <| by
        change σ u *ᵥ (0 : ιM → K) = (0 : ιM → K)
        rw [Matrix.mulVec_zero]
  obtain ⟨b, hb, hne⟩ := IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    (α := ↥J) hU2 (two_dvd_natCard_of_ne_bot_O01 hJne) h0
  have hbfix : ∀ u : ↥U, σ u *ᵥ (b : ιM → K) = (b : ιM → K) := by
    intro u
    have h := congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hb) u)
    change σ u *ᵥ (b : ιM → K) = (b : ιM → K) at h
    exact h
  have hbmem := hUfix (b : ιM → K) (fun u hu => by
    have h := hbfix ⟨u, hu⟩
    change ((u : GL ιM K) : Matrix ιM ιM K) *ᵥ (b : ιM → K) = (b : ιM → K) at h
    exact h)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hbmem
  have hb0 : (b : ιM → K) ≠ 0 := by
    intro h
    exact hne (Subtype.ext h.symm)
  have ha0 : a ≠ 0 := by
    intro h
    apply hb0
    rw [← ha, h, zero_smul]
  exact ⟨a, ha0, ha.symm ▸ b.2⟩

theorem smul_e1M_mem {J : AddSubgroup (ιM → K)}
    (hJ : ∀ γ ∈ StatedOmega (StatedQuadMinus 2 K b c), ∀ v ∈ J, (γ : Matrix ιM ιM K) *ᵥ v ∈ J)
    {a : K} (ha : a ≠ 0) (haJ : a • KTabC.e1M K ∈ J) (d : K) : d • KTabC.e1M K ∈ J := by
  by_cases hd : d = 0
  · rw [hd, zero_smul]
    exact J.zero_mem
  · obtain ⟨t, ht⟩ := NatBorelIrr.exists_mulVec_e1M_eq_smul_omegaMinusFour (b := b) (c := c)
      (Units.mk0 (d / a) (div_ne_zero hd ha))
    have hmem := hJ (t : GL ιM K) t.2 (a • KTabC.e1M K) haJ
    rw [Matrix.mulVec_smul, ht, Units.val_mk0, smul_smul, mul_div_cancel₀ d ha] at hmem
    exact hmem

end CFSG.LocalAnalysis.UniquenessCase.UC22.OmegaMinusFourIrr

end
