module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusGen
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted GGOppRad GGOppRadSpU

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

theorem forall_isCompl_of_two_mul_le_minus {M' N' : ℕ}
    {ℓ' : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ} (hℓ' : IsMinusLevel M' ℓ')
    {F' : ℕ → Submodule K (Vm n K)} (hF' : IsSelfDual (minusForm n hirr).polar F' N')
    (h : ∀ j, 2 * j ≤ N' → ∃ k, IsCompl (stdFlag ℓ' k) (F' j)) (j : ℕ) :
    ∃ k, IsCompl (stdFlag ℓ' k) (F' j) := by
  by_cases hj : 2 * j ≤ N'
  · exact h j hj
  by_cases hjN : N' ≤ j
  · exact ⟨0, by rw [stdFlag_zero, hF'.top j hjN]; exact isCompl_bot_top⟩
  obtain ⟨k, hk⟩ := h (N' - j) (by omega)
  have := isCompl_perp (minusForm n hirr).polar hk
  rw [perp_stdFlag_minus' hirr hℓ', hF'.perp _ (Nat.sub_le N' j), Nat.sub_sub_self (by omega)]
    at this
  exact ⟨_, this⟩

include hirr in
theorem exists_lt_of_minusU_ne_bot {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (h : minusU (b := b) (c := c) ℓ ≠ ⊥) : ∃ a a', ℓ a < ℓ a' := by
  by_contra hcon
  push Not at hcon
  refine h ((Subgroup.eq_bot_iff_forall _).mpr fun g hg => minusRep_injective hirr ?_)
  have hg' := (mem_minusU_iff_isUniTriM hirr).mp hg
  rw [map_one]
  refine (Pi.basisFun K (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)).ext fun a => ?_
  rw [Pi.basisFun_apply, Module.End.one_apply]
  have h1 := hg' a
  have h0 : stdFlag (K := K) ℓ (ℓ a) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => (Submodule.mem_bot K).mpr (funext fun c' => hv c' (hcon c' a))
  rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
  exact h1

include hirr in
theorem ggOppRadGood_minusU (hn : 4 ≤ n) {ℓ : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → ℕ}
    (hℓ : IsMinusLevel (2 * finrank K (Vm n K)) ℓ)
    (hQ : GGRadicalTwo ⊤ (minusU (b := b) (c := c) ℓ))
    (hN : (⊤ : Subgroup (spinGroup (quadMinus n K b c))) ⊓
      Subgroup.normalizer (minusU (b := b) (c := c) ℓ : Set (spinGroup (quadMinus n K b c))) =
        minusP ℓ)
    (hne : minusU (b := b) (c := c) ℓ ≠ ⊥) :
    GGOppRadGood ⊤ (minusU (b := b) (c := c) ℓ) := by
  classical
  have : Finite (spinGroup (quadMinus n K b c)) := finite_spinGroup_quadMinus hirr
  set d := finrank K (Vm n K) with hd
  have hd2 : d = (n - 1) + ((n - 1) + 2) := by
    rw [hd, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  refine ⟨minusU (ℓ ∘ mpr), ⟨radicalTwo_minusU_comp_mpr hirr hn hℓ hQ,
    card_minusU_comp_mpr hirr hn hℓ, ?_⟩,
    sup_minusU_comp_mpr hirr hn hℓ (exists_lt_of_minusU_ne_bot hirr hne), fun V hV => ?_⟩
  · rw [hN]
    exact minusU_comp_mpr_inf_minusP hirr hℓ
  obtain ⟨hVrad, hVcard, hVbot⟩ := hV
  set F' := singFlag (minusForm n hirr) (minusRep n K b c) V with hF'def
  obtain ⟨hVeq, -⟩ := eq_flagKernel_singFlag_of_radical (minusRep_injective hirr) (minusRep_Q hirr)
    (noQuotientReflection_minusRep hirr hn) hVrad
  have hbot : flagKernel (minusRep n K b c) F' ⊓ flagStab (minusRep n K b c) (stdFlag ℓ) = ⊥ := by
    rw [← hVeq]
    rw [hN] at hVbot
    exact hVbot
  have hF' : IsSelfDual (minusForm n hirr).polar F' (2 * d + 1) :=
    isSelfDual_singFlag (minusForm n hirr) (minusRep n K b c) V
  have hFs : ∀ j, 2 * j ≤ 2 * d + 1 → (minusForm n hirr).IsTotallySingular (F' j) := fun j hj =>
    isTotallySingular_singFlag (minusForm n hirr) (minusRep n K b c) V
      ((show j ≤ d by omega).trans (le_of_eq hd))
  have hA : IsSelfDual (minusForm n hirr).polar (stdFlag ℓ) (2 * d + 1) :=
    isSelfDual_stdFlag_minus hirr hℓ
  have hAs : ∀ k, 2 * k ≤ 2 * d + 1 → (minusForm n hirr).IsTotallySingular (stdFlag ℓ k) :=
    fun k hk => isTotallySingular_stdFlag_minus hirr hℓ hk
  have hV2 : Even (finrank K (Vm n K)) := ⟨n, by omega⟩
  have hcompl : ∀ j, 2 * j ≤ 2 * d + 1 → ∃ k, IsCompl (stdFlag ℓ k) (F' j) := by
    intro j hj
    refine (isCompl_or_oriflamme hV2 (exists_minusRep_eq_eichler hirr hn) hA hF' hAs hFs hbot
      hj).resolve_right fun hX => ?_
    have hXd : 2 * finrank K (F' j) = finrank K (Vm n K) := hX.1
    have h1 : finrank K (F' j) ≤ n - 1 := finrank_le_of_quadMinus hirr (hFs j hj)
    clear hX
    omega
  have hcompl' := forall_isCompl_of_two_mul_le_minus hirr hℓ hF' hcompl
  obtain ⟨h, i, hi, hhU, hhF, hle⟩ := exists_mem_minusU_flagMap_eq hirr hn hℓ hF'
    (fun j hj => hFs j (by omega)) hcompl'
  have hVD : V = (minusU (b := b) (c := c) i).map (MulAut.conj h).toMonoidHom := by
    rw [minusU, ← flagKernel_flagMap, hhF]
    exact hVeq
  have hcV : Nat.card V = Nat.card (minusU (b := b) (c := c) i) := by
    rw [hVD]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hc1 : Nat.card (minusU (b := b) (c := c) ℓ) ≤
      Nat.card (minusU (b := b) (c := c) (i ∘ mpr)) := by
    rw [card_minusU_comp_mpr hirr hn hi, ← hcV, hVcard]
  have heq : minusU (b := b) (c := c) (i ∘ mpr) = minusU ℓ := Subgroup.eq_of_le_of_card_ge hle hc1
  have hii : (i ∘ mpr) ∘ mpr = i := by
    funext a
    simp [mpr_mpr]
  have heq' : minusU (b := b) (c := c) i = minusU (ℓ ∘ mpr) := by
    rw [← hii, minusU_comp_mpr hirr hn hi.comp_mpr, heq, ← minusU_comp_mpr hirr hn hℓ]
  exact ⟨h, hhU, hVD.trans (by rw [heq'])⟩

include hirr in
theorem ggOppRadGood_minus (hn : 4 ≤ n) {R : Subgroup (spinGroup (quadMinus n K b c))}
    (hRne : R ≠ ⊥) (hR : GGRadicalTwo ⊤ R) : GGOppRadGood ⊤ R := by
  have : Finite (spinGroup (quadMinus n K b c)) := finite_spinGroup_quadMinus hirr
  obtain ⟨hReq, hRN⟩ := eq_flagKernel_singFlag_of_radical (minusRep_injective hirr)
    (minusRep_Q hirr) (noQuotientReflection_minusRep hirr hn) hR
  obtain ⟨g, ℓ, hℓ, hF⟩ := exists_singFlag_eq_flagMap_minus hirr hn R
  have hRU : R = (minusU (b := b) (c := c) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [minusU, ← flagKernel_flagMap, ← hF]
    exact hReq
  have hRP : Subgroup.normalizer (R : Set (spinGroup (quadMinus n K b c))) =
      (minusP (b := b) (c := c) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [minusP, ← flagStab_flagMap, ← hF, ← hRN, top_inf_eq]
  have hR0 : minusU (b := b) (c := c) ℓ = R.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hRU, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]
  have hrad0 : GGRadicalTwo ⊤ (minusU (b := b) (c := c) ℓ) := by
    rw [hR0]
    exact hR.map_conj (mem_normalizer_top _)
  have hN0 : (⊤ : Subgroup (spinGroup (quadMinus n K b c))) ⊓
      Subgroup.normalizer (minusU (b := b) (c := c) ℓ : Set (spinGroup (quadMinus n K b c))) =
        minusP ℓ := by
    rw [hR0, top_inf_eq, ← GGTwoSig.map_conj_normalizer, hRP, ← GGTwoSig.map_conj_mul,
      inv_mul_cancel, GGTwoSig.map_conj_one]
  have hne0 : minusU (b := b) (c := c) ℓ ≠ ⊥ := fun h => hRne (by rw [hRU, h, Subgroup.map_bot])
  rw [hRU]
  exact (ggOppRadGood_minusU hirr hn hℓ hrad0 hN0 hne0).map_conj (mem_normalizer_top g)

end GGOppRadOmega

end CFSG.StandardType
