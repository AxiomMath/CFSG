module

public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusVar
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusGen
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalTransfer

public section

namespace CFSG.StandardType

namespace GGOppRadOmega

open Module QuadraticMap CFSG.LieType.BorelTits CFSG.LieType.Universal.Spin GGOppRad GGOppRadSpU

variable {n : ℕ} {K : Type} [Field K]

theorem forall_isCompl_of_two_mul_le {M' N' : ℕ} {ℓ' : Fin n ⊕ Fin n → ℕ} (hℓ' : IsSpLevel M' ℓ')
    {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)} (hF' : IsSelfDual (spForm n K) F' N')
    (h : ∀ j, 2 * j ≤ N' → ∃ k, IsCompl (stdFlag ℓ' k) (F' j)) (j : ℕ) :
    ∃ k, IsCompl (stdFlag ℓ' k) (F' j) := by
  by_cases hj : 2 * j ≤ N'
  · exact h j hj
  by_cases hjN : N' ≤ j
  · exact ⟨0, by rw [stdFlag_zero, hF'.top j hjN]; exact isCompl_bot_top⟩
  obtain ⟨k, hk⟩ := h (N' - j) (by omega)
  have := isCompl_perp (spForm n K) hk
  rw [perp_stdFlag hℓ', hF'.perp _ (Nat.sub_le N' j), Nat.sub_sub_self (by omega)] at this
  exact ⟨_, this⟩

theorem eq_of_two_mul_finrank {F' : ℕ → Submodule K (Fin n ⊕ Fin n → K)} (hF' : Monotone F')
    {j j₀ : ℕ} (hj : 2 * finrank K (F' j) = finrank K (Fin n ⊕ Fin n → K))
    (hj₀ : 2 * finrank K (F' j₀) = finrank K (Fin n ⊕ Fin n → K)) : F' j = F' j₀ := by
  rcases le_total j j₀ with h | h
  · exact Submodule.eq_of_le_of_finrank_eq (hF' h) (by omega)
  · exact (Submodule.eq_of_le_of_finrank_eq (hF' h) (by omega)).symm

variable [Finite K] [CharP K 2]

theorem exists_lt_of_plusU_ne_bot {ℓ : Fin n ⊕ Fin n → ℕ} (h : plusU (K := K) ℓ ≠ ⊥) :
    ∃ a b, ℓ a < ℓ b := by
  by_contra hcon
  push Not at hcon
  refine h ((Subgroup.eq_bot_iff_forall _).mpr fun g hg => plusRep_injective ?_)
  have hg' := mem_plusU_iff_isUniTri.mp hg
  rw [map_one]
  refine (Pi.basisFun K (Fin n ⊕ Fin n)).ext fun a => ?_
  rw [Pi.basisFun_apply, Module.End.one_apply]
  have h1 := hg' a
  have h0 : stdFlag (K := K) ℓ (ℓ a) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => (Submodule.mem_bot K).mpr (funext fun c => hv c (hcon c a))
  rw [h0, Submodule.mem_bot, sub_eq_zero] at h1
  exact h1

theorem ggOppRadGood_plusU (hn : 3 ≤ n) {ℓ : Fin n ⊕ Fin n → ℕ}
    (hℓ : IsSpLevel (2 * finrank K (Fin n ⊕ Fin n → K)) ℓ)
    (hQ : GGRadicalTwo ⊤ (plusU (K := K) ℓ))
    (hN : (⊤ : Subgroup (spinGroup (quadPlus n K))) ⊓
      Subgroup.normalizer (plusU (K := K) ℓ : Set (spinGroup (quadPlus n K))) = plusP ℓ)
    (hne : plusU (K := K) ℓ ≠ ⊥)
    (hno : ∀ k, 2 * (k + 1) ≤ 2 * finrank K (Fin n ⊕ Fin n → K) + 1 →
      2 * (finrank K (stdFlag (K := K) ℓ k) + 1) = finrank K (Fin n ⊕ Fin n → K) →
      2 * finrank K (stdFlag (K := K) ℓ (k + 1)) = finrank K (Fin n ⊕ Fin n → K) → False) :
    GGOppRadGood ⊤ (plusU (K := K) ℓ) := by
  classical
  have : Finite (spinGroup (quadPlus n K)) := finite_spinGroup_quadPlus
  set d := finrank K (Fin n ⊕ Fin n → K) with hd
  have hd2 : d = 2 * n := finrank_V
  refine ⟨plusU (ℓ ∘ Sum.swap), ⟨radicalTwo_plusU_comp_swap hn hQ, card_plusU_comp_swap hn ℓ, ?_⟩,
    sup_plusU_comp_swap hn hℓ (exists_lt_of_plusU_ne_bot hne), fun V hV => ?_⟩
  · rw [hN]
    exact plusU_comp_swap_inf_plusP hℓ
  obtain ⟨hVrad, hVcard, hVbot⟩ := hV
  set F' := singFlag (plusForm n K) (plusRep n K) V with hF'def
  obtain ⟨hVeq, -⟩ := eq_flagKernel_singFlag_of_radical plusRep_injective plusRep_Q
    (noQuotientReflection_plusRep hn) hVrad
  have hbot : flagKernel (plusRep n K) F' ⊓ flagStab (plusRep n K) (stdFlag ℓ) = ⊥ := by
    rw [← hVeq]
    rw [hN] at hVbot
    exact hVbot
  have hF' : IsSelfDual (plusForm n K).polar F' (2 * d + 1) :=
    isSelfDual_singFlag (plusForm n K) (plusRep n K) V
  have hFs : ∀ j, 2 * j ≤ 2 * d + 1 → (plusForm n K).IsTotallySingular (F' j) := fun j hj =>
    isTotallySingular_singFlag (plusForm n K) (plusRep n K) V (by omega)
  have hA : IsSelfDual (plusForm n K).polar (stdFlag ℓ) (2 * d + 1) := by
    have := isSelfDual_stdFlag (K := K) hℓ
    rwa [← plusForm_polar] at this
  have hAs : ∀ k, 2 * k ≤ 2 * d + 1 → (plusForm n K).IsTotallySingular (stdFlag ℓ k) :=
    fun k hk => isTotallySingular_stdFlag hℓ hk
  have hV2 : Even (finrank K (Fin n ⊕ Fin n → K)) := ⟨n, by omega⟩
  have hcomp := fun j (hj : 2 * j ≤ 2 * d + 1) =>
    isCompl_or_oriflamme hV2 (exists_plusRep_eq_eichler hn) hA hF' hAs hFs hbot hj
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M', ℓ', hℓ', hvar, hcompl⟩ : ∃ (M' : ℕ) (ℓ' : Fin n ⊕ Fin n → ℕ), IsSpLevel M' ℓ' ∧
      (∀ g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K),
        (∀ v, quadPlus n K (g v) = quadPlus n K v) → IsUniTri ℓ' g → IsUniTri ℓ g) ∧
      ∀ j, 2 * j ≤ 2 * d + 1 → ∃ k, IsCompl (stdFlag ℓ' k) (F' j) := by
    by_cases hori : ∃ j, 2 * j ≤ 2 * d + 1 ∧ ¬ ∃ k, IsCompl (stdFlag ℓ k) (F' j)
    · obtain ⟨j₀, hj₀, hnc⟩ := hori
      obtain ⟨hXd, k, x, hk, hAk, hk0, hxX, hxk, hXx, hcase⟩ := (hcomp j₀ hj₀).resolve_left hnc
      rcases hcase with hN' | ⟨hk1, hsup⟩
      · have hkd : k = d := by omega
        subst hkd
        obtain ⟨b, hb, huniq, hcompl0⟩ :=
          exists_isCompl_of_oriflamme hℓ hAk hXd hxX hxk hXx (hFs j₀ hj₀)
        have hbs := level_swap_eq hℓ hb
        refine ⟨4 * d, varLevel ℓ d b, isSpLevel_varLevel hℓ hd1 hb,
          fun g hg h => isUniTri_of_varLevel hℓ hd1 hb huniq hg h, fun j hj => ?_⟩
        rcases hcomp j hj with ⟨k', hk'⟩ | ⟨hXd', -⟩
        · exact ⟨_, by rw [← stdFlag_varLevel hℓ hd1 hb huniq k']; exact hk'⟩
        · have hjj : F' j = F' j₀ := eq_of_two_mul_finrank hF'.mono hXd' hXd
          exact ⟨2 * d, by rw [stdFlag_varLevel_two_mul hb hd1 hbs, hjj]; exact hcompl0⟩
      · exfalso
        refine hno k hk1 hAk ?_
        rw [hsup, Submodule.finrank_sup_span_singleton hxk]
        omega
    · push Not at hori
      exact ⟨2 * d, ℓ, hℓ, fun g _ h => h, hori⟩
  have hF'sp : IsSelfDual (spForm n K) F' (2 * d + 1) := by
    have := hF'
    rwa [plusForm_polar] at this
  have hcompl' := forall_isCompl_of_two_mul_le hℓ' hF'sp hcompl
  have hZ : ∃ z, (plusForm n K).IsTotallySingular (stdFlag ℓ z) ∧
      (plusForm n K).polar.perp (stdFlag ℓ z) ≤ stdFlag ℓ (z + 1) :=
    ⟨d, hAs d (by omega), by
      rw [plusForm_polar, perp_stdFlag hℓ d, show 2 * d + 1 - d = d + 1 by omega]⟩
  obtain ⟨h, i, hi, hhU, hhF, hle⟩ := exists_mem_plusU_flagMap_eq hn hℓ' hvar hZ hF'
    (fun j hj => hFs j (by omega)) hcompl'
  have hVD : V = (plusU (K := K) i).map (MulAut.conj h).toMonoidHom := by
    rw [plusU, ← flagKernel_flagMap, hhF]
    exact hVeq
  have hcV : Nat.card V = Nat.card (plusU (K := K) i) := by
    rw [hVD]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hc1 : Nat.card (plusU (K := K) ℓ) ≤ Nat.card (plusU (K := K) (i ∘ Sum.swap)) := by
    rw [card_plusU_comp_swap hn, ← hcV, hVcard]
  have heq : plusU (K := K) (i ∘ Sum.swap) = plusU ℓ := Subgroup.eq_of_le_of_card_ge hle hc1
  have hii : (i ∘ Sum.swap) ∘ Sum.swap = i := by
    funext a
    simp
  have heq' : plusU (K := K) i = plusU (ℓ ∘ Sum.swap) := by
    rw [← hii, plusU_comp_swap hn (i ∘ Sum.swap), heq, ← plusU_comp_swap hn]
  exact ⟨h, hhU, hVD.trans (by rw [heq'])⟩

theorem ggOppRadGood_plus (hn : 3 ≤ n) {R : Subgroup (spinGroup (quadPlus n K))} (hRne : R ≠ ⊥)
    (hR : GGRadicalTwo ⊤ R) : GGOppRadGood ⊤ R := by
  have : Finite (spinGroup (quadPlus n K)) := finite_spinGroup_quadPlus
  obtain ⟨hReq, hRN⟩ := eq_flagKernel_singFlag_of_radical plusRep_injective plusRep_Q
    (noQuotientReflection_plusRep hn) hR
  obtain ⟨g, ℓ, hℓ, hF⟩ := exists_singFlag_eq_flagMap_plus hn R
  have hRU : R = (plusU (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [plusU, ← flagKernel_flagMap, ← hF]
    exact hReq
  have hRP : Subgroup.normalizer (R : Set (spinGroup (quadPlus n K))) =
      (plusP (K := K) ℓ).map (MulAut.conj g).toMonoidHom := by
    rw [plusP, ← flagStab_flagMap, ← hF, ← hRN, top_inf_eq]
  have hR0 : plusU (K := K) ℓ = R.map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [hRU, ← GGTwoSig.map_conj_mul, inv_mul_cancel, GGTwoSig.map_conj_one]
  have hrad0 : GGRadicalTwo ⊤ (plusU (K := K) ℓ) := by
    rw [hR0]
    exact hR.map_conj (mem_normalizer_top _)
  have hN0 : (⊤ : Subgroup (spinGroup (quadPlus n K))) ⊓
      Subgroup.normalizer (plusU (K := K) ℓ : Set (spinGroup (quadPlus n K))) = plusP ℓ := by
    rw [hR0, top_inf_eq, ← GGTwoSig.map_conj_normalizer, hRP, ← GGTwoSig.map_conj_mul,
      inv_mul_cancel, GGTwoSig.map_conj_one]
  have hne0 : plusU (K := K) ℓ ≠ ⊥ := fun h => hRne (by rw [hRU, h, Subgroup.map_bot])
  have hdim : ∀ j ≤ finrank K (Fin n ⊕ Fin n → K),
      finrank K (singSeq (plusForm n K) (plusRep n K) R j) = finrank K (stdFlag (K := K) ℓ j) := by
    intro j hj
    have h1 := congrFun hF j
    rw [singFlag, isoCompletion_of_le hj] at h1
    rw [h1]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (rep_injective_apply g) _)).symm
  have hno : ∀ k, 2 * (k + 1) ≤ 2 * finrank K (Fin n ⊕ Fin n → K) + 1 →
      2 * (finrank K (stdFlag (K := K) ℓ k) + 1) = finrank K (Fin n ⊕ Fin n → K) →
      2 * finrank K (stdFlag (K := K) ℓ (k + 1)) = finrank K (Fin n ⊕ Fin n → K) → False := by
    intro k hk hZ hL
    exact not_two_mul_finrank_singSeq_succ plusRep_Q R k (by rw [hdim k (by omega)]; exact hZ)
      (by rw [hdim (k + 1) (by omega)]; exact hL)
  rw [hRU]
  exact (ggOppRadGood_plusU hn hℓ hrad0 hN0 hne0 hno).map_conj (mem_normalizer_top g)

end GGOppRadOmega

end CFSG.StandardType
