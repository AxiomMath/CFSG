module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseB
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseBG
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseBGlue3

public section

namespace CFSG.Quasithin.H13.L827X.LBCaseBGlue

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.H13.L827X.LBDefs CFSG.Quasithin.H13.L827X.LBGroupAbs
  CFSG.Quasithin.H13.L827X.LBCaseAGBase CFSG.Quasithin.H13.L827X.LBCaseBGlue2
  CFSG.Quasithin.H13.L827X.LBCaseBGlue3
open scoped commutatorElement

theorem caseB_glue {G : Type} [Group G] [Finite G]
    {T X K U V X₁ W₀ W₁ : Subgroup G} {v : G}
    (h : CFSG.Quasithin.H13.L827X.LBDefs.XiHyp T X K U V X₁ W₀ W₁ v)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {τ : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G) →* (W ≃ₗ[ZMod 2] W)} {π : W₁ → W}
    (hR : CFSG.Quasithin.H13.L827X.LBDefs.ChiefRepProps (CFSG.Quasithin.conjClosure K T ⊔ T)
      (pCoreOf 2 X) W₀ W₁ τ π)
    (hvΛ : v ∈ CFSG.Quasithin.conjClosure K T ⊔ T)
    (hB : ⁅W₁, CFSG.Quasithin.H13.L827X.LBDefs.XiY X⁆ ≤ W₀) :
    8 ≤ Module.finrank (ZMod 2)
      (LinearMap.range ((τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap - 1)) := by
  classical
  have h' := h
  obtain ⟨-, hXi, -, hK, hXK, hNKX, -, -, -, -, hVT, -, hVsq, -, hX1X, -, hvV, hvX1, -,
    hW0W1, -, -, hΛW1, -, hWX⟩ := h'
  obtain ⟨-, hTN, -, p, hp, hp2, hpow, hidx, -⟩ := hXi
  obtain ⟨-, hKperf, -, -⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer.trans hNKX
  have hKK₀ : K ≤ CFSG.Quasithin.conjClosure K T := CFSG.Quasithin.le_conjClosure K T
  have hK₀N : CFSG.Quasithin.conjClosure K T ≤ Subgroup.normalizer (X : Set G) :=
    CFSG.Quasithin.conjClosure_le fun t ht z hz =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTN ht) (hKN hz)) (Subgroup.inv_mem _ (hTN ht))
  have hK₀Λ : CFSG.Quasithin.conjClosure K T ≤ CFSG.Quasithin.conjClosure K T ⊔ T := le_sup_left
  have hXΛ : X ≤ CFSG.Quasithin.conjClosure K T ⊔ T := (hXK.trans hKK₀).trans le_sup_left
  have hΛN : CFSG.Quasithin.conjClosure K T ⊔ T ≤ Subgroup.normalizer (X : Set G) :=
    sup_le hK₀N hTN
  have hvN : v ∈ Subgroup.normalizer (X : Set G) := hTN (hVT hvV)
  have hvv : v * v = 1 := by
    rw [← pow_two]
    exact hVsq v hvV
  have hK₀perf : ⁅CFSG.Quasithin.conjClosure K T, CFSG.Quasithin.conjClosure K T⁆ =
      CFSG.Quasithin.conjClosure K T := conjClosure_commutator_glue2 hKperf
  haveI : Group.IsPerfect (CFSG.Quasithin.conjClosure K T) := Subgroup.isPerfect_iff.mpr hK₀perf
  obtain ⟨hYidx, hS⟩ := index_Yof_of_relIndex_glue2 hidx
  obtain ⟨E, hAddG, hMod, hfin, hE, q, hq_add, hq_surj, hq_ker⟩ :=
    exists_quot_glue2 hYidx (pow_mem_Yof_glue2 hpow)
  haveI : Fintype E := Fintype.ofFinite E
  let σ : (CFSG.Quasithin.conjClosure K T) →* (E ≃ₗ[ZMod p] E) :=
    sigmaGlue2 p hq_surj hq_add hq_ker hK₀N
  have hσ : ∀ (γ : CFSG.Quasithin.conjClosure K T) (x : X),
      σ γ (q x) = q (conjXEquiv X (hK₀N γ.2) x) :=
    fun γ x => sigmaGlue2_apply_q p hq_surj hq_add hq_ker hK₀N γ x
  have hN : ¬ Group.IsSolvable σ.range := by
    intro hs
    have hle : (σ.comp (Subgroup.inclusion hKK₀)).range ≤ σ.range := by
      rintro _ ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKK₀ k, rfl⟩
    have hφ : ∀ (k : K) (x x' : X), (x' : G) = (k : G) * (x : G) * (k : G)⁻¹ →
        (σ.comp (Subgroup.inclusion hKK₀)) k (q x) = q x' := by
      intro k x x' hx'
      rw [MonoidHom.comp_apply, hσ]
      congr 1
      apply Subtype.ext
      simp only [conjXEquiv_coe, Subgroup.coe_inclusion]
      rw [hx']
    exact CFSG.Quasithin.H13.L827X.LBCaseBG.not_solvable_range_K h hp2 hE q hq_add hq_surj hq_ker
      (σ.comp (Subgroup.inclusion hKK₀)) hφ
      (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle))
  have hP : Group.IsPerfect σ.range := Group.IsPerfect.range σ
  obtain ⟨hp5, hO2, hO3⟩ :=
    CFSG.Quasithin.H13.L827X.LBCaseBG.dual_orbit_facts hp2
      CFSG.Quasithin.H13.L827X.sl2OrbitFacts_holds hE σ hP hN
  have hτY : ∀ y : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G), (y : G) ∈ XiY X → τ y = 1 :=
    fun y hy => tau_eq_one_of_mem_XiY_glue3 hR hΛW1 hW0W1.le hB hy
  have hρ0 : rhoGlue3 τ hXΛ hq_surj 0 = 1 := rhoGlue3_zero hXΛ hq_surj hq_add hq_ker hτY
  have hρadd : ∀ e₁ e₂ : E, rhoGlue3 τ hXΛ hq_surj (e₁ + e₂) =
      rhoGlue3 τ hXΛ hq_surj e₁ * rhoGlue3 τ hXΛ hq_surj e₂ :=
    fun e₁ e₂ => rhoGlue3_add hXΛ hq_surj hq_add hq_ker hτY e₁ e₂
  have hinc : ∀ γ : CFSG.Quasithin.conjClosure K T,
      (τ.comp (Subgroup.inclusion hK₀Λ)) γ = τ ⟨(γ : G), hK₀Λ γ.2⟩ := by
    intro γ
    rw [MonoidHom.comp_apply]
    congr 1
  have hcompat : ∀ (γ : CFSG.Quasithin.conjClosure K T) (e : E),
      ((τ.comp (Subgroup.inclusion hK₀Λ)) γ : Module.End (ZMod 2) W) * rhoGlue3 τ hXΛ hq_surj e =
        rhoGlue3 τ hXΛ hq_surj (σ γ e) *
          ((τ.comp (Subgroup.inclusion hK₀Λ)) γ : Module.End (ZMod 2) W) := by
    intro γ e
    rw [hinc γ]
    exact rhoGlue3_conj hXΛ hq_surj hq_add hq_ker hτY (hK₀Λ γ.2) (hK₀N γ.2) (σ γ) (hσ γ) e
  have hC : ∀ w : W, (∀ x : E, rhoGlue3 τ hXΛ hq_surj x w = w) → w = 0 := by
    intro w hw
    apply fixed_zero_glue3 hR hXΛ hΛN hΛW1 hX1X hWX w
    intro x
    have hwx := hw (q x)
    rw [rhoGlue3_q hXΛ hq_surj hq_ker hτY x] at hwx
    exact hwx
  have hgq : ∀ x : X, conjLEGlue2 p hq_surj hq_add hq_ker hvN (q x) =
      q (conjXEquiv X hvN x) := fun x => by
    rw [conjLEGlue2_apply, conjFunGlue2_q hq_surj hq_ker]
  have hVg : ∀ e : E, (τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap * rhoGlue3 τ hXΛ hq_surj e =
      rhoGlue3 τ hXΛ hq_surj (conjLEGlue2 p hq_surj hq_add hq_ker hvN e) *
        (τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap :=
    fun e => rhoGlue3_conj hXΛ hq_surj hq_add hq_ker hτY hvΛ hvN
      (conjLEGlue2 p hq_surj hq_add hq_ker hvN) hgq e
  have hVV : (τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap *
      (τ ⟨v, hvΛ⟩ : W ≃ₗ[ZMod 2] W).toLinearMap = 1 := by
    rw [← CFSG.Quasithin.H13.L827X.LBCaseAG.rep_mul_caseAG τ]
    have e : (⟨v, hvΛ⟩ * ⟨v, hvΛ⟩ : (CFSG.Quasithin.conjClosure K T ⊔ T : Subgroup G)) = 1 :=
      Subtype.ext hvv
    rw [e, CFSG.Quasithin.H13.L827X.LBCaseAG.rep_one_caseAG τ]
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : E, conjLEGlue2 p hq_surj hq_add hq_ker hvN e₀ ≠ e₀ := by
    by_contra hall
    push Not at hall
    apply hvX1
    apply comm_zpowers_le_glue3 hp2 hvN hvv hX1X hS
    have hfix : ∀ x : X, q (conjXEquiv X hvN x) = q x := fun x => by
      have hx := hall (q x)
      rw [conjLEGlue2_apply, conjFunGlue2_q hq_surj hq_ker] at hx
      exact hx
    exact fun x => conj_mul_inv_mem_glue3 hvN hq_ker hfix x
  have hgg : ∀ e : E, conjLEGlue2 p hq_surj hq_add hq_ker hvN
      (conjLEGlue2 p hq_surj hq_add hq_ker hvN e) = e :=
    conjLEGlue2_sq_glue3 p hq_surj hq_add hq_ker hvN hvv
  have hy : e₀ - conjLEGlue2 p hq_surj hq_add hq_ker hvN e₀ ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm he₀)
  have hgy : conjLEGlue2 p hq_surj hq_add hq_ker hvN
      (e₀ - conjLEGlue2 p hq_surj hq_add hq_ker hvN e₀) =
      -(e₀ - conjLEGlue2 p hq_surj hq_add hq_ker hvN e₀) := by
    rw [map_sub, hgg, neg_sub]
  haveI : Nontrivial W := hR.1
  exact CFSG.Quasithin.H13.L827X.LBCaseB.caseB_eight_le hp5 hE σ
    (τ.comp (Subgroup.inclusion hK₀Λ)) (rhoGlue3 τ hXΛ hq_surj)
    hρ0 hρadd hcompat hC hO2 hO3 hy hVV hVg hgy

end CFSG.Quasithin.H13.L827X.LBCaseBGlue

end
