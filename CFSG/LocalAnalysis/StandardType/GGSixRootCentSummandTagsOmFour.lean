module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightLeviBasic
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageSplit

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)

section SL

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ P₃ P₄ : HypPair Q}

theorem orth_flip {P P' : HypPair Q} (h : P.Orth P') : P.Orth (flipPair P') :=
  ⟨h.ef, h.ee, h.ff, h.fe⟩

theorem eichler_mem_commutator_sl (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄) (h₂₃ : P₂.Orth P₃)
    (h₂₄ : P₂.Orth P₄) (h₃₄ : P₃.Orth P₄) {H : Subgroup (V ≃ₗ[K] V)}
    (hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H)
    (hx : ∀ t : K, eichler Q P₃.e (t • P₄.f) ∈ H) (hy : ∀ t : K, eichler Q P₄.e (t • P₃.f) ∈ H)
    (c : K) :
    eichler Q P₁.e (c • P₃.e) ∈ ⁅H, H⁆ ∧ eichler Q P₁.e (c • P₃.f) ∈ ⁅H, H⁆ ∧
      eichler Q P₁.e (c • P₄.e) ∈ ⁅H, H⁆ ∧ eichler Q P₁.e (c • P₄.f) ∈ ⁅H, H⁆ := by
  have h₄₃ := h₃₄.symm
  have key : ∀ (P P' : HypPair Q), P₁.Orth P → P₁.Orth P' → ∀ (t : K) (v : V),
      polar Q P₁.e v = 0 → polar Q P₂.e v = 0 → eichler Q P.e (t • P'.f) ∈ H →
      eichler Q P₁.e (eichler Q P.e (t • P'.f) v - v) ∈ ⁅H, H⁆ := by
    intro P P' h1P h1P' t v hv1 hv2 hg
    have hgO := eichler_mem_orthogonalGroup Q P.e (t • P'.f)
    have hgu : eichler Q P.e (t • P'.f) P₁.e = P₁.e :=
      eichler_apply_of_polar_eq_zero h1P.ee (by rw [polar_smul_right_eq, h1P'.ef, mul_zero])
    rw [← commutatorElement_eichler hgO hgu hv1]
    exact commutator_mem_commutator hg (hR v hv1 hv2).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := key P₃ P₄ h₁₃ h₁₄ (-c) P₄.e h₁₄.ee h₂₄.ee (hx (-c))
    rwa [eichler_smul_f_apply_e' h₃₄, sub_sub_cancel_left, ← neg_smul, neg_neg] at h
  · have h := key P₄ P₃ h₁₄ h₁₃ c P₄.f h₁₄.ef h₂₄.ef (hy c)
    rwa [eichler_smul_f_apply_f h₄₃, add_sub_cancel_left] at h
  · have h := key P₄ P₃ h₁₄ h₁₃ (-c) P₃.e h₁₃.ee h₂₃.ee (hy (-c))
    rwa [eichler_smul_f_apply_e' h₄₃, sub_sub_cancel_left, ← neg_smul, neg_neg] at h
  · have h := key P₃ P₄ h₁₃ h₁₄ c P₃.f h₁₃.ef h₂₃.ef (hx c)
    rwa [eichler_smul_f_apply_f h₃₄, add_sub_cancel_left] at h

theorem eichler_comb_mem_commutator_sl (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄)
    (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄) (h₃₄ : P₃.Orth P₄) {H : Subgroup (V ≃ₗ[K] V)}
    (hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H)
    (hx : ∀ t : K, eichler Q P₃.e (t • P₄.f) ∈ H) (hy : ∀ t : K, eichler Q P₄.e (t • P₃.f) ∈ H)
    (a b a' b' : K) :
    eichler Q P₁.e (a • P₃.e + b • P₃.f + (a' • P₄.e + b' • P₄.f)) ∈ ⁅H, H⁆ := by
  have hc := eichler_mem_commutator_sl h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hR hx hy
  have p1 : ∀ (d : K) (v : V), polar Q P₁.e v = 0 → polar Q P₁.e (d • v) = 0 := fun d v hv => by
    rw [polar_smul_right_eq, hv, mul_zero]
  have pa := p1 a _ h₁₃.ee
  have pb := p1 b _ h₁₃.ef
  have pa' := p1 a' _ h₁₄.ee
  have pb' := p1 b' _ h₁₄.ef
  have pab : polar Q P₁.e (a • P₃.e + b • P₃.f) = 0 := by rw [polar_add_right, pa, pb, add_zero]
  have pab' : polar Q P₁.e (a' • P₄.e + b' • P₄.f) = 0 := by
    rw [polar_add_right, pa', pb', add_zero]
  rw [← eichler_mul pab pab', ← eichler_mul pa pb, ← eichler_mul pa' pb']
  exact mul_mem (mul_mem (hc a).1 (hc b).2.1) (mul_mem (hc a').2.2.1 (hc b').2.2.2)

theorem rootRadical_le_commutator_sl (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄)
    (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄) (h₃₄ : P₃.Orth P₄)
    (hspan : ∀ w, InW P₁ P₂ w → w = polar Q w P₃.f • P₃.e + polar Q w P₃.e • P₃.f +
      (polar Q w P₄.f • P₄.e + polar Q w P₄.e • P₄.f))
    {H : Subgroup (V ≃ₗ[K] V)} (hRH : rootRadical Q P₁ P₂ ≤ H)
    (hx : ∀ t : K, eichler Q P₃.e (t • P₄.f) ∈ H) (hy : ∀ t : K, eichler Q P₄.e (t • P₃.f) ∈ H) :
    rootRadical Q P₁ P₂ ≤ ⁅H, H⁆ := by
  have hR : ∀ y, polar Q P₁.e y = 0 → polar Q P₂.e y = 0 →
      eichler Q P₁.e y ∈ H ∧ eichler Q P₂.e y ∈ H := fun y h1 h2 =>
    ⟨hRH (eichler_mem_rootRadical_left h₁₂ h1 h2), hRH (eichler_mem_rootRadical_right h₁₂ h1 h2)⟩
  have hR' : ∀ y, polar Q P₂.e y = 0 → polar Q P₁.e y = 0 →
      eichler Q P₂.e y ∈ H ∧ eichler Q P₁.e y ∈ H := fun y h2 h1 => (hR y h1 h2).symm
  have hW1 : ∀ w, InW P₁ P₂ w → eichler Q P₁.e w ∈ ⁅H, H⁆ := fun w hw => by
    rw [hspan w hw]
    exact eichler_comb_mem_commutator_sl h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hR hx hy _ _ _ _
  have hW2 : ∀ w, InW P₂ P₁ w → eichler Q P₂.e w ∈ ⁅H, H⁆ := fun w hw => by
    rw [hspan w (inW_comm.mpr hw)]
    exact eichler_comb_mem_commutator_sl h₂₃ h₂₄ h₁₃ h₁₄ h₃₄ hR' hx hy _ _ _ _
  refine rootRadical_le_of_eichler_mem h₁₂ (fun y h1 h2 => ?_) (fun y h1 h2 => ?_)
  · exact eichler_mem_of_pieces h₁₂ hW1 (eichler_smul_e_mem_commutator' h₁₂ h₁₃ h₂₃ hR) h1 h2
  · exact eichler_mem_of_pieces h₁₂.symm hW2 (eichler_smul_e_mem_commutator' h₁₂.symm h₂₃ h₁₃ hR')
      h2 h1

end SL

section Card

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit (specialImage specialRho)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : QuadraticForm K W}

theorem card_orthDerived_le_four (hR : (polarBilin R).Nondegenerate) (hdim : finrank K W = 4)
    (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) (hq : 4 ≤ Nat.card K) :
    Nat.card (orthDerived R) ≤ Nat.card SL(2, K) ^ 2 := by
  classical
  have hq2 : Nat.card K ≠ 2 := by omega
  have hq3 : Nat.card K ≠ 3 := by omega
  obtain ⟨-, -, -, hcov4, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      _ hR (Or.inr (Or.inr ⟨hdim, hS⟩))
  obtain ⟨-, e, -, -, hcomm, -⟩ := hcov4 hdim hS hq2 hq3
  have hJ : commutator (TauCeti.QuadraticMap.orthogonalGroup R) =
      (specialImage K).map e.symm.toMonoidHom := by
    rw [hcomm, ← Subgroup.map_sup, CFSG.LocalAnalysis.ComponentInitial.determinantFactors_sup]
  have hder : (commutator (TauCeti.QuadraticMap.orthogonalGroup R)).map
      (TauCeti.QuadraticMap.orthogonalGroup R).subtype = orthDerived R := by
    rw [Subgroup.map_subtype_commutator]
  calc Nat.card (orthDerived R)
      = Nat.card (commutator (TauCeti.QuadraticMap.orthogonalGroup R)) := by
        rw [← hder, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    _ = Nat.card (specialImage K) := by
        rw [hJ, Subgroup.card_map_of_injective e.symm.injective]
    _ ≤ Nat.card (SL(2, K) × SL(2, K)) :=
        Nat.card_le_card_of_surjective _ (specialRho (K := K)).rangeRestrict_surjective
    _ = Nat.card SL(2, K) ^ 2 := by rw [Nat.card_prod, _root_.sq]

theorem eq_two_or_three_of_dvd_card_four (hR : (polarBilin R).Nondegenerate)
    (hdim : finrank K W = 4) (hS : ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0)
    (hK : Nat.card K = 2) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R)) : p = 2 ∨ p = 3 := by
  obtain ⟨h1, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      R hR (Or.inr (Or.inr ⟨hdim, hS⟩))
  exact (h1 (Or.inr ⟨⟨hdim, hS⟩, Or.inl hK⟩)).1 p hp hpd

omit [Finite K] [FiniteDimensional K W] in
theorem exists_totallySingular_two {P P' : HypPair R} (h : P.Orth P') :
    ∃ S : Submodule K W, finrank K S = 2 ∧ ∀ x ∈ S, R x = 0 := by
  refine ⟨Submodule.span K (Set.range ![P.e, P'.e]), ?_, fun x hx => ?_⟩
  · rw [finrank_span_eq_card (linearIndependent_pair_e' h), Fintype.card_fin]
  · obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [QuadraticMap.map_add R, QuadraticMap.map_smul, QuadraticMap.map_smul, P.Q_e, P'.Q_e,
      polar_smul_left_eq, polar_smul_right_eq, h.ee]
    simp

end Card

section FrameFour

theorem fin_four_cover : ∀ i j k l m : Fin 4, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
    m = i ∨ m = j ∨ m = k ∨ m = l := by
  decide

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem eq_comb_of_inW_four (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    {s t : Bool} {c : K} (hc : c ≠ 0) {w : V}
    (hw : InW (framePair F j t) (smulPair (framePair F i s) hc) w) :
    w = polar Q w (F.vec k false) • F.vec k true + polar Q w (F.vec k true) • F.vec k false +
      (polar Q w (F.vec l false) • F.vec l true + polar Q w (F.vec l true) • F.vec l false) := by
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hwi : ∀ u, polar Q (F.vec i u) w = 0 := by
    have h3 : polar Q (F.vec i s) w = 0 := by
      have h : polar Q (c • F.vec i s) w = 0 := hw3
      rwa [polar_smul_left_eq, mul_eq_zero, or_iff_right hc] at h
    have h4 : polar Q (F.vec i (!s)) w = 0 := by
      have h : polar Q (c⁻¹ • F.vec i (!s)) w = 0 := hw4
      rwa [polar_smul_left_eq, mul_eq_zero, or_iff_right (inv_ne_zero hc)] at h
    intro u
    rcases Bool.eq_or_eq_not u s with rfl | rfl
    · exact h3
    · exact h4
  have hwj : ∀ u, polar Q (F.vec j u) w = 0 := by
    intro u
    rcases Bool.eq_or_eq_not u t with rfl | rfl
    · exact hw1
    · exact hw2
  have key : w - (polar Q w (F.vec k false) • F.vec k true +
      polar Q w (F.vec k true) • F.vec k false + (polar Q w (F.vec l false) • F.vec l true +
        polar Q w (F.vec l true) • F.vec l false)) = 0 := by
    refine hF0 _ fun m u => ?_
    simp only [polar_sub_right, polar_add_right, polar_smul_right_eq]
    rcases fin_four_cover i j k l m hij hik hil hjk hjl hkl with rfl | rfl | rfl | rfl
    · rw [hwi u, F.polar_vec_of_ne hik, F.polar_vec_of_ne hik, F.polar_vec_of_ne hil,
        F.polar_vec_of_ne hil]
      ring
    · rw [hwj u, F.polar_vec_of_ne hjk, F.polar_vec_of_ne hjk, F.polar_vec_of_ne hjl,
        F.polar_vec_of_ne hjl]
      ring
    · rw [F.polar_vec_of_ne hkl, F.polar_vec_of_ne hkl]
      cases u
      · have h1 := F.polar_vec_not m false
        rw [Bool.not_false] at h1
        rw [h1, F.polar_vec_self, polar_comm Q w (F.vec m false)]
        ring
      · have h1 := F.polar_vec_not m true
        rw [Bool.not_true] at h1
        rw [h1, F.polar_vec_self, polar_comm Q w (F.vec m true)]
        ring
    · rw [F.polar_vec_of_ne hkl.symm, F.polar_vec_of_ne hkl.symm]
      cases u
      · have h1 := F.polar_vec_not m false
        rw [Bool.not_false] at h1
        rw [h1, F.polar_vec_self, polar_comm Q w (F.vec m false)]
        ring
      · have h1 := F.polar_vec_not m true
        rw [Bool.not_true] at h1
        rw [h1, F.polar_vec_self, polar_comm Q w (F.vec m true)]
        ring
  exact sub_eq_zero.mp key

end FrameFour

section Factors

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₃ P₄ : HypPair Q}

open scoped MatrixGroups

theorem leviFix_inf_flip_eq_bot (h₃₄ : P₃.Orth P₄) :
    leviFix (elementaryGroup Q) P₃ P₄ ⊓ leviFix (elementaryGroup Q) P₃ (flipPair P₄) = ⊥ := by
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  rw [eq_bot_iff]
  rintro w ⟨hwX, hwY⟩
  have hYX := le_centralizer_iff.mp (leviFix_le_centralizer_flip h₃₄ hE hE)
  have hcen : (⟨w, hwX⟩ : leviFix (elementaryGroup Q) P₃ P₄) ∈
      center (leviFix (elementaryGroup Q) P₃ P₄) := by
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hYX hwY) y y.2
  set ε := leviFixEquiv P₃ P₄ h₃₄ hE with hε
  have h1 : ε ⟨w, hwX⟩ ∈ center SL(2, K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hcen) y']
  rw [center_SL2_eq_bot_of_charTwo, mem_bot] at h1
  have h2 : (⟨w, hwX⟩ : leviFix (elementaryGroup Q) P₃ P₄) = 1 := ε.injective (by rw [h1, map_one])
  rw [mem_bot]
  exact congrArg Subtype.val h2

end Factors

section LayerFour

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open scoped MatrixGroups

theorem ggRCSLayer_frame_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (F : HypFrame Q 4)
    (hF0 : ∀ x : V, (∀ k u, polar Q (F.vec k u) x = 0) → x = 0) {i j k l : Fin 4}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (s t : Bool) {c : K} (hc : c ≠ 0) (h23 : Nat.card K = 2 → p ≠ 3)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayer p ψ.range M (ψ (u * x * u⁻¹)) := by
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  have h₁₂ := orth₁₂ F hij s t hc
  have h₁₃ := orth₁₃ F hjk t true
  have h₁₄ := orth₁₃ F hjl t true
  have h₂₃ := orth₂₃ F hik s true hc
  have h₂₄ := orth₂₃ F hil s true hc
  have h₃₄ := framePair_orth F hkl true true
  have h₁₄' := orth_flip h₁₄
  have h₂₄' := orth_flip h₂₄
  have h₃₄' := orth_flip h₃₄
  have hspan₁ : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (framePair F l true).f • (framePair F l true).e +
          polar Q w (framePair F l true).e • (framePair F l true).f) := fun w hw =>
    eq_comb_of_inW_four F hF0 hij hik hil hjk hjl hkl hc hw
  have hspan₂ : ∀ w, InW (framePair F j t) (smulPair (framePair F i s) hc) w →
      w = polar Q w (framePair F k true).f • (framePair F k true).e +
        polar Q w (framePair F k true).e • (framePair F k true).f +
        (polar Q w (flipPair (framePair F l true)).f • (flipPair (framePair F l true)).e +
          polar Q w (flipPair (framePair F l true)).e • (flipPair (framePair F l true)).f) :=
    fun w hw => by
      conv_lhs => rw [hspan₁ w hw]
      simp only [flipPair_e, flipPair_f]
      abel
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hWeq : wSub (framePair F j t) (smulPair (framePair F i s) hc) =
      spanU₄ (framePair F k true) (framePair F l true) := by
    apply le_antisymm
    · intro w hw
      rw [hspan₁ w (mem_wSub.mp hw)]
      exact add_mem (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₁)
        (Submodule.smul_mem _ _ mem_spanU₄_f₁))
        (add_mem (Submodule.smul_mem _ _ mem_spanU₄_e₂) (Submodule.smul_mem _ _ mem_spanU₄_f₂))
    · rw [spanU₄, Submodule.span_le]
      rintro _ (rfl | rfl | rfl | rfl)
      · exact vec_mem_wSub F hik hjk hc true
      · exact vec_mem_wSub F hil hjl hc true
      · exact vec_mem_wSub F hik hjk hc false
      · exact vec_mem_wSub F hil hjl hc false
  have hdim : finrank K (wSub (framePair F j t) (smulPair (framePair F i s) hc)) = 4 := by
    rw [hWeq, finrank_spanU₄ h₃₄]
  have hS := exists_totallySingular_two (R := Q.restrict (wSub (framePair F j t)
      (smulPair (framePair F i s) hc)))
    (orth_restrictPair h₃₄ (vec_mem_wSub F hik hjk hc true) (vec_mem_wSub F hik hjk hc false)
      (vec_mem_wSub F hil hjl hc true) (vec_mem_wSub F hil hjl hc false))
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  rw [← hφr] at hG₀M hM
  have hRE : rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) (framePair F j t) (smulPair (framePair F i s) hc) ≤
      σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) ≤ σ.range :=
    hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q (framePair F j t) (smulPair (framePair F i s) hc)) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) (framePair F j t)
    (smulPair (framePair F i s) hc)) with hAGdef
  set BG := Φ σ φ (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) with hBGdef
  have hX : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ BG := by
    have hx' : σ x = eichler Q (framePair F j t).e (smulPair (framePair F i s) hc).e := hx
    rw [RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC, centralizer_eq_comap hσ hσE x, hx',
      centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv _ _ h₁₂ hE)
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    have hp3 := h23 hK
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
    have hpA : ¬ p ∣ Nat.card AG := by
      rw [Nat.card_congr (eA.trans e3).toEquiv, card_perm_three]
      exact fun h => hp3 (eq_three_of_dvd_six hp hp2 h)
    have hpB : ¬ p ∣ Nat.card BG := by
      rw [Nat.card_congr (Φ_equiv hσ φ hφ hL₂E).toEquiv]
      intro hpd
      have hdvd : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ∣
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub (framePair F j t)
            (smulPair (framePair F i s) hc)))) := by
        rw [Nat.card_congr (MonoidHom.ofInjective (resW_injective (Q := Q) h₁₂)).toEquiv]
        refine Subgroup.card_dvd_of_le ?_
        rintro _ ⟨g, rfl⟩
        exact resW_mem_orthogonalGroup g
      rcases eq_two_or_three_of_dvd_card_four hR hdim hS hK hp (dvd_trans hpd hdvd) with h | h
      · exact hp2 h
      · exact hp3 h
    refine ⟨∅, fun _ h => absurd h (Set.notMem_empty _), fun y hy hyp => ?_⟩
    have hy1 : y ∈ AG ⊔ (QG ⊔ BG) := by
      have e : ggRCSX φ.range (φ x) = AG ⊔ (QG ⊔ BG) := by rw [hX]; ac_rfl
      rw [← e]
      exact hy
    have hy2 := ggRCST_mem_of_mem_sup_coprime hp hpA
      (le_normalizer_sup_of_centralizer h1Q h12) hy1 hyp
    have hy3 := ggRCST_mem_of_mem_sup_coprime hp hpB h2Q (by rwa [sup_comm] at hy2) hyp
    rw [ggRCS_eq_one_of_mem_two hp hp2 hQ2 hy3 hyp]
    exact one_mem _
  ·
    have hΩ := omegaGroup_le_orthDerived_of_splitFour hR hdim hS hK
    have hcardR := card_orthDerived_le_four hR hdim hS hK
    have hLa := leviFix_le_omFix (Q := Q) h₁₃ h₁₄ h₂₃ h₂₄
    have hLb := leviFix_le_omFix (Q := Q) h₁₃ h₁₄' h₂₃ h₂₄'
    have hab := leviFix_le_centralizer_flip h₃₄ hE hE
    have hdisj := leviFix_inf_flip_eq_bot (Q := Q) h₃₄
    have hcard' : Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) ≤
        Nat.card (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)) *
          Nat.card (leviFix (elementaryGroup Q) (framePair F k true)
            (flipPair (framePair F l true))) := by
      rw [Nat.card_congr (omFixEquiv h₁₂ hQ hEΩ hOE hR hΩ).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄ hE).toEquiv,
        Nat.card_congr (leviFixEquiv _ _ h₃₄' hE).toEquiv, ← _root_.sq]
      exact hcardR
    have hgen : omFix Q (framePair F j t) (smulPair (framePair F i s) hc) =
        leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ⊔
          leviFix (elementaryGroup Q) (framePair F k true) (flipPair (framePair F l true)) := by
      refine le_antisymm (fun g hg => ?_) (sup_le hLa hLb)
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_card_le hLa hLb hab hdisj hcard' g hg
      exact mul_mem (mem_sup_left ha) (mem_sup_right hb)
    have hLaE : leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true) ≤
        σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
    have hLbE : leviFix (elementaryGroup Q) (framePair F k true)
        (flipPair (framePair F l true)) ≤ σ.range := hσE ▸ fun g hg => (mem_leviFix.mp hg).1
    set B1G := Φ σ φ (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true))
      with hB1Gdef
    set B2G := Φ σ φ (leviFix (elementaryGroup Q) (framePair F k true)
      (flipPair (framePair F l true))) with hB2Gdef
    have hBG : BG = B1G ⊔ B2G := by rw [hBGdef, hgen, Φ_sup hσ φ hLaE hLbE]
    have hX4 : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ B1G ⊔ B2G := by rw [hX, hBG, ← sup_assoc]
    have hSL : CFSG.IsQuasisimple SL(2, K) :=
      CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK)
    have qz : ∀ L : Subgroup G, (↥L ≃* SL(2, K)) → CFSG.IsQuasisimple L ∧ center L = ⊥ :=
      fun L e => ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hSL, by
        rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e.symm,
          center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]⟩
    obtain ⟨hAq, hAZ⟩ := qz AG eA
    obtain ⟨hB1q, hB1Z⟩ := qz B1G ((Φ_equiv hσ φ hφ hLaE).trans (leviFixEquiv _ _ h₃₄ hE))
    obtain ⟨hB2q, hB2Z⟩ := qz B2G ((Φ_equiv hσ φ hφ hLbE).trans (leviFixEquiv _ _ h₃₄' hE))
    have hB1Q : B1G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLa.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hB2Q : B2G ≤ normalizer (QG : Set G) :=
      Φ_le_normalizer φ (hLb.trans (omFix_le_normalizer_rootRadical h₁₂))
    have hAB1 : AG ≤ centralizer (B1G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ _ _)
    have hAB2 : AG ≤ centralizer (B2G : Set G) :=
      Φ_le_centralizer hσ φ (leviFix_le_centralizer_of_orth h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' _ _)
    have hB12 : B1G ≤ centralizer (B2G : Set G) := Φ_le_centralizer hσ φ hab
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hQB1 : QG ≤ ⁅QG ⊔ B1G, QG ⊔ B1G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ hspan₁
        (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (framePair F l true)) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hE t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄ hE t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLaE) (sup_le hRE hLaE), Φ_sup hσ φ hRE hLaE] at h
    have hQB2 : QG ≤ ⁅QG ⊔ B2G, QG ⊔ B2G⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_sl h₁₂ h₁₃ h₁₄' h₂₃ h₂₄' h₃₄'
        hspan₂ (H := rootRadical Q _ _ ⊔ leviFix (elementaryGroup Q) (framePair F k true)
          (flipPair (framePair F l true))) le_sup_left
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hE t).1)
        (fun t => mem_sup_right (eichler_mem_leviFix h₃₄' hE t).2))
      rwa [Φ_commutator hσ φ (sup_le hRE hLbE) (sup_le hRE hLbE), Φ_sup hσ φ hRE hLbE] at h
    have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
      pCoreOf_eq_of_three_summands (by rw [hX4]; ac_rfl) hQ2 h1Q hB1Q hB2Q hAB1 hAB2 hB12
        (ggRCSOmSummand_of_isQuasisimple hAq hAZ) (ggRCSOmSummand_of_isQuasisimple hB1q hB1Z)
        (ggRCSOmSummand_of_isQuasisimple hB2q hB2Z)
    exact ggRCSLayer_of_three_summands hp hp2 hG₀M hM hQ2 hO2 hX4 h1Q hB1Q hB2Q hAB1 hAB2 hB12
      (fun _ => ⟨hAq, hQA⟩) (fun _ => ⟨hB1q, hQB1⟩) (fun _ => ⟨hB2q, hQB2⟩)

end LayerFour

end RCSTOm

end CFSG.StandardType
