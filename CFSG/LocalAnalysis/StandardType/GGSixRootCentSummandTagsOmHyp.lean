module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmFrame

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)

section HypFrame

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {N : ℕ}
  (F : HypFrame Q N)

theorem orth₁₂ {i j : Fin N} (hij : i ≠ j) (s t : Bool) {c : K} (hc : c ≠ 0) :
    (framePair F j t).Orth (smulPair (framePair F i s) hc) :=
  orth_smulPair (framePair_orth F hij.symm t s) hc

theorem orth₁₃ {j k : Fin N} (hjk : j ≠ k) (t u : Bool) :
    (framePair F j t).Orth (framePair F k u) :=
  framePair_orth F hjk t u

theorem orth₂₃ {i k : Fin N} (hik : i ≠ k) (s u : Bool) {c : K} (hc : c ≠ 0) :
    (smulPair (framePair F i s) hc).Orth (framePair F k u) :=
  (orth_smulPair (framePair_orth F hik.symm u s) hc).symm

theorem inW_frame {i j : Fin N} {s t : Bool} {c : K} (hc : c ≠ 0) {y : V}
    (hi : ∀ u, polar Q (F.vec i u) y = 0) (hj : ∀ u, polar Q (F.vec j u) y = 0) :
    InW (framePair F j t) (smulPair (framePair F i s) hc) y := by
  refine ⟨hj t, hj (!t), ?_, ?_⟩
  · change polar Q (c • F.vec i s) y = 0
    rw [polar_smul_left_eq, hi, mul_zero]
  · change polar Q (c⁻¹ • F.vec i (!s)) y = 0
    rw [polar_smul_left_eq, hi, mul_zero]

theorem vec_mem_wSub {i j k : Fin N} (hik : i ≠ k) (hjk : j ≠ k) {s t : Bool} {c : K}
    (hc : c ≠ 0) (u : Bool) :
    F.vec k u ∈ wSub (framePair F j t) (smulPair (framePair F i s) hc) :=
  mem_wSub.mpr (inW_frame F hc (fun v => F.polar_vec_of_ne hik v u)
    (fun v => F.polar_vec_of_ne hjk v u))

theorem exists_totallySingular_wSub {i j k l m : Fin N} (hik : i ≠ k) (hil : i ≠ l)
    (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l) (hkm : k ≠ m)
    (hlm : l ≠ m) (s t : Bool) {c : K} (hc : c ≠ 0) :
    ∃ T : Submodule K (wSub (framePair F j t) (smulPair (framePair F i s) hc)),
      finrank K T = 3 ∧ ∀ x ∈ T, Q.restrict (wSub (framePair F j t)
        (smulPair (framePair F i s) hc)) x = 0 :=
  exists_totallySingular_of_hypPairs
    (P₁ := restrictPair (framePair F k true) (vec_mem_wSub F hik hjk hc true)
      (vec_mem_wSub F hik hjk hc false))
    (P₂ := restrictPair (framePair F l true) (vec_mem_wSub F hil hjl hc true)
      (vec_mem_wSub F hil hjl hc false))
    (P₃ := restrictPair (framePair F m true) (vec_mem_wSub F him hjm hc true)
      (vec_mem_wSub F him hjm hc false))
    (orth_restrictPair (framePair_orth F hkl true true) _ _ _ _)
    (orth_restrictPair (framePair_orth F hkm true true) _ _ _ _)
    (orth_restrictPair (framePair_orth F hlm true true) _ _ _ _)

theorem exists_restrict_ne_zero {i j k : Fin N} (hik : i ≠ k) (hjk : j ≠ k) {s t : Bool}
    {c : K} (hc : c ≠ 0) :
    ∃ v, Q.restrict (wSub (framePair F j t) (smulPair (framePair F i s) hc)) v ≠ 0 := by
  refine ⟨⟨F.vec k true + F.vec k false, add_mem (vec_mem_wSub F hik hjk hc true)
    (vec_mem_wSub F hik hjk hc false)⟩, ?_⟩
  rw [restrict_apply', QuadraticMap.map_add Q, F.map_vec, F.map_vec, zero_add, zero_add]
  have h := F.polar_vec_not k true
  rw [Bool.not_true] at h
  rw [h]
  exact one_ne_zero

theorem leviFix_le_omFix {P₁ P₂ P₃ P₄ : HypPair Q} (h₁₃ : P₁.Orth P₃) (h₁₄ : P₁.Orth P₄)
    (h₂₃ : P₂.Orth P₃) (h₂₄ : P₂.Orth P₄) :
    leviFix (elementaryGroup Q) P₃ P₄ ≤ omFix Q P₁ P₂ := by
  intro g hg
  obtain ⟨hgE, -, hgW⟩ := mem_leviFix.mp hg
  obtain ⟨a1, a2⟩ := inW_of_orth h₁₃ h₁₄
  obtain ⟨b1, b2⟩ := inW_of_orth h₂₃ h₂₄
  exact mem_omFix.mpr ⟨hgE, hgW _ a1, hgW _ a2, hgW _ b1, hgW _ b2⟩

theorem three_dvd_card_omFix [Finite K] [Finite V] {i j k l : Fin N} (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (s t : Bool) {c : K} (hc : c ≠ 0)
    (hK : Nat.card K = 2) :
    3 ∣ Nat.card (omFix Q (framePair F j t) (smulPair (framePair F i s) hc)) := by
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hle := leviFix_le_omFix (P₃ := framePair F k true) (P₄ := framePair F l true)
    (orth₁₃ F hjk t true) (orth₁₃ F hjl t true) (orth₂₃ F hik s true hc) (orth₂₃ F hil s true hc)
  have h6 :
      Nat.card (leviFix (elementaryGroup Q) (framePair F k true) (framePair F l true)) = 6 := by
    rw [Nat.card_congr (leviFixEquiv _ _ (framePair_orth F hkl true true)
      (eichler_mem_elementaryGroup Q)).toEquiv,
      CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hd := Subgroup.card_dvd_of_le hle
  rw [h6] at hd
  exact dvd_trans (by norm_num) hd

end HypFrame

section Five

theorem exists_one_ne {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) : ∃ k : Fin N, i ≠ k ∧ j ≠ k := by
  classical
  have hcard : 0 < ((Finset.univ.erase i).erase j).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin N))) (a := i)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
  exact ⟨k, Ne.symm hk.2, Ne.symm hk.1⟩

theorem exists_two_ne {N : ℕ} (hN : 4 ≤ N) (i j : Fin N) :
    ∃ k l : Fin N, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  classical
  have hcard : 1 < ((Finset.univ.erase i).erase j).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin N))) (a := i)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨k, l, hk, hl, hkl⟩ := Finset.one_lt_card_iff.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl
  exact ⟨k, l, Ne.symm hk.2, Ne.symm hl.2, Ne.symm hk.1, Ne.symm hl.1, hkl⟩


theorem exists_three_ne {N : ℕ} (hN : 5 ≤ N) (i j : Fin N) :
    ∃ k l m : Fin N, i ≠ k ∧ i ≠ l ∧ i ≠ m ∧ j ≠ k ∧ j ≠ l ∧ j ≠ m ∧ k ≠ l ∧ k ≠ m ∧ l ≠ m := by
  classical
  have hcard : 2 < ((Finset.univ.erase i).erase j).card := by
    have h1 := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := j)
    have h2 := Finset.pred_card_le_card_erase (s := (Finset.univ : Finset (Fin N))) (a := i)
    rw [Finset.card_univ, Fintype.card_fin] at h2
    omega
  obtain ⟨k, l, m, hk, hl, hm, hkl, hkm, hlm⟩ := Finset.two_lt_card_iff.mp hcard
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk hl hm
  exact ⟨k, l, m, Ne.symm hk.2, Ne.symm hl.2, Ne.symm hm.2, Ne.symm hk.1, Ne.symm hl.1,
    Ne.symm hm.1, hkl, hkm, hlm⟩

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {N : ℕ} (F : HypFrame Q N)

theorem ggRCSLayer_hypFrame_five {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) {i j k l m : Fin N} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (him : i ≠ m) (hjk : j ≠ k) (hjl : j ≠ l) (hjm : j ≠ m) (hkl : k ≠ l)
    (hkm : k ≠ m) (hlm : l ≠ m) (s t : Bool) {c : K} (hc : c ≠ 0)
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U}
    (hx : σ x = eichler Q (F.vec j t) (c • F.vec i s))
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayer p ψ.range M (ψ (u * x * u⁻¹)) := by
  have h₁₂ := orth₁₂ F hij s t hc
  have hR := nondegenerate_restrict_wSub hQ h₁₂
  have hT := exists_totallySingular_wSub F hik hil him hjk hjl hjm hkl hkm hlm s t hc
  have : Finite V := Module.finite_of_finite K
  exact ggRCSLayer_frame (P₃ := framePair F l true) hp hp2 hQ hEΩ hOE h₁₂ (orth₁₃ F hjl t true)
    (orth₂₃ F hil s true hc) (y₀ := F.vec k true) (framePair F k true).e_ne_zero
    (inW_frame F hc (fun v => F.polar_vec_of_ne hik v true) (fun v => F.polar_vec_of_ne hjk v true))
    ⟨F.polar_vec_of_ne hkl.symm true true, F.polar_vec_of_ne hkl.symm false true⟩
    (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT)
    (CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hR hT)
    (center_orthDerived_eq_bot' hR hT (exists_restrict_ne_zero F hik hjk hc))
    (fun hK _ => three_dvd_card_omFix F hik hil hjk hjl hkl s t hc hK) hσ hσE hx hxC ψ hψ hG₀M hM u

end Five

section Witt

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {P₁ P₂ : HypPair Q}

theorem linearIndependent_four (h₁₂ : P₁.Orth P₂) :
    LinearIndependent K ![P₁.e, P₂.e, P₁.f, P₂.f] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • P₁.e + g 1 • P₂.e + g 2 • P₁.f + g 3 • P₂.f = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have h21 := h₁₂.symm
  have key : ∀ v : V, g 0 * polar Q P₁.e v + g 1 * polar Q P₂.e v + g 2 * polar Q P₁.f v +
      g 3 * polar Q P₂.f v = 0 := fun v => by
    have := congrArg (fun w => polar Q w v) hg'
    simpa [polar_add_left, polar_smul_left_eq] using this
  have e0 := key P₁.f
  have e1 := key P₂.f
  have e2 := key P₁.e
  have e3 := key P₂.e
  simp only [P₁.polar_ef, P₁.polar_ff, P₁.polar_fe, P₁.polar_ee, P₂.polar_ef, P₂.polar_ff,
    P₂.polar_fe, P₂.polar_ee, h₁₂.ee, h₁₂.ef, h₁₂.fe, h₁₂.ff, h21.ee, h21.ef, h21.fe, h21.ff,
    mul_one, mul_zero, add_zero, zero_add] at e0 e1 e2 e3
  intro i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem linearIndependent_pair_e' (h₁₂ : P₁.Orth P₂) : LinearIndependent K ![P₁.e, P₂.e] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have h1 := congrArg (fun v => polar Q v P₁.f) hab
  have h2 := congrArg (fun v => polar Q v P₂.f) hab
  have h21 := h₁₂.symm
  simp only [polar_add_left, polar_smul_left_eq, P₁.polar_ef, P₂.polar_ef, h₁₂.ef, h21.ef,
    polar_zero_left, mul_one, mul_zero, add_zero, zero_add] at h1 h2
  exact ⟨h1, h2⟩

theorem finrank_spanU₄ (h₁₂ : P₁.Orth P₂) : finrank K (spanU₄ P₁ P₂) = 4 := by
  have h := finrank_span_eq_card (linearIndependent_four h₁₂)
  have hs : Set.range ![P₁.e, P₂.e, P₁.f, P₂.f] = {P₁.e, P₂.e, P₁.f, P₂.f} := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hs, Fintype.card_fin] at h
  exact h

theorem finrank_wSub_add_four [FiniteDimensional K V] (h₁₂ : P₁.Orth P₂) :
    finrank K (wSub P₁ P₂) + 4 = finrank K V := by
  rw [← finrank_spanU₄ h₁₂]
  exact Submodule.finrank_add_eq_of_isCompl (isCompl_wSub_spanU₄ h₁₂)

theorem exists_totallySingular_add_two [FiniteDimensional K V] (h₁₂ : P₁.Orth P₂)
    (T : Submodule K (wSub P₁ P₂)) (hT : ∀ x ∈ T, Q.restrict (wSub P₁ P₂) x = 0) :
    ∃ T' : Submodule K V, finrank K T' = finrank K T + 2 ∧ ∀ x ∈ T', Q x = 0 := by
  set A := T.map (wSub P₁ P₂).subtype with hAdef
  set B := Submodule.span K (Set.range ![P₁.e, P₂.e]) with hBdef
  have hA : finrank K A = finrank K T := Submodule.finrank_map_subtype_eq _ _
  have hB : finrank K B = 2 := by
    rw [hBdef, finrank_span_eq_card (linearIndependent_pair_e' h₁₂), Fintype.card_fin]
  have hBU : B ≤ spanU₄ P₁ P₂ := by
    rw [hBdef, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · exact mem_spanU₄_e₁
    · exact mem_spanU₄_e₂
  have hAW : A ≤ wSub P₁ P₂ := Submodule.map_subtype_le _ _
  have hAB : A ⊓ B = ⊥ := disjoint_iff.mp ((isCompl_wSub_spanU₄ h₁₂).disjoint.mono hAW hBU)
  refine ⟨A ⊔ B, ?_, ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hAB, finrank_bot, add_zero, hA, hB] at h
    exact h
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp ha
    have hQa : Q t = 0 := hT t ht
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hb
    have hQb : Q (∑ k, cf k • ![P₁.e, P₂.e] k) = 0 := by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, P₁.Q_e, P₂.Q_e,
        polar_smul_left_eq, polar_smul_right_eq, h₁₂.ee]
      simp
    have hab : polar Q t (∑ k, cf k • ![P₁.e, P₂.e] k) = 0 :=
      polar_eq_zero_of_inW_of_mem_spanU₄ h₁₂ (mem_wSub.mp t.2) (hBU hb)
    simp only [Submodule.subtype_apply] at hQa hab ⊢
    rw [QuadraticMap.map_add Q, hQa, hQb, hab, add_zero, add_zero]

end Witt

end RCSTOm

end CFSG.StandardType
