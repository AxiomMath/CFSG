module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLD6GenAux

public section

namespace CFSG.StandardType.QTwoD6

open Module

private theorem qd6g_perm_part (σ : Equiv.Perm (Fin 6)) :
    (∃ h ∈ W6, h e0 = e0 ∧ ∀ a, h (epsVec a) = epsVec (σ a)) ∧
      (∀ g : V7 ≃ₗ[ZMod 3] V7, g e0 = e0 → (∀ a, g (epsVec a) = epsVec (σ a)) → g ∈ W6) := by
  have hclosure :
      Submonoid.closure (Set.range fun i : Fin 5 => Equiv.swap i.castSucc i.succ) = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ 5
  refine Submonoid.dense_induction _ hclosure ?_ ?_ ?_ σ
  · rintro τ ⟨i, rfl⟩
    refine ⟨⟨simpleD6 i.castSucc, Subgroup.subset_closure ⟨i.castSucc, rfl⟩, qd6g_simple_e0 _,
      fun a => qd6g_simple_eps_adj i a⟩, ?_⟩
    intro g hg0 hgeps
    have hgh : g = simpleD6 i.castSucc := qd6g_linEquiv_ext (by rw [hg0, qd6g_simple_e0])
      (by intro a; rw [hgeps a, qd6g_simple_eps_adj])
    rw [hgh]
    exact Subgroup.subset_closure ⟨i.castSucc, rfl⟩
  · refine ⟨⟨1, one_mem _, by simp, fun a => by simp⟩, ?_⟩
    intro g hg0 hgeps
    have hg1 : g = 1 := qd6g_linEquiv_ext (by simpa using hg0) (by intro a; simpa using hgeps a)
    rw [hg1]
    exact one_mem _
  · rintro σ τ ⟨⟨hσ, hσW, hσ0, hσeps⟩, hσmem⟩ ⟨⟨hτ, hτW, hτ0, hτeps⟩, hτmem⟩
    refine ⟨⟨hσ * hτ, mul_mem hσW hτW, ?_, ?_⟩, ?_⟩
    · change hσ (hτ e0) = e0
      rw [hτ0, hσ0]
    · intro a
      change hσ (hτ (epsVec a)) = epsVec ((σ * τ) a)
      rw [hτeps a, hσeps]
      rfl
    · intro g hg0 hgeps
      have hg'0 : (g * hτ⁻¹) e0 = e0 := by
        change g (hτ⁻¹ e0) = e0
        have hτinv0 : hτ⁻¹ e0 = e0 := by
          have := congrArg (fun v => hτ⁻¹ v) hτ0
          simpa using this.symm
        rw [hτinv0, hg0]
      have hg'eps : ∀ a, (g * hτ⁻¹) (epsVec a) = epsVec (σ a) := by
        intro a
        change g (hτ⁻¹ (epsVec a)) = epsVec (σ a)
        have hτinv : hτ⁻¹ (epsVec a) = epsVec (τ⁻¹ a) := by
          have := congrArg (fun v => hτ⁻¹ v) (hτeps (τ⁻¹ a))
          simpa using this.symm
        rw [hτinv, hgeps]
        simp
      have hg'W : g * hτ⁻¹ ∈ W6 := hσmem (g * hτ⁻¹) hg'0 hg'eps
      have hgeq : g = (g * hτ⁻¹) * hτ := by group
      rw [hgeq]
      exact mul_mem hg'W hτW

private theorem qd6g_pair_perm (a b : Fin 6) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 6), σ 4 = a ∧ σ 5 = b := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 2 => if i = 0 then (4 : Fin 6) else 5)
    (fun i : Fin 2 => if i = 0 then a else b)
    (by decide) (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨σ, hσ 0, hσ 1⟩

private theorem qd6g_prod_sign (s : Fin 6 → ZMod 3) (hs : ∀ a, s a = 1 ∨ s a = -1) :
    (∏ a, s a) = 1 ∨ (∏ a, s a) = -1 := by
  have h : ∀ t : Finset (Fin 6), (∏ a ∈ t, s a) = 1 ∨ (∏ a ∈ t, s a) = -1 := by
    intro t
    induction t using Finset.induction_on with
    | empty => left; simp
    | insert a t ha ih =>
      rw [Finset.prod_insert ha]
      rcases ih with ih | ih <;> rcases hs a with h | h <;> rw [ih, h]
      · left; ring
      · right; ring
      · right; ring
      · left; ring
  simpa using h Finset.univ

private theorem qd6g_prod_update (s : Fin 6 → ZMod 3) (b : Fin 6) (hsb : s b ≠ 0) :
    (∏ a, (if a = b then -s b else s a)) = -∏ a, s a := by
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ b)
        (fun a => if a = b then -s b else s a),
    Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ b) s]
  have hdiff : (∏ x ∈ Finset.univ \ {b}, (if x = b then -s b else s x)) =
      ∏ x ∈ Finset.univ \ {b}, s x := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hx
    rw [if_neg hx.2]
  rw [hdiff, if_pos rfl, neg_mul]

private theorem qd6g_pair_flip (a b : Fin 6) (hab : a ≠ b) :
    ∃ f ∈ W6, f e0 = e0 ∧ f (epsVec a) = -epsVec a ∧ f (epsVec b) = -epsVec b ∧
      (∀ c, c ≠ a → c ≠ b → f (epsVec c) = epsVec c) := by
  obtain ⟨σ, hσ4, hσ5⟩ := qd6g_pair_perm a b hab
  obtain ⟨⟨hσ, hσW, hσ0, hσeps⟩, -⟩ := qd6g_perm_part σ
  let f45 : V7 ≃ₗ[ZMod 3] V7 := simpleD6 4 * simpleD6 5
  have hf45W : f45 ∈ W6 :=
    mul_mem (Subgroup.subset_closure ⟨4, rfl⟩) (Subgroup.subset_closure ⟨5, rfl⟩)
  have hf45e0 : f45 e0 = e0 := qd6g_f45_e0
  have hσinv0 : hσ⁻¹ e0 = e0 := by
    have := congrArg (fun v => hσ⁻¹ v) hσ0
    simpa using this.symm
  have hσinv_eps : ∀ c, hσ⁻¹ (epsVec c) = epsVec (σ⁻¹ c) := by
    intro c
    have := congrArg (fun v => hσ⁻¹ v) (hσeps (σ⁻¹ c))
    simpa using this.symm
  refine ⟨hσ * f45 * hσ⁻¹, mul_mem (mul_mem hσW hf45W) (inv_mem hσW), ?_, ?_, ?_, ?_⟩
  · change hσ (f45 (hσ⁻¹ e0)) = e0
    rw [hσinv0, hf45e0, hσ0]
  · change hσ (f45 (hσ⁻¹ (epsVec a))) = -epsVec a
    have hsa : σ⁻¹ a = 4 := by rw [← hσ4]; exact Equiv.symm_apply_apply σ 4
    rw [hσinv_eps a, hsa, qd6g_f45_4, map_neg, hσeps 4, hσ4]
  · change hσ (f45 (hσ⁻¹ (epsVec b))) = -epsVec b
    have hsb : σ⁻¹ b = 5 := by rw [← hσ5]; exact Equiv.symm_apply_apply σ 5
    rw [hσinv_eps b, hsb, qd6g_f45_5, map_neg, hσeps 5, hσ5]
  · intro c hca hcb
    change hσ (f45 (hσ⁻¹ (epsVec c))) = epsVec c
    have hc4 : σ⁻¹ c ≠ 4 := by
      intro h
      exact hca ((Equiv.apply_symm_apply σ c).symm.trans ((congrArg σ h).trans hσ4))
    have hc5 : σ⁻¹ c ≠ 5 := by
      intro h
      exact hcb ((Equiv.apply_symm_apply σ c).symm.trans ((congrArg σ h).trans hσ5))
    rw [hσinv_eps c, qd6g_f45_of_ne (σ⁻¹ c) hc4 hc5, hσeps]
    simp

private theorem qd6g_sign_exists (t : Finset (Fin 6)) (ht : Even t.card) :
    ∃ w ∈ W6, w e0 = e0 ∧ ∀ a, w (epsVec a) = (if a ∈ t then (-1 : ZMod 3) else 1) • epsVec a := by
  revert ht
  induction t using Finset.strongInductionOn with
  | _ t ih =>
    intro ht
    by_cases h0 : t.card = 0
    · have ht0 : t = ∅ := Finset.card_eq_zero.mp h0
      subst ht0
      exact ⟨1, one_mem _, by simp, fun a => by simp⟩
    · have hlt : 1 < t.card := by
        rcases ht with ⟨k, hk⟩
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hlt
      have hb' : b ∈ t.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
      have hcard : ((t.erase a).erase b).card = t.card - 2 := by
        rw [Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
        omega
      have ht2sub : (t.erase a).erase b ⊂ t := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_erase] at hx
          exact hx.2.2
        · intro heq
          have := congrArg Finset.card heq
          omega
      have ht2even : Even ((t.erase a).erase b).card := by
        rw [hcard]
        rcases ht with ⟨k, hk⟩
        exact ⟨k - 1, by omega⟩
      obtain ⟨w2, hw2W, hw2e0, hw2⟩ := ih ((t.erase a).erase b) ht2sub ht2even
      obtain ⟨f, hfW, hfe0, hfa, hfb, hfc⟩ := qd6g_pair_flip a b hab
      refine ⟨f * w2, mul_mem hfW hw2W, ?_, ?_⟩
      · change f (w2 e0) = e0
        rw [hw2e0, hfe0]
      · intro c
        change f (w2 (epsVec c)) = (if c ∈ t then -1 else 1) • epsVec c
        by_cases hca : c = a
        · subst hca
          have ha2 : c ∉ (t.erase c).erase b := by simp [Finset.mem_erase]
          rw [hw2, if_neg ha2, one_smul, hfa, if_pos ha]
          simp
        · by_cases hcb : c = b
          · subst hcb
            have hb2 : c ∉ (t.erase a).erase c := by simp [Finset.mem_erase]
            rw [hw2, if_neg hb2, one_smul, hfb, if_pos hb]
            simp
          · by_cases hct : c ∈ t
            · have hct2 : c ∈ (t.erase a).erase b := by
                simp only [Finset.mem_erase]
                exact ⟨hcb, hca, hct⟩
              rw [hw2, if_pos hct2, if_pos hct]
              simp [hfc c hca hcb]
            · have hct2 : c ∉ (t.erase a).erase b := by
                intro h
                have h' := h
                simp only [Finset.mem_erase] at h'
                exact hct h'.2.2
              rw [hw2, if_neg hct2, if_neg hct]
              simp [hfc c hca hcb]

private theorem qd6g_prod_eq_one_even (s : Fin 6 → ZMod 3) (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hprod : ∏ a, s a = 1) : Even (Finset.univ.filter (fun a => s a = -1)).card := by
  have h1 : ∏ a, s a = ∏ a, (if s a = -1 then (-1 : ZMod 3) else 1) := by
    apply Finset.prod_congr rfl
    intro a _
    rcases hs a with h | h <;> simp [h]
  rw [h1] at hprod
  have h2 : (∏ a, (if s a = -1 then (-1 : ZMod 3) else 1)) =
      (-1 : ZMod 3) ^ (Finset.univ.filter (fun a => s a = -1)).card := by
    rw [show (∏ a, (if s a = -1 then (-1 : ZMod 3) else 1)) =
        ∏ a, (if a ∈ Finset.univ.filter (fun a => s a = -1) then (-1 : ZMod 3) else 1) by
      apply Finset.prod_congr rfl
      intro a _
      simp]
    rw [Finset.prod_ite_mem, Finset.prod_const, Finset.univ_inter]
  rw [h2] at hprod
  exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hprod

private theorem qd6g_mono_mem (g : V7 ≃ₗ[ZMod 3] V7) (σ : Equiv.Perm (Fin 6))
    (s : Fin 6 → ZMod 3) (hs : ∀ a, s a = 1 ∨ s a = -1) (hprod : ∏ a, s a = 1)
    (h0 : g e0 = e0) (hg : ∀ a, g (epsVec a) = s a • epsVec (σ a)) : g ∈ W6 := by
  obtain ⟨⟨hσ, hσW, hσ0, hσeps⟩, -⟩ := qd6g_perm_part σ
  have hσinv0 : hσ⁻¹ e0 = e0 := by
    have := congrArg (fun v => hσ⁻¹ v) hσ0
    simpa using this.symm
  have hσinv_eps : ∀ a, hσ⁻¹ (epsVec a) = epsVec (σ⁻¹ a) := by
    intro a
    have := congrArg (fun v => hσ⁻¹ v) (hσeps (σ⁻¹ a))
    simpa using this.symm
  have hd0 : (hσ⁻¹ * g) e0 = e0 := by
    change hσ⁻¹ (g e0) = e0
    rw [h0, hσinv0]
  have hd : ∀ a, (hσ⁻¹ * g) (epsVec a) = s a • epsVec a := by
    intro a
    change hσ⁻¹ (g (epsVec a)) = s a • epsVec a
    rw [hg a, map_smul, hσinv_eps (σ a)]
    simp
  obtain ⟨w, hwW, hwe0, hw⟩ := qd6g_sign_exists (Finset.univ.filter (fun a => s a = -1))
    (qd6g_prod_eq_one_even s hs hprod)
  have hsaeq : ∀ a, s a = (if a ∈ Finset.univ.filter (fun a => s a = -1) then
      (-1 : ZMod 3) else 1) := by
    intro a
    by_cases h : a ∈ Finset.univ.filter (fun a => s a = -1)
    · rw [if_pos h]
      exact (Finset.mem_filter.mp h).2
    · rw [if_neg h]
      rcases hs a with h1 | h1
      · exact h1
      · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ a, h1⟩) h
  have hd_eq_w : hσ⁻¹ * g = w := qd6g_linEquiv_ext (by rw [hd0, hwe0]) (by
    intro a
    rw [hd a, hw a, hsaeq a])
  have hgeq : g = hσ * w := by
    rw [← hd_eq_w]
    group
  rw [hgeq]
  exact mul_mem hσW hwW

theorem monomial_normal_form (T : V7 ≃ₗ[ZMod 3] V7) (σ : Equiv.Perm (Fin 6))
    (s : Fin 6 → ZMod 3) (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hT0 : T e0 ∈ Submodule.span (ZMod 3) {e0}) (hT : ∀ a, T (epsVec a) = s a • epsVec (σ a)) :
    ∃ w ∈ W6, ∃ π : Fin 6 ≃ Fin 6, (π = Equiv.refl _ ∨ π = swapD6) ∧
      ∀ i, T (hvec i) = w (hvec (π i)) := by
  obtain ⟨lam, hlam_eq⟩ := Submodule.mem_span_singleton.mp hT0
  have hTe0 : T e0 = lam • e0 := hlam_eq.symm
  have hlam : lam ≠ 0 := by
    intro h
    have h1 : T e0 = 0 := by rw [hTe0, h, zero_smul]
    have h2 : e0 = 0 := T.injective (by rw [h1, map_zero])
    exact absurd h2 (by decide)
  rcases qd6g_prod_sign s hs with hP | hP
  · refine ⟨T * qd6g_kappa lam hlam, ?_, Equiv.refl _, Or.inl rfl, ?_⟩
    · refine qd6g_mono_mem (T * qd6g_kappa lam hlam) σ s hs hP ?_ ?_
      · change T (qd6g_kappa lam hlam e0) = e0
        rw [qd6g_kappa_e0, map_smul, hTe0, smul_smul, inv_mul_cancel₀ hlam, one_smul]
      · intro a
        change T (qd6g_kappa lam hlam (epsVec a)) = s a • epsVec (σ a)
        rw [qd6g_kappa_eps, hT a]
    · intro i
      change T (hvec i) = T (qd6g_kappa lam hlam (hvec i))
      rw [qd6g_kappa_hvec]
  · let s' : Fin 6 → ZMod 3 := fun a => if a = 5 then -s 5 else s a
    have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := by
      intro a
      by_cases h : a = 5
      · subst h
        change (if (5 : Fin 6) = 5 then -s 5 else s 5) = 1 ∨
          (if (5 : Fin 6) = 5 then -s 5 else s 5) = -1
        rw [if_pos rfl]
        rcases hs 5 with h5 | h5 <;> rw [h5]
        · right; rfl
        · left; rfl
      · change (if a = 5 then -s 5 else s a) = 1 ∨ (if a = 5 then -s 5 else s a) = -1
        rw [if_neg h]
        exact hs a
    have hs5 : s 5 ≠ 0 := by
      rcases hs 5 with h5 | h5 <;> rw [h5] <;> decide
    have hprod' : ∏ a, s' a = 1 := by
      have h := qd6g_prod_update s 5 hs5
      change (∏ a, (if a = 5 then -s 5 else s a)) = 1
      rw [h, hP]
      ring
    refine ⟨T * qd6g_tau * qd6g_kappa lam hlam, ?_, swapD6, Or.inr rfl, ?_⟩
    · refine qd6g_mono_mem (T * qd6g_tau * qd6g_kappa lam hlam) σ s' hs' hprod' ?_ ?_
      · change T (qd6g_tau (qd6g_kappa lam hlam e0)) = e0
        rw [qd6g_kappa_e0, map_smul, qd6g_tau_e0, map_smul, hTe0, smul_smul,
          inv_mul_cancel₀ hlam, one_smul]
      · intro a
        change T (qd6g_tau (qd6g_kappa lam hlam (epsVec a))) = s' a • epsVec (σ a)
        rw [qd6g_kappa_eps, qd6g_tau_eps]
        by_cases h : a = 5
        · subst h
          rw [if_pos rfl, map_neg, hT 5]
          change - (s 5 • epsVec (σ 5)) = (if (5 : Fin 6) = 5 then -s 5 else s 5) •
            epsVec (σ 5)
          rw [if_pos rfl, neg_smul]
        · rw [if_neg h, hT a]
          change s a • epsVec (σ a) = (if a = 5 then -s 5 else s a) • epsVec (σ a)
          rw [if_neg h]
    · intro i
      change T (hvec i) = T (qd6g_tau (qd6g_kappa lam hlam (hvec (swapD6 i))))
      rw [qd6g_kappa_hvec, qd6g_tau_hvec]
      have hinv : swapD6 (swapD6 i) = i := by fin_cases i <;> decide +kernel
      rw [hinv]

end CFSG.StandardType.QTwoD6

end
