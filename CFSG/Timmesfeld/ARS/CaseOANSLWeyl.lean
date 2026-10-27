module

public import CFSG.Timmesfeld.ARS.CaseEPointType
public import CFSG.Timmesfeld.ARS.ExclNSChain

public section

namespace CFSG.Timmesfeld.ARS.CaseOANSL

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg ExclNS

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A) (P : EpsCoords A)

abbrev parJ : Subgroup (coxeterMatrix hA).Group :=
  (coxeterMatrix hA).toCoxeterSystem.parabolic {k : Fin n | k.val ≠ 0}

theorem E_single_zero (hn : 2 ≤ n) :
    P.E (Pi.single (⟨0, by omega⟩ : Fin n) 1) = ev n 0 - ev n 1 :=
  P.single _ (by simp only; omega)

theorem exists_dominant (hn : 2 ≤ n) :
    ∃ l : Fin n → ℤ, P.E l = P.c • ev n 0 ∧
      (∀ w, weylAction hA w l = l → w ∈ parJ hA) ∧
      ∀ w, weylAction hA w l = l ∨ weylAction hA w l = -l ∨
        ∃ u ∈ parJ hA, ∃ v ∈ parJ hA,
          w = u * (coxeterMatrix hA).toCoxeterSystem.simple (⟨0, by omega⟩ : Fin n) * v := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  set J : Set (Fin n) := {k | k.val ≠ 0} with hJ
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  obtain ⟨w', hw'⟩ := CaseE.exists_eps_weylAction_last hA P (by omega)
  set l := weylAction hA w' (Pi.single last 1) with hl
  have hQ : ∀ k, P.invForm.Q l (Pi.single k 1) = if k.val = 0 then P.c else 0 := by
    intro k
    rw [EpsCoords.invForm_apply, hw']
    by_cases h : k.val + 1 < n
    · rw [P.single k h]
      simp only [smul_dotProduct, dotProduct_sub, ev_dotProduct_ev, smul_eq_mul]
      rw [ite_eq_right (show ¬ (0 = k.val + 1 ∧ 0 < n) by omega)]
      by_cases hk : k.val = 0
      · rw [ite_eq_left ⟨hk.symm, by omega⟩, ite_eq_left hk]
        ring
      · rw [ite_eq_right (fun h' => hk h'.1.symm), ite_eq_right hk]
        ring
    · rw [P.last k h]
      simp only [smul_dotProduct, dotProduct_smul, ev_dotProduct_ev, smul_eq_mul]
      have hk : k.val ≠ 0 := by omega
      rw [ite_eq_right (fun h' => hk h'.1.symm), ite_eq_right hk]
      ring
  have hstab : ∀ w, weylAction hA w l = l → w ∈ cs.parabolic J := by
    intro w hw
    have hdom : ∀ k, 0 ≤ P.invForm.Q l (Pi.single k 1) := fun k => by
      rw [hQ]
      split_ifs
      exacts [P.c_pos.le, le_rfl]
    have h := P.invForm.mem_closure_of_weylAction_eq hA hdom w hw
    have hset : {k | P.invForm.Q l (Pi.single k 1) = 0} = J := by
      ext k
      show P.invForm.Q l (Pi.single k 1) = 0 ↔ k.val ≠ 0
      rw [hQ]
      split_ifs with h0
      · simp [h0, P.c_pos.ne']
      · simp [h0]
    rw [hset] at h
    refine (Subgroup.closure_le _).2 ?_ h
    rintro _ ⟨k, hk, rfl⟩
    exact cs.simple_mem_parabolic hk
  have hlast' : ∀ w, ∀ b < n, b ≠ 0 →
      (P.E (weylAction hA w l) = P.c • ev n b ∨ P.E (weylAction hA w l) = -(P.c • ev n b)) →
      ∃ z ∈ cs.parabolic J, weylAction hA (z * w) l = Pi.single last 1 := by
    intro w b hb hb0 hE
    have hsupp : ∀ k ∉ J, weylAction hA (w * w') (Pi.single last 1) k = 0 := by
      intro k hk
      have hk0 : k = ⟨0, by omega⟩ := Fin.ext (by simpa [hJ] using hk)
      subst hk0
      rw [weylAction_mul_apply, ← hl]
      have e := CaseE.eps_apply_zero P hn (weylAction hA w l)
      rw [← e]
      have hb0' : (0 : ℕ) ≠ b := Ne.symm hb0
      rcases hE with hE | hE <;> rw [hE] <;> simp [ev, hb0']
    obtain ⟨z, hz, m, -, hzm⟩ := exists_parabolic_of_support hA J (w * w') last hsupp
    have hzl : weylAction hA (z * w) l = Pi.single m 1 := by
      rw [weylAction_mul_apply, hl, ← weylAction_mul_apply hA w, hzm]
    have hmlast : m = last := by
      obtain ⟨b', -, hE'⟩ := CaseE.exists_eps_weylAction hA P (z * w) (v := l) (x := P.c)
        (b := 0) (by omega) (Or.inl hw')
      rw [hzl] at hE'
      by_contra hne
      have hm1 : m.val + 1 < n := by
        have h1 := m.isLt
        have h2 : m.val ≠ n - 1 := fun e => hne (Fin.ext e)
        omega
      rw [P.single m hm1] at hE'
      rcases hE' with hE' | hE' <;>
      · have e1 := congrFun hE' ⟨m.val, m.isLt⟩
        have e2 := congrFun hE' ⟨m.val + 1, hm1⟩
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, ev, smul_eq_mul] at e1 e2
        split_ifs at e1 e2 <;> omega
    exact ⟨z, hz, hmlast ▸ hzl⟩
  have hs₀ : P.E (weylAction hA (cs.simple ⟨0, by omega⟩) l) = P.c • ev n 1 := by
    rw [weylAction_simple, P.refl, hw', stdReflB_smul, stdReflB_ev_of_lt (by simp only; omega)]
    congr 2
  obtain ⟨z₀, hz₀, hz₀l⟩ := hlast' (cs.simple ⟨0, by omega⟩) 1 (by omega) (by omega)
    (Or.inl hs₀)
  refine ⟨l, hw', hstab, fun w => ?_⟩
  obtain ⟨b, hb, hE⟩ := CaseE.exists_eps_weylAction hA P w (v := l) (x := P.c) (b := 0)
    (by omega) (Or.inl hw')
  by_cases hb0 : b = 0
  · subst hb0
    rcases hE with hE | hE
    · exact Or.inl (P.inj (hE.trans hw'.symm))
    · exact Or.inr (Or.inl (P.inj (by rw [hE, map_neg, hw'])))
  · obtain ⟨z, hz, hzl⟩ := hlast' w b hb hb0 hE
    right
    right
    have hv : (z₀ * cs.simple ⟨0, by omega⟩)⁻¹ * (z * w) ∈ cs.parabolic J := by
      refine hstab _ ?_
      rw [weylAction_mul_apply, hzl, ← hz₀l, weylAction_inv_apply_apply]
    refine ⟨z⁻¹ * z₀, mul_mem (inv_mem hz) hz₀, _, hv, ?_⟩
    group

theorem exists_parJ_eq_add (hn : 2 ≤ n) {l : Fin n → ℤ} (hl : P.E l = P.c • ev n 0)
    (hstab : ∀ w, weylAction hA w l = l → w ∈ parJ hA) :
    ∃ u ∈ parJ hA, P.E (weylAction hA u (Pi.single (⟨0, by omega⟩ : Fin n) 1)) =
      ev n 0 + ev n 1 := by
  set vs : Fin 2 → Fin n → ℤ := ![Pi.single (⟨0, by omega⟩ : Fin n) 1, l] with hvs
  have h0 : Reach hA P vs fun i => (![1, P.c] : Fin 2 → ℤ) i • ev n 0 +
      (![-1, 0] : Fin 2 → ℤ) i • ev n 1 := by
    obtain ⟨w, hw⟩ := Reach.refl (hA := hA) (P := P) vs
    refine ⟨w, fun i => ?_⟩
    rw [hw i]
    fin_cases i
    · simp only [vs, Fin.zero_eta, Matrix.cons_val_zero, E_single_zero P hn]
      simp [sub_eq_add_neg]
    · simp only [vs, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hl]
      simp
  obtain ⟨u, hu⟩ := h0.neg_snd (by omega) (by omega)
  refine ⟨u, hstab u (P.inj ?_), ?_⟩
  · have := hu 1
    simp only [vs, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, hl]
    simp
  · have := hu 0
    simp only [vs, Matrix.cons_val_zero] at this
    rw [this]
    simp

theorem exists_weyl_neg (hn : 2 ≤ n) {l γ : Fin n → ℤ} (hl : P.E l = P.c • ev n 0)
    (hγ : P.E γ = ev n 0 + ev n 1) :
    ∃ y, weylAction hA y (Pi.single (⟨0, by omega⟩ : Fin n) 1) = -γ ∧
      weylAction hA y γ = -Pi.single (⟨0, by omega⟩ : Fin n) 1 ∧ weylAction hA y l = -l := by
  set vs : Fin 3 → Fin n → ℤ := ![Pi.single (⟨0, by omega⟩ : Fin n) 1, γ, l] with hvs
  have h0 : Reach hA P vs fun i => (![1, 1, P.c] : Fin 3 → ℤ) i • ev n 0 +
      (![-1, 1, 0] : Fin 3 → ℤ) i • ev n (0 + 1) := by
    obtain ⟨w, hw⟩ := Reach.refl (hA := hA) (P := P) vs
    refine ⟨w, fun i => ?_⟩
    rw [hw i]
    fin_cases i
    · simp only [vs, Fin.zero_eta, Matrix.cons_val_zero, E_single_zero P hn]
      simp [sub_eq_add_neg]
    · simp only [vs, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hγ]
      simp
    · simp only [vs, Fin.reduceFinMk, Matrix.cons_val, hl]
      simp
  have h1 := h0.swap_fst_snd (by omega)
  have h2 := h1.neg_snd (by omega) (by omega)
  have h3 := h2.swap_fst_snd (by omega)
  obtain ⟨y, hy⟩ := h3
  refine ⟨y, P.inj ?_, P.inj ?_, P.inj ?_⟩
  · have := hy 0
    simp only [vs, Matrix.cons_val_zero] at this
    rw [this, map_neg, hγ]
    simp
    abel
  · have := hy 1
    simp only [vs, Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [this, map_neg, E_single_zero P hn]
    simp
    abel
  · have := hy 2
    simp only [vs, Matrix.cons_val] at this
    rw [this, map_neg, hl]
    simp

end CFSG.Timmesfeld.ARS.CaseOANSL
