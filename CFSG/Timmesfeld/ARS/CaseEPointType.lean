module

public import CFSG.Timmesfeld.ARS.CaseEPointCount
public import CFSG.Timmesfeld.ARS.ExclNSClassical
public import CFSG.Timmesfeld.ARS.ExclNSPointDefs

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace CaseE

open ExclNS

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ} (hA : TauCeti.IsFiniteType A) (P : EpsCoords A)

theorem eps_apply_zero (hn : 2 ≤ n) (v : Fin n → ℤ) :
    P.E v ⟨0, by omega⟩ = v ⟨0, by omega⟩ := by
  conv_lhs => rw [← sum_smul_single v]
  rw [map_sum, Finset.sum_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · rw [map_zsmul, Pi.smul_apply, P.single _ (by simp only; omega)]
    simp [ev]
  · intro k _ hk
    have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
    rw [map_zsmul, Pi.smul_apply]
    have hk0' : (0 : ℕ) ≠ k.val := Ne.symm hk0
    by_cases h : k.val + 1 < n
    · rw [P.single k h]
      simp [ev, hk0']
    · rw [P.last k h]
      simp [ev, hk0']
  · simp

theorem exists_eps_weylAction (w : (coxeterMatrix hA).Group) {v : Fin n → ℤ} {x : ℤ}
    {b : ℕ} (hb : b < n) (hv : P.E v = x • ev n b ∨ P.E v = -(x • ev n b)) :
    ∃ b' < n, P.E (weylAction hA w v) = x • ev n b' ∨
      P.E (weylAction hA w v) = -(x • ev n b') := by
  induction w using (coxeterMatrix hA).toCoxeterSystem.simple_induction_left with
  | one => exact ⟨b, hb, by simpa using hv⟩
  | mul_simple_left w k ih =>
    obtain ⟨b', hb', h⟩ := ih
    rw [weylAction_mul_apply, weylAction_simple, P.refl]
    by_cases hk : k.val + 1 < n
    · refine ⟨swapN k.val b', by simp only [swapN]; split_ifs <;> omega, ?_⟩
      rcases h with h | h <;> rw [h]
      · left
        rw [stdReflB_smul, stdReflB_ev_of_lt hk]
      · right
        rw [stdReflB_neg, stdReflB_smul, stdReflB_ev_of_lt hk]
    · refine ⟨b', hb', ?_⟩
      rcases h with h | h <;> rw [h]
      · rw [stdReflB_smul, stdReflB_ev_of_not_lt hk]
        split_ifs
        · right
          rw [smul_neg]
        · left
          rfl
      · rw [stdReflB_neg, stdReflB_smul, stdReflB_ev_of_not_lt hk]
        split_ifs
        · left
          rw [smul_neg, neg_neg]
        · right
          rfl

theorem exists_eps_weylAction_last (hn : 1 ≤ n) :
    ∃ w : (coxeterMatrix hA).Group,
      P.E (weylAction hA w (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) = P.c • ev n 0 := by
  have key : ∀ j, j ≤ n - 1 → ∃ w : (coxeterMatrix hA).Group,
      P.E (weylAction hA w (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) = P.c • ev n (n - 1 - j) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨1, ?_⟩
      rw [map_one, Module.End.one_apply, P.last _ (by simp only; omega)]
      rfl
    | succ j ih =>
      intro hj
      obtain ⟨w, hw⟩ := ih (by omega)
      set k : Fin n := ⟨n - 2 - j, by omega⟩
      have hk : k.val + 1 < n := by simp only [k]; omega
      refine ⟨(coxeterMatrix hA).toCoxeterSystem.simple k * w, ?_⟩
      rw [weylAction_mul_apply, weylAction_simple, P.refl, hw, stdReflB_smul,
        stdReflB_ev_of_lt hk]
      congr 2
      simp only [swapN, k]
      split_ifs <;> omega
  obtain ⟨w, hw⟩ := key (n - 1) le_rfl
  refine ⟨w, ?_⟩
  rw [hw, Nat.sub_self]

include P in
theorem exists_doubleCoset_three (hn : 2 ≤ n) :
    ∃ x : Fin 3 → (coxeterMatrix hA).Group, ∀ w, ∃ i,
      ∃ u ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k.val ≠ 0},
      ∃ v ∈ (coxeterMatrix hA).toCoxeterSystem.parabolic {k | k.val ≠ 0}, w = u * x i * v := by
  set cs := (coxeterMatrix hA).toCoxeterSystem
  set J : Set (Fin n) := {k | k.val ≠ 0} with hJ
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  obtain ⟨w', hw'⟩ := exists_eps_weylAction_last hA P (by omega)
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
  set x₂ := w' * cs.simple last * w'⁻¹ with hx₂
  have hx₂l : weylAction hA x₂ l = -l := by
    rw [hx₂, hl, weylAction_mul_apply, weylAction_mul_apply, weylAction_inv_apply_apply,
      weylAction_simple_single, map_neg]
  refine ⟨![1, w'⁻¹, x₂], fun w => ?_⟩
  obtain ⟨b, hb, hE⟩ := exists_eps_weylAction hA P w (v := l) (x := P.c) (b := 0) (by omega)
    (Or.inl hw')
  by_cases hb0 : b = 0
  · subst hb0
    rcases hE with hE | hE
    ·
      refine ⟨0, 1, one_mem _, w, hstab w (P.inj (hE.trans hw'.symm)), ?_⟩
      simp
    ·
      have hwl : weylAction hA w l = -l := P.inj (by rw [hE, map_neg, hw'])
      refine ⟨2, 1, one_mem _, x₂⁻¹ * w, hstab _ ?_, ?_⟩
      · rw [weylAction_mul_apply, hwl, ← hx₂l, weylAction_inv_apply_apply]
      · simp
  ·
    have hsupp : ∀ k ∉ J, weylAction hA (w * w') (Pi.single last 1) k = 0 := by
      intro k hk
      have hk0 : k = ⟨0, by omega⟩ := Fin.ext (by simpa [hJ] using hk)
      subst hk0
      rw [weylAction_mul_apply, ← hl]
      have e := eps_apply_zero P hn (weylAction hA w l)
      rw [← e]
      have hb0' : (0 : ℕ) ≠ b := Ne.symm hb0
      rcases hE with hE | hE <;> rw [hE] <;> simp [ev, hb0']
    obtain ⟨z, hz, m, -, hzm⟩ := exists_parabolic_of_support hA J (w * w') last hsupp
    have hzl : weylAction hA (z * w) l = Pi.single m 1 := by
      rw [weylAction_mul_apply, hl, ← weylAction_mul_apply hA w, hzm]
    have hmlast : m = last := by
      obtain ⟨b', -, hE'⟩ := exists_eps_weylAction hA P (z * w) (v := l) (x := P.c) (b := 0)
        (by omega) (Or.inl hw')
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
    subst hmlast
    refine ⟨1, z⁻¹, inv_mem hz, w' * z * w, hstab _ ?_, ?_⟩
    · rw [mul_assoc, weylAction_mul_apply, hzl]
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      group

end CaseE

theorem ExclNS.pointTypeInput : ExclNS.PointTypeInput := by
  intro G _ R A A₀ hS F B hBC hrank hB hT hn
  obtain ⟨P⟩ : Nonempty (ExclNS.EpsCoords F.D.cartan) := by
    rcases hBC with h | h
    · exact ⟨h ▸ ExclNS.epsB F.D.rank⟩
    · exact ⟨h ▸ ExclNS.epsC F.D.rank⟩
  obtain ⟨x, hx⟩ := CaseE.exists_doubleCoset_three F.D.isFiniteType P (by omega)
  refine false_of_doubleCoset_three hS F.hct F.hext F.Ψ F.surj hB.mem ?_
    (J := {k | k.val ≠ 0}) (fun k hk => hn k hk) x hx
  rw [Subgroup.map_sup]
  exact sup_le hT hB.le

end CFSG.Timmesfeld.ARS
