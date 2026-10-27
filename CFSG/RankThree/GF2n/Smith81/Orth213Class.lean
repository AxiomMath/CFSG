module

public import CFSG.RankThree.GF2n.Smith81.Orth213Stmts
public import CFSG.RankThree.GF2n.Smith81.Orth213ClassCount
public import CFSG.RankThree.GF2n.Smith81.Orth213ClassAFrame
public import CFSG.RankThree.GF2n.Smith81.Lin28CondRest

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement Matrix

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

@[expose] def ClassConcl (C : OrthCtx M Q Z B) (x : G) : Prop :=
  (∃ g : Matrix (Fin 2) (Fin 2) C.K, g.det = 1 ∧ g ≠ 1 ∧ (g - 1) * (g - 1) = 0 ∧
      ActsAsTensor Q Z C.M₀ C.φ x g id) ∨
  (∃ u w : C.ι → C.K, C.qU u = 0 ∧ C.qU w = 0 ∧ QuadraticMap.polar C.qU u w = 0 ∧
      LinearIndependent C.K ![u, w] ∧
      ActsAsTensor Q Z C.M₀ C.φ x 1 ⇑(eichler C.qU u w))

theorem actsAsTensor_of_change {C : OrthCtx M Q Z B} {x : G} (h : GL (Fin 2) C.K)
    (hdet : (h : Matrix (Fin 2) (Fin 2) C.K).det = 1) {g' : Matrix (Fin 2) (Fin 2) C.K}
    {o : (C.ι → C.K) → (C.ι → C.K)} (ho : ∀ a b, o (a + b) = o a + o b)
    (ho' : ∀ (c : C.K) a, o (c • a) = c • o a)
    (hact : ActsAsTensor Q Z (C.change h hdet).M₀ (C.change h hdet).φ x g' o) :
    ActsAsTensor Q Z C.M₀ C.φ x
      (((h⁻¹ : GL (Fin 2) C.K) : Matrix (Fin 2) (Fin 2) C.K) * g' *
        (h : Matrix (Fin 2) (Fin 2) C.K)) o := by
  have h1 := ActsAsTensor.change hact h⁻¹ ho ho'
  have hφ : (C.φ.trans (orthTensorEquiv h)).trans (orthTensorEquiv h⁻¹) = C.φ := by
    refine LinearEquiv.ext fun e => ?_
    show orthTensor _ id (orthTensor _ id (C.φ e)) = C.φ e
    rw [orthTensor_id_comp, Units.inv_mul, orthTensor_one_id]
  rw [inv_inv] at h1
  intro y hy
  have := h1 y hy
  simp only [OrthCtx.change] at this
  rw [hφ] at this
  exact this

theorem classConcl_of_change {C : OrthCtx M Q Z B} {x : G} (h : GL (Fin 2) C.K)
    (hdet : (h : Matrix (Fin 2) (Fin 2) C.K).det = 1) (hcl : ClassConcl (C.change h hdet) x) :
    ClassConcl C x := by
  set H : Matrix (Fin 2) (Fin 2) C.K := (h : Matrix (Fin 2) (Fin 2) C.K) with hH
  set Hi : Matrix (Fin 2) (Fin 2) C.K := ((h⁻¹ : GL (Fin 2) C.K) : Matrix (Fin 2) (Fin 2) C.K)
    with hHi
  have hHHi : H * Hi = 1 := by
    rw [hH, hHi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hHiH : Hi * H = 1 := by
    rw [hH, hHi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hdeti : Hi.det = 1 := det_units_inv_eq_one h hdet
  rcases hcl with ⟨g', hg1, hg2, hg3, hact⟩ | ⟨u, w, hu, hw, huw, hli, hact⟩
  · left
    refine ⟨Hi * g' * H, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, Matrix.det_mul, hg1, hdeti, hdet, one_mul, mul_one]
    · intro heq
      apply hg2
      have : g' = H * (Hi * g' * H) * Hi := (mul_conj_cancel_of_mul_eq_one hHHi g').symm
      rw [this, heq, mul_one, hHHi]
    · have e : Hi * g' * H - 1 = Hi * (g' - 1) * H := by
        rw [mul_sub, sub_mul, mul_one, hHiH]
      rw [e]
      calc Hi * (g' - 1) * H * (Hi * (g' - 1) * H)
          = Hi * (g' - 1) * (H * Hi) * (g' - 1) * H := by simp only [mul_assoc]
        _ = Hi * ((g' - 1) * (g' - 1)) * H := by rw [hHHi, mul_one]; simp only [mul_assoc]
        _ = 0 := by rw [hg3, mul_zero, zero_mul]
    · exact actsAsTensor_of_change h hdet (fun a b => rfl) (fun c a => rfl) hact
  · right
    refine ⟨u, w, hu, hw, huw, hli, ?_⟩
    have := actsAsTensor_of_change h hdet (fun a b => map_add (eichler C.qU u w) a b)
      (fun c a => map_smul (eichler C.qU u w) c a) hact
    rwa [mul_one, hHiH] at this

theorem indep_of_not_mem {K ι : Type} [Field K] {u w : ι → K} (hu0 : u ≠ 0)
    (hw : ¬ ∃ c : K, w = c • u) : ∀ s t : K, s • u + t • w = 0 → s = 0 ∧ t = 0 := by
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hu0, rfl⟩
  · exfalso
    apply hw
    refine ⟨-(s / t), ?_⟩
    have h1 : t • w = -(s • u) := eq_neg_of_add_eq_zero_right hst
    calc w = t⁻¹ • (t • w) := (inv_smul_smul₀ ht _).symm
      _ = t⁻¹ • -(s • u) := by rw [h1]
      _ = -(s / t) • u := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

section Situation

variable [Finite G]

theorem exists_root_group (h28 : Smith28OrthStatement) (hc : SmithOrthCfg M Q Z B)
    {X : Subgroup G} {x : G} (hs : Sit M Q Z X x) :
    ∃ g : G, conjSubgroup g Z ≤ Q ∧ conjSubgroup g Z ≤ QB X := by
  obtain ⟨v, hvc, hvQ, hvX⟩ := h28 G M Q Z B hc X x hs
  have hv1 : v ≠ 1 := ne_one_of_isConj_Z hs.ne_one hvc
  have h12 := smith_1_12 hs
  obtain ⟨h₀, hh₀⟩ := hs.conj
  have hz₀ : h₀⁻¹ * x * h₀ ∈ Z := mem_conjSubgroup.mp (hh₀ ▸ hs.mem)
  have hz₀1 : h₀⁻¹ * x * h₀ ≠ 1 := by
    intro e
    apply hs.ne_one
    have e' : x = h₀ * (h₀⁻¹ * x * h₀) * h₀⁻¹ := by group
    rw [e', e]
    group
  have hvZ : v ∉ Z := by
    intro hvZ
    have hm : v ∈ Z ⊓ QB X := ⟨hvZ, hvX⟩
    rw [Z_inf_QB_eq_bot hs h12, Subgroup.mem_bot] at hm
    exact hv1 hm
  have hvcl : InZClass Z v := by
    obtain ⟨c, hc'⟩ := isConj_iff.mp hvc
    exact ⟨c * h₀, h₀⁻¹ * x * h₀, hz₀, hz₀1, by rw [← hc']; group⟩
  obtain ⟨A, hA, hAQX⟩ := exists_root_of_mem_module hc.ctx hs ⟨hvQ, hvX⟩ hvZ hvcl
  obtain ⟨g, rfl⟩ := hA
  exact ⟨g, fun y hy => (hAQX hy).1, fun y hy => (hAQX hy).2⟩

theorem classConcl_std (h52 : Smith52ActStatement) (hc : SmithOrthCfg M Q Z B)
    (C : OrthCtx M Q Z B) {X : Subgroup G} {x : G} (hs : Sit M Q Z X x)
    (hθ : ∀ y ∈ Q, ⁅y, x⁆ ∈ Z → ⁅y, x⁆ = 1) (hxL : x ∈ Lgen M (LB M Q B)) {g : G}
    (hAQ : conjSubgroup g Z ≤ Q) (hAX : conjSubgroup g Z ≤ QB X) {a : G}
    (haA : a ∈ conjSubgroup g Z) (ha1 : a ≠ 1) {u : C.ι → C.K} (hu0 : u ≠ 0) (hqu : C.qU u = 0)
    (hpa : C.φ (C.M₀.π a) = (u, 0)) : ClassConcl C x := by
  have H := hc.ctx.hyp
  have hA : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  obtain ⟨β, w, huw, hact⟩ := normal_form_std h52 hc C hs hxL hA hAQ hAX haA ha1 hu0 hqu hpa
  have hβq := beta_mul_q_eq_zero hθ hc C hs hu0 hqu huw hact
  by_cases hwu : ∃ c : C.K, w = c • u
  ·
    obtain ⟨c, rfl⟩ := hwu
    have hE : eichler C.qU u (c • u) = 1 := eichler_smul_self_eq_one C.qU hqu c
    by_cases hβ : β = 0
    · exfalso
      subst hβ
      exact not_shape_zero hc C hs hqu c hact
    · left
      refine ⟨!![1, β; 0, 1], by simp [Matrix.det_fin_two_of], ?_, ?_, ?_⟩
      · intro h
        exact hβ (by simpa using congrFun (congrFun h 0) 1)
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
      · rw [hE] at hact
        exact hact
  ·
    have hind := indep_of_not_mem hu0 hwu
    have hq4 : 4 ≤ Nat.card C.K := by rw [C.hD.card]; exact H.q4
    have hn4 : 4 ≤ Fintype.card C.ι := four_le_card_of_cfg hc C
    have hnd := C.hF.nondeg
    have hImg := imgSet_eq_Ish h52 hc C hs hθ hA hAQ hAX haA ha1 hu0 hqu hpa huw hact
    have hAF := aframe_count h52 hc C hs hAQ hAX
    rw [hImg] at hAF
    have _hKu := nSing_perp_one hnd hu0 hqu (by omega)
    have hN := nSing_numeric hnd hq4 hn4
    have _hb : 0 < (Nat.card C.K - 1) * Nat.card C.K ^ (Fintype.card C.ι - 3) :=
      Nat.mul_pos (by omega) (pow_pos (by omega) _)
    by_cases hβ : β = 0
    · subst hβ
      by_cases hqw : C.qU w = 0
      · right
        refine ⟨u, w, hqu, hqw, huw, LinearIndependent.pair_iff.mpr hind, ?_⟩
        rwa [Matrix.one_fin_two.symm] at hact
      · exfalso
        have _hT := tCount_Ish_zero (qU := C.qU) hu0 hqu huw
        have _hK := nSing_perp_two_nonsing hnd hu0 hqu huw hqw (by omega)
        rcases hAF with ⟨uz, huz0, hquz, _hIV⟩ | ⟨uz, ux, huz0, hquz, hqux, hzx, hind', _hIII⟩
        · have _hKz := nSing_perp_one hnd huz0 hquz (by omega)
          exact hN.1 (by omega)
        · have _hKz := nSing_perp_one hnd huz0 hquz (by omega)
          have _hK2 := nSing_perp_two hnd huz0 hquz hqux hzx hind' (by omega)
          apply hN.2
          rw [mul_add]
          omega
    · exfalso
      have hqw : C.qU w = 0 := (mul_eq_zero.mp hβq).resolve_left hβ
      have _hT := tCount_Ish_ne (qU := C.qU) hu0 hqu huw hβ
      have _hK2 := nSing_perp_two hnd hu0 hqu hqw huw hind (by omega)
      rcases hAF with ⟨uz, huz0, hquz, _hIV⟩ | ⟨uz, ux, huz0, hquz, hqux, hzx, hind', _hIII⟩
      · have _hKz := nSing_perp_one hnd huz0 hquz (by omega)
        omega
      · have _hKz := nSing_perp_one hnd huz0 hquz (by omega)
        have _hK2' := nSing_perp_two hnd huz0 hquz hqux hzx hind' (by omega)
        have _hqq : Nat.card C.K ^ 2 = Nat.card C.K * Nat.card C.K := sq _
        nlinarith

end Situation

end CFSG.RankThree.GF2n.Smith81.OrthClass

namespace CFSG.RankThree.GF2n.Smith81

open QuadraticMap CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement Matrix
open OrthClass


theorem orthClass_of (h25 : Smith25OrthStatement) (h52 : Smith52ActStatement)
    (h28 : Smith28OrthStatement) (h4 : Orth212C4CondStatement) : OrthClassStatement := by
  intro G _ _ M Q Z B hc C X x hs
  have H := hc.ctx.hyp
  obtain ⟨g, hAQ, hAX⟩ := exists_root_group h28 hc hs
  have hA : IsZConjugate Z (conjSubgroup g Z) := ⟨g, rfl⟩
  obtain ⟨hAZ, -, hXLB⟩ := lin29_of_sit hs hA hAQ hAX
  have hcA : Ctx M Q Z (conjSubgroup g Z) := ⟨H, hA, hAQ, hAZ⟩
  have hxL : x ∈ Lgen M (LB M Q B) := LB_le_Lgen_of_25 h25 hc hcA (hXLB hs.mem)
  have hθ := theta_zero_of h4 h28 hc hs
  obtain ⟨z, hz, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    have hZne : Z ≠ ⊥ := by
      intro h
      have h4' := H.q4
      rw [h, Subgroup.card_bot] at h4'
      omega
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
    exact ⟨z, z.2, fun h => hz1 (Subtype.ext h)⟩
  have haA : g * z * g⁻¹ ∈ conjSubgroup g Z := by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rw [e]
    exact hz
  have ha1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    have : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [this, h]
    group
  have haZ : g * z * g⁻¹ ∉ Z := by
    intro h
    have hm : g * z * g⁻¹ ∈ Z ⊓ conjSubgroup g Z := ⟨h, haA⟩
    rw [inf_conjSubgroup_eq_bot_of_isTI H.ti hAZ, Subgroup.mem_bot] at hm
    exact ha1 hm
  have hac : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨c₁, c₂, u, hc12, hu0, hqu, hφa⟩ := (C.hF.root z hz hz1 _ (hAQ haA) haZ).mp hac
  have hcne : (![c₁, c₂] : Fin 2 → C.K) ≠ 0 := by
    intro h
    rcases hc12 with h1 | h2
    · exact h1 (by simpa using congrFun h 0)
    · exact h2 (by simpa using congrFun h 1)
  obtain ⟨h, hdet, hh⟩ := exists_change_pure (![c₁, c₂]) hcne u
  have hpa : (C.change h hdet).φ (C.M₀.π (g * z * g⁻¹)) = (u, 0) := by
    show (C.φ.trans (orthTensorEquiv h)) (C.M₀.π (g * z * g⁻¹)) = (u, 0)
    rw [LinearEquiv.trans_apply, hφa, orthTensorEquiv_apply]
    simpa using hh
  have key : ClassConcl (C.change h hdet) x :=
    classConcl_std h52 hc (C.change h hdet) hs hθ hxL hAQ hAX haA ha1 hu0 hqu hpa
  exact classConcl_of_change h hdet key

end CFSG.RankThree.GF2n.Smith81
