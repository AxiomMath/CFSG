module

public import CFSG.Quasithin.MS93.S5ACoc
public import CFSG.Quasithin.MS93.S5AGeo

public noncomputable section

namespace CFSG.Quasithin.MS93.S5

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.JonesParshall MSP
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

@[expose] def cform (B : F) (m : V4 F) (g : Sp4 F) : V4 F := B • sqf (mat g) + (mat g *ᵥ m - m)

omit [Fintype F] [CharP F 2] in
theorem mat_tau {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    mat (tau hC) = fromBlocks 1 C 0 1 := coe_tau hC

theorem cform_tau_inl0 (B : F) (m : V4 F) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    cform B m (tau hC) (.inl 0) =
      B * sqrtF (C 0 0) + (C 0 0 * m (.inr 0) + C 0 1 * m (.inr 1)) := by
  simp only [cform, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sqf, quadQ, mat_tau]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem cform_tau_inl1 (B : F) (m : V4 F) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) :
    cform B m (tau hC) (.inl 1) =
      B * sqrtF (C 1 1) + (C 1 0 * m (.inr 0) + C 1 1 * m (.inr 1)) := by
  simp only [cform, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sqf, quadQ, mat_tau]
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem cform_tau_inr (B : F) (m : V4 F) {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (j : Fin 2) : cform B m (tau hC) (.inr j) = 0 := by
  simp only [cform, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sqf, quadQ, mat_tau]
  fin_cases j <;> simp [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, sqrtF_zero]

theorem cform_tau_eq_zero {B : F} {m : V4 F} {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C)
    (h0 : B * sqrtF (C 0 0) + (C 0 0 * m (.inr 0) + C 0 1 * m (.inr 1)) = 0)
    (h1 : B * sqrtF (C 1 1) + (C 1 0 * m (.inr 0) + C 1 1 * m (.inr 1)) = 0) :
    cform B m (tau hC) = 0 := by
  funext i
  rcases i with i | i <;> fin_cases i
  · exact (cform_tau_inl0 B m hC).trans h0
  · exact (cform_tau_inl1 B m hC).trans h1
  · exact cform_tau_inr B m hC 0
  · exact cform_tau_inr B m hC 1

omit [Fintype F] [CharP F 2] in
theorem tau_mem_Q₂ {a b : F} : tau (sym2_transpose a b 0) ∈ Q₂ F := by
  rw [mem_Q₂_iff]
  refine ⟨tau_mem_unipotent _, ?_⟩
  rw [mat_tau]
  rfl

theorem eq_zero_of_cform_Q₂ {B : F} {m : V4 F} (h : ∀ g ∈ Q₂ F, cform B m g = 0) : B = 0 := by
  have h1 := congrFun (h _ (tau_mem_Q₂ (a := 0) (b := 1))) (.inl 1)
  rw [cform_tau_inl1] at h1
  simp only [sym2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, sqrtF_zero, mul_zero, one_mul, zero_mul,
    add_zero, zero_add, Pi.zero_apply] at h1
  have h2 := congrFun (h _ (tau_mem_Q₂ (a := 1) (b := 0))) (.inl 0)
  rw [cform_tau_inl0] at h2
  simp only [sym2, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one, sqrtF_one, mul_one, one_mul, zero_mul,
    add_zero, Pi.zero_apply, h1] at h2
  exact h2

theorem sqrt_mul_eq_of_ne_zero {B w x : F} (hx : x ≠ 0)
    (h : B * sqrtF x + x * w = 0) : sqrtF x * w = B := by
  have hs : sqrtF x ≠ 0 := fun h0 => hx (by rw [← sqrtF_sq x, h0]; ring)
  have e : sqrtF x * (B + sqrtF x * w) = 0 := by
    have e0 : sqrtF x * (B + sqrtF x * w) = B * sqrtF x + sqrtF x ^ 2 * w := by ring
    rw [sqrtF_sq] at e0
    exact e0.trans h
  have e2 := (mul_eq_zero.1 e).resolve_left hs
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination e2 - B * h2

theorem eq_or_eq_of_three {B w c d₁ d₂ d₃ : F} (hB : B ≠ 0) (h₁ : B * sqrtF d₁ + d₁ * w = c)
    (h₂ : B * sqrtF d₂ + d₂ * w = c) (h₃ : B * sqrtF d₃ + d₃ * w = c) :
    d₁ = d₂ ∨ d₁ = d₃ ∨ d₂ = d₃ := by
  by_contra hne
  push Not at hne
  obtain ⟨n12, n13, n23⟩ := hne
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hx : d₁ + d₂ ≠ 0 := fun h0 => n12 (by linear_combination h0 - d₂ * h2)
  have hy : d₁ + d₃ ≠ 0 := fun h0 => n13 (by linear_combination h0 - d₃ * h2)
  have ex : B * sqrtF (d₁ + d₂) + (d₁ + d₂) * w = 0 := by
    rw [sqrtF_add]
    linear_combination h₁ + h₂ + c * h2
  have ey : B * sqrtF (d₁ + d₃) + (d₁ + d₃) * w = 0 := by
    rw [sqrtF_add]
    linear_combination h₁ + h₃ + c * h2
  have hx' := sqrt_mul_eq_of_ne_zero hx ex
  have hy' := sqrt_mul_eq_of_ne_zero hy ey
  have hw : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hx'
    exact hB hx'.symm
  have hxy : sqrtF (d₁ + d₂) = sqrtF (d₁ + d₃) :=
    mul_right_cancel₀ hw (hx'.trans hy'.symm)
  have hsq := congrArg (· ^ 2) hxy
  simp only [sqrtF_sq] at hsq
  exact n23 (by linear_combination hsq)

open Classical in
@[expose] def sigmaF (B w₁ w₂ : F) : Finset (F × F × F) :=
  Finset.univ.filter fun t => B * sqrtF t.1 + (t.1 * w₁ + t.2.1 * w₂) = 0 ∧
    B * sqrtF t.2.2 + (t.2.1 * w₁ + t.2.2 * w₂) = 0

theorem mem_sigmaF {B w₁ w₂ : F} {t : F × F × F} :
    t ∈ sigmaF B w₁ w₂ ↔ B * sqrtF t.1 + (t.1 * w₁ + t.2.1 * w₂) = 0 ∧
      B * sqrtF t.2.2 + (t.2.1 * w₁ + t.2.2 * w₂) = 0 := by
  simp [sigmaF]

theorem eq_zero_of_sqrtF {B x : F} (hB : B ≠ 0) (h : B * sqrtF x = 0) : x = 0 := by
  have h1 := (mul_eq_zero.1 h).resolve_left hB
  rw [← sqrtF_sq x, h1]
  ring

theorem card_sigmaF_zero {B : F} (hB : B ≠ 0) : (sigmaF B 0 0).card ≤ Fintype.card F := by
  classical
  have hinj : Set.InjOn (fun t : F × F × F => t.2.1) (sigmaF B 0 0 : Set (F × F × F)) := by
    intro t ht t' ht' htt
    have h := mem_sigmaF.1 ht
    have h' := mem_sigmaF.1 ht'
    simp only [mul_zero, add_zero] at h h'
    obtain ⟨a, b, d⟩ := t
    obtain ⟨a', b', d'⟩ := t'
    simp only at h h' htt
    rw [eq_zero_of_sqrtF hB h.1, eq_zero_of_sqrtF hB h.2, eq_zero_of_sqrtF hB h'.1,
      eq_zero_of_sqrtF hB h'.2, htt]
  calc (sigmaF B 0 0).card = ((sigmaF B 0 0).image fun t => t.2.1).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card F := Finset.card_le_univ _

omit [Field F] [Fintype F] [CharP F 2] in
theorem prod3_ext {t t' : F × F × F} (h1 : t.1 = t'.1) (h2 : t.2.1 = t'.2.1)
    (h3 : t.2.2 = t'.2.2) : t = t' :=
  Prod.ext h1 (Prod.ext h2 h3)

theorem card_sigmaF_le {B : F} (hB : B ≠ 0) (w₁ w₂ : F) :
    (sigmaF B w₁ w₂).card ≤ 2 * Fintype.card F := by
  classical
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_cases hw₂ : w₂ = 0
  · subst hw₂
    by_cases hw₁ : w₁ = 0
    · subst hw₁
      exact (card_sigmaF_zero hB).trans (Nat.le_mul_of_pos_left _ two_pos)
    ·
      refine (Finset.card_le_mul_card_image (sigmaF B w₁ 0) (f := fun t => t.2.2) 2
        fun d _ => ?_).trans (Nat.mul_le_mul_left _ (Finset.card_le_univ _))
      by_contra hlt
      push Not at hlt
      obtain ⟨t, t', t'', ht, ht', ht'', n1, n2, n3⟩ := Finset.two_lt_card_iff.1 hlt
      simp only [Finset.mem_filter, mem_sigmaF, mul_zero, add_zero] at ht ht' ht''
      obtain ⟨⟨e1, e2⟩, hd⟩ := ht
      obtain ⟨⟨e1', e2'⟩, hd'⟩ := ht'
      obtain ⟨⟨e1'', e2''⟩, hd''⟩ := ht''
      have hb' : t'.2.1 = t.2.1 := mul_right_cancel₀ hw₁ (by
        rw [hd'] at e2'
        rw [hd] at e2
        linear_combination e2' - e2)
      have hb'' : t''.2.1 = t.2.1 := mul_right_cancel₀ hw₁ (by
        rw [hd''] at e2''
        rw [hd] at e2
        linear_combination e2'' - e2)
      rcases eq_or_eq_of_three (c := 0) (w := w₁) hB e1 e1' e1'' with h | h | h
      · exact n1 (prod3_ext h hb'.symm (hd.trans hd'.symm))
      · exact n2 (prod3_ext h hb''.symm (hd.trans hd''.symm))
      · exact n3 (prod3_ext h (hb'.trans hb''.symm) (hd'.trans hd''.symm))
  ·
    refine (Finset.card_le_mul_card_image (sigmaF B w₁ w₂) (f := fun t => t.1) 2
      fun a₀ _ => ?_).trans (Nat.mul_le_mul_left _ (Finset.card_le_univ _))
    by_contra hlt
    push Not at hlt
    obtain ⟨t, t', t'', ht, ht', ht'', n1, n2, n3⟩ := Finset.two_lt_card_iff.1 hlt
    simp only [Finset.mem_filter, mem_sigmaF] at ht ht' ht''
    obtain ⟨⟨e1, e2⟩, ha⟩ := ht
    obtain ⟨⟨e1', e2'⟩, ha'⟩ := ht'
    obtain ⟨⟨e1'', e2''⟩, ha''⟩ := ht''
    have hb' : t'.2.1 = t.2.1 := mul_right_cancel₀ hw₂ (by
      rw [ha'] at e1'
      rw [ha] at e1
      linear_combination e1' - e1)
    have hb'' : t''.2.1 = t.2.1 := mul_right_cancel₀ hw₂ (by
      rw [ha''] at e1''
      rw [ha] at e1
      linear_combination e1'' - e1)
    have f1 : B * sqrtF t.2.2 + t.2.2 * w₂ = t.2.1 * w₁ := by
      linear_combination e2 - t.2.1 * w₁ * h2
    have f2 : B * sqrtF t'.2.2 + t'.2.2 * w₂ = t.2.1 * w₁ := by
      rw [← hb']
      linear_combination e2' - t'.2.1 * w₁ * h2
    have f3 : B * sqrtF t''.2.2 + t''.2.2 * w₂ = t.2.1 * w₁ := by
      rw [← hb'']
      linear_combination e2'' - t''.2.1 * w₁ * h2
    rcases eq_or_eq_of_three hB f1 f2 f3 with h | h | h
    · exact n1 (prod3_ext (ha.trans ha'.symm) hb'.symm h)
    · exact n2 (prod3_ext (ha.trans ha''.symm) hb''.symm h)
    · exact n3 (prod3_ext (ha'.trans ha''.symm) (hb'.trans hb''.symm) h)

@[expose] def q1Coord (g : Sp4 F) : F × F × F :=
  (mat g (.inl 0) (.inr 0), mat g (.inl 0) (.inr 1), mat g (.inl 1) (.inr 1))

omit [Fintype F] [CharP F 2] in
theorem exists_tau_of_mem_Q₁ {g : Sp4 F} (hg : g ∈ Q₁ F) :
    ∃ (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C), g = tau hC := by
  rw [Q₁_eq_radical] at hg
  exact hg

omit [Fintype F] [CharP F 2] in
theorem q1Coord_injOn : Set.InjOn (q1Coord (F := F)) (Q₁ F : Set (Sp4 F)) := by
  intro g hg g' hg' h
  obtain ⟨C, hC, rfl⟩ := exists_tau_of_mem_Q₁ hg
  obtain ⟨C', hC', rfl⟩ := exists_tau_of_mem_Q₁ hg'
  simp only [q1Coord, mat_tau, Prod.mk.injEq] at h
  simp only [fromBlocks_apply₁₂] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hCC : C = C' := by
    rw [eq_sym2 hC, eq_sym2 hC', h1, h2, h3]
  subst hCC
  rfl

theorem q1Coord_mem_sigmaF {B : F} {m : V4 F} {g : Sp4 F} (hg : g ∈ Q₁ F)
    (h : cform B m g = 0) : q1Coord g ∈ sigmaF B (m (.inr 0)) (m (.inr 1)) := by
  obtain ⟨C, hC, rfl⟩ := exists_tau_of_mem_Q₁ hg
  have h0 := congrFun h (.inl 0)
  have h1 := congrFun h (.inl 1)
  rw [cform_tau_inl0] at h0
  rw [cform_tau_inl1] at h1
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    simpa using this
  rw [h10] at h1
  rw [mem_sigmaF]
  simp only [q1Coord, mat_tau, fromBlocks_apply₁₂]
  exact ⟨h0, h1⟩

theorem card_toFinset_le_sigmaF {B : F} {m : V4 F} {S : Set (Sp4 F)} [Fintype S]
    (hS : S ⊆ Q₁ F) (h : ∀ g ∈ S, cform B m g = 0) :
    S.toFinset.card ≤ (sigmaF B (m (.inr 0)) (m (.inr 1))).card := by
  classical
  refine Finset.card_le_card_of_injOn q1Coord (fun g hg => ?_) (fun g hg g' hg' hgg => ?_)
  · have hg' : g ∈ S := Set.mem_toFinset.1 (Finset.mem_coe.1 hg)
    exact Finset.mem_coe.2 (q1Coord_mem_sigmaF (hS hg') (h g hg'))
  · exact q1Coord_injOn (hS (Set.mem_toFinset.1 (Finset.mem_coe.1 hg)))
      (hS (Set.mem_toFinset.1 (Finset.mem_coe.1 hg'))) hgg

theorem card_le_of_cform_Q₁ {B : F} (hB : B ≠ 0) {m : V4 F} {S : Set (Sp4 F)}
    (hS : S ⊆ Q₁ F) (h : ∀ g ∈ S, cform B m g = 0) : Nat.card S ≤ 2 * Nat.card F := by
  classical
  rw [Nat.card_eq_card_toFinset, Nat.card_eq_fintype_card (α := F)]
  exact (card_toFinset_le_sigmaF hS h).trans (card_sigmaF_le hB _ _)

theorem card_le_of_cform_Q₁_zero {B : F} (hB : B ≠ 0) {m : V4 F} (hm0 : m (.inr 0) = 0)
    (hm1 : m (.inr 1) = 0) {S : Set (Sp4 F)} (hS : S ⊆ Q₁ F) (h : ∀ g ∈ S, cform B m g = 0) :
    Nat.card S ≤ Nat.card F := by
  classical
  rw [Nat.card_eq_card_toFinset, Nat.card_eq_fintype_card (α := F)]
  have h1 := card_toFinset_le_sigmaF hS h
  rw [hm0, hm1] at h1
  exact h1.trans (card_sigmaF_zero hB)

omit [Fintype F] [CharP F 2] in
theorem transv_eq_tau (x : V4 F) (hx : x ∈ ln₀ F) :
    transv x 1 = tau (sym2_transpose (x (.inl 0) * x (.inl 0)) (x (.inl 0) * x (.inl 1))
      (x (.inl 1) * x (.inl 1))) := by
  obtain ⟨h0, h1⟩ := mem_ln₀.1 hx
  refine ext_mulVec fun v => ?_
  rw [transv_mulVec, mat_tau]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [form_apply, h0, h1, mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, sym2] <;>
    ring

omit [Fintype F] [CharP F 2] in
theorem transv_mem_Q₁ {x : V4 F} (hx : x ∈ ln₀ F) : transv x 1 ∈ Q₁ F :=
  xPoint_le_qLine isLine_ln₀ ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
    (transv_mem_xPoint x 1)

theorem eq_xPoint_sup_of_cform (hF : Fintype.card F = 2) {B : F} (hB : B ≠ 0) {m : V4 F}
    {J : Subgroup (Sp4 F)} (hJ : J ≤ Q₁ F) (h : ∀ g ∈ J, cform B m g = 0)
    (hcard : 4 ≤ Nat.card J) :
    ∃ x y : V4 F, x ≠ 0 ∧ y ≠ 0 ∧ x ∈ ln₀ F ∧ y ∈ ln₀ F ∧ (F ∙ x) ≠ (F ∙ y) ∧
      J = xPoint (F ∙ x) ⊔ xPoint (F ∙ y) := by
  classical
  have hNF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  have h01 : ∀ c : F, c = 0 ∨ c = 1 := by
    intro c
    by_contra hc
    push Not at hc
    have hs : ({0, 1, c} : Finset F).card ≤ 2 := hF ▸ Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hc.1.symm]),
      Finset.card_insert_of_notMem (by simp [hc.2.symm]), Finset.card_singleton] at hs
    omega
  have hB1 : B = 1 := (h01 B).resolve_left hB
  have hsq : ∀ c : F, sqrtF c = c := fun c => by
    rcases h01 c with rfl | rfl
    · exact sqrtF_zero
    · exact sqrtF_one
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  set T : Set (Sp4 F) := {g | g ∈ Q₁ F ∧ cform B m g = 0} with hTdef
  have hJT : (J : Set (Sp4 F)) ⊆ T := fun g hg => ⟨hJ hg, h g hg⟩
  have hT4 : Nat.card T ≤ 4 := by
    have := card_le_of_cform_Q₁ hB (S := T) (fun g hg => hg.1) (fun g hg => hg.2)
    rw [hNF] at this
    simpa using this
  have hJcard : Nat.card (J : Set (Sp4 F)) = Nat.card J := rfl
  have hJeq : (J : Set (Sp4 F)) = T := by
    refine Set.eq_of_subset_of_ncard_le hJT ?_ (Set.toFinite T)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hJcard]
    omega
  have hmemT : ∀ g, g ∈ T → g ∈ J := fun g hg => by
    have : g ∈ (J : Set (Sp4 F)) := hJeq ▸ hg
    exact this
  have hX : ∀ x : V4 F, x ≠ 0 → x ∈ ln₀ F → cform B m (transv x 1) = 0 →
      xPoint (F ∙ x) ≤ J := by
    intro x hx0 hx hc g hg
    obtain ⟨c, rfl⟩ := (mem_xPoint_span hx0).1 hg
    rcases h01 c with rfl | rfl
    · rw [transv_zero]
      exact J.one_mem
    · exact hmemT _ ⟨transv_mem_Q₁ hx, hc⟩
  have hfin : ∀ x y : V4 F, x ≠ 0 → y ≠ 0 → x ∈ ln₀ F → y ∈ ln₀ F → (F ∙ x) ≠ (F ∙ y) →
      cform B m (transv x 1) = 0 → cform B m (transv y 1) = 0 →
      ∃ x y : V4 F, x ≠ 0 ∧ y ≠ 0 ∧ x ∈ ln₀ F ∧ y ∈ ln₀ F ∧ (F ∙ x) ≠ (F ∙ y) ∧
        J = xPoint (F ∙ x) ⊔ xPoint (F ∙ y) := by
    intro x y hx0 hy0 hx hy hxy hcx hcy
    refine ⟨x, y, hx0, hy0, hx, hy, hxy, ?_⟩
    have hle : xPoint (F ∙ x) ⊔ xPoint (F ∙ y) ≤ J := sup_le (hX x hx0 hx hcx) (hX y hy0 hy hcy)
    have hperp : (F ∙ y) ≤ perp (F ∙ x) := by
      rw [Submodule.span_singleton_le_iff_mem, mem_perp_span]
      obtain ⟨a0, a1⟩ := mem_ln₀.1 hx
      obtain ⟨b0, b1⟩ := mem_ln₀.1 hy
      rw [form_apply, a0, a1, b0, b1]
      ring
    have hc4 := card_xPoint_sup (isPoint_span hx0) (isPoint_span hy0) hxy hperp
    rw [hNF] at hc4
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have : Nat.card J ≤ 4 := by
      rw [← hJcard]
      have e : Nat.card (J : Set (Sp4 F)) = Nat.card T := by rw [hJeq]
      omega
    omega
  have he1 : e₁ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩
  have he2 : e₂ F ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩
  have he12 : e₁ F + e₂ F ∈ ln₀ F := (ln₀ F).add_mem he1 he2
  have he12' : e₁ F + e₂ F ≠ 0 := fun h0 => by simpa using congrFun h0 (.inl 0)
  have hne : ∀ x y : V4 F, x ∈ ln₀ F → (∃ i, x i = 0 ∧ y i ≠ 0) → x ≠ 0 → (F ∙ x) ≠ (F ∙ y) := by
    intro x y _ ⟨i, hxi, hyi⟩ _ hxy
    have hy : y ∈ F ∙ x := hxy ▸ Submodule.mem_span_singleton_self y
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    simp [hxi] at hyi
  have hne' : ∀ x y : V4 F, (∃ i, x i ≠ 0 ∧ y i = 0) → y ≠ 0 → (F ∙ x) ≠ (F ∙ y) := by
    intro x y ⟨i, hxi, hyi⟩ _ hxy
    have hx : x ∈ F ∙ y := hxy.symm ▸ Submodule.mem_span_singleton_self x
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    simp [hyi] at hxi
  have hval : ∀ x : V4 F, x ∈ ln₀ F →
      (B * sqrtF (x (.inl 0) * x (.inl 0)) + (x (.inl 0) * x (.inl 0) * m (.inr 0) +
        x (.inl 0) * x (.inl 1) * m (.inr 1)) = 0) →
      (B * sqrtF (x (.inl 1) * x (.inl 1)) + (x (.inl 0) * x (.inl 1) * m (.inr 0) +
        x (.inl 1) * x (.inl 1) * m (.inr 1)) = 0) → cform B m (transv x 1) = 0 := by
    intro x hx h0 h1
    rw [transv_eq_tau x hx]
    exact cform_tau_eq_zero _ (by simpa [sym2] using h0) (by simpa [sym2] using h1)
  rcases h01 (m (.inr 0)) with hw1 | hw1 <;> rcases h01 (m (.inr 1)) with hw2 | hw2
  · exfalso
    have := card_le_of_cform_Q₁_zero hB hw1 hw2 (S := T) (fun g hg => hg.1) (fun g hg => hg.2)
    rw [hNF] at this
    have e : Nat.card (J : Set (Sp4 F)) = Nat.card T := by rw [hJeq]
    omega
  ·
    refine hfin (e₂ F) (e₁ F + e₂ F) e₂_ne_zero he12' he2 he12
      (hne _ _ he2 ⟨.inl 0, by simp, by simp⟩ e₂_ne_zero) ?_ ?_
    · exact hval _ he2 (by simp [hB1, hw1, hw2, sqrtF_zero])
        (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
    · exact hval _ he12 (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
        (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
  ·
    refine hfin (e₁ F) (e₁ F + e₂ F) e₁_ne_zero he12' he1 he12
      (hne _ _ he1 ⟨.inl 1, by simp, by simp⟩ e₁_ne_zero) ?_ ?_
    · exact hval _ he1 (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
        (by simp [hw1, hw2, sqrtF_zero])
    · exact hval _ he12 (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
        (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
  ·
    refine hfin (e₁ F) (e₂ F) e₁_ne_zero e₂_ne_zero he1 he2
      (hne _ _ he1 ⟨.inl 1, by simp, by simp⟩ e₁_ne_zero) ?_ ?_
    · exact hval _ he1 (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)
        (by simp [hw1, hw2, sqrtF_zero])
    · exact hval _ he2 (by simp [hw1, hw2, sqrtF_zero])
        (by simp [hB1, hw1, hw2, hsq]; linear_combination h2)

end CFSG.Quasithin.MS93.S5
