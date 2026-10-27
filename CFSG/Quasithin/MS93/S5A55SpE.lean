module

public import CFSG.Quasithin.MS93.MSPRankOne
public import CFSG.Quasithin.MS93.S59Gen
public import CFSG.Quasithin.MS93.S5A56Sp

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F]

abbrev mu₀ (F : Type) [Field F] : Submodule F (V4 F) := Submodule.span F {e₁ F, f₂ F}

theorem mem_mu₀ {v : V4 F} : v ∈ mu₀ F ↔ v (.inl 1) = 0 ∧ v (.inr 0) = 0 := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    simp
  · rintro ⟨h0, h1⟩
    refine ⟨v (.inl 0), v (.inr 1), ext4 ?_ ?_ ?_ ?_⟩ <;> simp [h0, h1]

theorem e₁_mem_mu₀ : e₁ F ∈ mu₀ F := Submodule.subset_span (by simp)

theorem f₂_mem_mu₀ : f₂ F ∈ mu₀ F := Submodule.subset_span (by simp)

theorem isLine_mu₀ : IsLine (mu₀ F) := by
  refine ⟨?_, fun x hx y hy => ?_⟩
  · have hw : f₂ F ∉ F ∙ e₁ F := by
      rw [Submodule.mem_span_singleton]
      rintro ⟨a, ha⟩
      have := congrFun ha (.inr 1)
      simp at this
    exact finrank_span_pair e₁_ne_zero hw
  · rw [form_apply, (mem_mu₀.1 hx).1, (mem_mu₀.1 hx).2, (mem_mu₀.1 hy).1, (mem_mu₀.1 hy).2]
    ring

theorem pt₀_le_mu₀ : pt₀ F ≤ mu₀ F := by
  rw [pt₀_eq_span, Submodule.span_singleton_le_iff_mem]
  exact e₁_mem_mu₀

theorem sub_mem_mu₀ {n : Sp4 F} (hn : n ∈ qLine (mu₀ F)) (v : V4 F) :
    mat n *ᵥ v - v ∈ mu₀ F := by
  have := sub_mem_perp_of_mem_fixer hn v
  rwa [isLine_mu₀.perp_eq] at this

theorem levMat_of_mem_qLine_mu₀ {n : Sp4 F} (hn : n ∈ qLine (mu₀ F)) :
    levMat n = !![1, 0; mat n (.inr 1) (.inl 1), 1] := by
  have hf : mat n *ᵥ f₂ F = f₂ F := hn _ f₂_mem_mu₀
  have he := (mem_mu₀.1 (sub_mem_mu₀ hn (e₂ F))).1
  have h11 : mat n (.inl 1) (.inl 1) = 1 := by
    rw [mat_apply_eq]
    simp only [Pi.sub_apply] at he
    have : (e₂ F) (.inl 1) = 1 := by simp
    rw [← sub_eq_zero.1 he] at this
    exact this
  have h12 : mat n (.inl 1) (.inr 1) = 0 := by rw [mat_apply_eq, hf]; simp
  have h22 : mat n (.inr 1) (.inr 1) = 1 := by rw [mat_apply_eq, hf]; simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levMat, h11, h12, h22]

theorem mem_Q₂_of_mem_qLine_mu₀ {n : Sp4 F} (hn : n ∈ qLine (mu₀ F))
    (hc : mat n (.inr 1) (.inl 1) = 0) : n ∈ Q₂ F := by
  have he : mat n *ᵥ e₁ F = e₁ F := hn _ e₁_mem_mu₀
  have hP : n ∈ P₂ F := mem_stab_of_le fun v hv => by
    rw [pt₀_eq_span] at hv ⊢
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [mulVec_smul, he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine mem_Q₂_iff_levQ.2 ⟨hP, he, Subtype.ext ?_⟩
  rw [coe_levQ, levMat_of_mem_qLine_mu₀ hn, hc, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

section Std

variable [CharP F 2]

omit [CharP F 2] in
theorem form_mulVec_ne_zero_of_mem_ln₀ {n : Sp4 F} (hn : n ∈ qLine (mu₀ F)) (hnQ : n ∉ Q₂ F)
    {u : V4 F} (hu : u ∈ ln₀ F) (hu1 : u ∉ F ∙ e₁ F) : form F u (mat n *ᵥ u) ≠ 0 := by
  have hc : mat n (.inr 1) (.inl 1) ≠ 0 := fun h0 => hnQ (mem_Q₂_of_mem_qLine_mu₀ hn h0)
  obtain ⟨h2, h3⟩ := mem_ln₀.1 hu
  have hu1' : u (.inl 1) ≠ 0 := by
    intro h1
    refine hu1 (Submodule.mem_span_singleton.2 ⟨u (.inl 0), ext4 ?_ ?_ ?_ ?_⟩) <;> simp [h1, h2, h3]
  have he : mat n *ᵥ e₁ F = e₁ F := hn _ e₁_mem_mu₀
  have h10 : mat n (.inr 1) (.inl 0) = 0 := by rw [mat_apply_eq, he]; simp
  obtain ⟨d1, d2⟩ := mem_mu₀.1 (sub_mem_mu₀ hn u)
  simp only [Pi.sub_apply] at d1 d2
  have h4 : (mat n *ᵥ u) (.inr 1) = mat n (.inr 1) (.inl 1) * u (.inl 1) := by
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h3, h10]
    ring
  rw [form_apply, h4, sub_eq_zero.1 d2, h2, h3]
  simp only [mul_zero, zero_mul, add_zero, sub_zero, zero_add]
  exact mul_ne_zero hu1' (mul_ne_zero hc hu1')

omit [CharP F 2] in
theorem form_mulVec_ne_zero_of_mem_mu₀ {y : Sp4 F} (hy : y ∈ Q₁ F)
    (hy1 : mat y (.inl 1) (.inr 1) = 1) {u : V4 F} (hu : u ∈ mu₀ F) (hu1 : u ∉ F ∙ e₁ F) :
    form F u (mat y *ᵥ u) ≠ 0 := by
  obtain ⟨h1, h2⟩ := mem_mu₀.1 hu
  have hu3 : u (.inr 1) ≠ 0 := by
    intro h3
    refine hu1 (Submodule.mem_span_singleton.2 ⟨u (.inl 0), ext4 ?_ ?_ ?_ ?_⟩) <;> simp [h1, h2, h3]
  rw [mulVec_of_mem_Q₁ hy, hy1, form_apply]
  simp [h1, h2]
  exact hu3

theorem Q₂_le_of_two (hq : Nat.card F = 2) {H : Subgroup (Sp4 F)}
    (hconjE : ∀ x y s, qe x y s ∈ H → qe (x + y) y s ∈ H)
    (hconjt : ∀ x y s, qe x y s ∈ H → qe x (y + x) s ∈ H) (h₀ : qe 1 0 0 ∈ H) :
    Q₂ F ≤ H := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h01 := eq_zero_or_eq_one_of_card_two hq
  have hmul : ∀ x y s x' y' s', qe x y s ∈ H → qe x' y' s' ∈ H →
      qe (x + x') (y + y') (s + s' + x * y' + x' * y) ∈ H := fun x y s x' y' s' h h' => by
    rw [← qe_mul]
    exact mul_mem h h'
  have h110 : qe 1 1 0 ∈ H := by
    have := hconjt 1 0 0 h₀
    rwa [zero_add] at this
  have h010 : qe 0 1 0 ∈ H := by
    have := hconjE 1 1 0 h110
    rwa [show (1 : F) + 1 = 0 by linear_combination h2] at this
  have h111 : qe 1 1 1 ∈ H := by
    have := hmul _ _ _ _ _ _ h₀ h010
    convert this using 1
    exact qe_congr (by ring) (by ring) (by ring)
  have h001 : qe 0 0 1 ∈ H := by
    have := hmul _ _ _ _ _ _ h111 h110
    convert this using 1
    exact qe_congr (by linear_combination -h2) (by linear_combination -h2)
      (by linear_combination -h2)
  have h000 : qe 0 0 0 ∈ H := by rw [qe_zero_zero, transv_zero]; exact one_mem H
  intro g hg
  obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hg
  rcases h01 x with rfl | rfl <;> rcases h01 y with rfl | rfl <;> rcases h01 s with rfl | rfl
  · exact h000
  · exact h001
  · exact h010
  · have := hmul _ _ _ _ _ _ h010 h001
    convert this using 1
    exact qe_congr (by ring) (by ring) (by ring)
  · exact h₀
  · have := hmul _ _ _ _ _ _ h₀ h001
    convert this using 1
    exact qe_congr (by ring) (by ring) (by ring)
  · exact h110
  · exact h111

theorem qe_one_zero_one : qe (1 : F) 0 1 = transv (e₂ F) 1 * transv (e₁ F + e₂ F) 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ext_mulVec fun v => ?_
  rw [qe_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, form_apply, form_apply]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp
  linear_combination (-v (.inr 1)) * h2

theorem qe_zero_one_one : qe (0 : F) 1 1 = transv (f₂ F) 1 * transv (e₁ F + f₂ F) 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine ext_mulVec fun v => ?_
  rw [qe_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, form_apply, form_apply]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> linear_combination (v (.inl 1)) * h2

theorem eq_top_std' {H : Subgroup (Sp4 F)} (hq : (∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ Nat.card F = 2)
    (h1 : ∀ k ∈ Q₁ F, ∃ y ∈ H, y ∈ Q₁ F ∧ y * k⁻¹ ∈ Q₂ F)
    (h2 : ∃ n ∈ H, n ∈ qLine (mu₀ F) ∧ n ∉ Q₂ F)
    (h3 : ∃ h ∈ H, h ∈ Q₂ F ∧ h ∉ X₂ F ∧
      ((∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ h ∉ commutator (Sp4 F)) ∧ (h ∈ Q₁ F ∨ h ∈ qLine (mu₀ F)))
    (h4 : ∃ e ∈ H, (pt₀ F).map (mulVecLin (mat e)) ≠ pt₀ F ∧
      ((pt₀ F).map (mulVecLin (mat e)) ≤ ln₀ F ∨ (pt₀ F).map (mulVecLin (mat e)) ≤ mu₀ F)) :
    H = ⊤ := by
  have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
  have hup : ∀ a : F, ∃ y ∈ H, y ∈ Q₁ F ∧ mat y (.inl 1) (.inr 1) = a := by
    intro a
    obtain ⟨y, hyH, hyQ, hyk⟩ := h1 _ (transv_e₂_mem_Q₁ a)
    refine ⟨y, hyH, hyQ, ?_⟩
    have hk := (mem_Q₂_iff.1 hyk).2
    rw [entry_mul_of_mem_Q₁ hyQ (inv_mem (transv_e₂_mem_Q₁ a)),
      entry_inv_of_mem_Q₁ (transv_e₂_mem_Q₁ a), entry_transv_e₂] at hk
    simp only [and_self, ite_true] at hk
    linear_combination hk
  obtain ⟨n, hnH, hnμ, hnQ⟩ := h2
  have hne : mat n *ᵥ e₁ F = e₁ F := hnμ _ e₁_mem_mu₀
  set c := mat n (.inr 1) (.inl 1) with hcdef
  have hc : c ≠ 0 := fun h0 => hnQ (mem_Q₂_of_mem_qLine_mu₀ hnμ h0)
  have hconjt : ∀ x y s, qe x y s ∈ H → qe x (y + c * x) s ∈ H := fun x y s h => by
    have := mul_mem (mul_mem hnH h) (inv_mem hnH)
    rw [qe_conj_of_fix hne, levMat_of_mem_qLine_mu₀ hnμ] at this
    convert this using 1
    refine qe_congr ?_ ?_ rfl
    · simp
    · simp [← hcdef, add_comm]
  have hconjE : ∀ a x y s, qe x y s ∈ H → qe (x + a * y) y s ∈ H := fun a x y s h => by
    obtain ⟨k, hkH, hkQ, hka⟩ := hup a
    have hk1 : mat k *ᵥ e₁ F = e₁ F := hkQ _ (mem_ln₀.2 ⟨by simp, by simp⟩)
    have := mul_mem (mul_mem hkH h) (inv_mem hkH)
    rw [qe_conj_of_fix hk1, levMat_of_mem_Q₁ hkQ, hka] at this
    convert this using 1
    refine qe_congr ?_ ?_ rfl <;> simp
  obtain ⟨h, hhH, hhQ₂, hhX, hodd, hh⟩ := h3
  obtain ⟨x, y, s, rfl⟩ := exists_eq_qe_of_mem_Q₂ hhQ₂
  have hyQ1 : qe x y s ∈ Q₁ F → y = 0 := fun hQ1 => by
    have := congrFun (hQ1 _ (mem_ln₀.2 ⟨by simp, by simp⟩ : e₂ F ∈ ln₀ F)) (.inl 0)
    rw [qe_mulVec] at this
    simpa using this
  have hxμ : qe x y s ∈ qLine (mu₀ F) → x = 0 := fun hμ => by
    have := congrFun (hμ _ f₂_mem_mu₀) (.inl 0)
    rw [qe_mulVec] at this
    simpa using this
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hxy
    push Not at hxy
    rw [hxy.1, hxy.2, qe_zero_zero] at hhX
    exact hhX (transv_mem_X₂ s)
  have hQ₂ : Q₂ F ≤ H := by
    by_cases ht : ∃ t : F, t ≠ 0 ∧ t ≠ 1
    ·
      obtain ⟨β, s₀, hβ, h₀⟩ : ∃ β s₀ : F, β ≠ 0 ∧ qe β 0 s₀ ∈ H := by
        rcases hh with hQ1 | hμ
        · have hy := hyQ1 hQ1
          subst hy
          exact ⟨x, s, hxy.resolve_right (fun h => h rfl), hhH⟩
        · have hx := hxμ hμ
          subst hx
          have hy : y ≠ 0 := hxy.resolve_left (fun h => h rfl)
          refine ⟨y, y * y, hy, ?_⟩
          have := mul_mem (hconjE 1 0 y s hhH) hhH
          rw [qe_mul] at this
          convert this using 1
          exact qe_congr (by ring) (by linear_combination (-y) * h2')
            (by linear_combination (-s) * h2')
      exact Q₂_le_of_qe_mem ht hβ hc h₀ hconjE hconjt
    ·
      have hq2 : Nat.card F = 2 := hq.resolve_left ht
      have : Finite F := Nat.finite_of_card_ne_zero (by omega)
      have hodd' := hodd.resolve_left ht
      have h01 := eq_zero_or_eq_one_of_card_two hq2
      have hc1 : c = 1 := (h01 c).resolve_left hc
      have hE1 : ∀ x y s, qe x y s ∈ H → qe (x + y) y s ∈ H := fun x y s h => by
        have := hconjE 1 x y s h
        rwa [one_mul] at this
      have ht1 : ∀ x y s, qe x y s ∈ H → qe x (y + x) s ∈ H := fun x y s h => by
        have := hconjt x y s h
        rwa [hc1, one_mul] at this
      have hcomm : ∀ {u v : V4 F}, u ≠ 0 → v ≠ 0 → transv u 1 * transv v 1 ∈ commutator (Sp4 F) :=
        fun hu hv => transv_mul_transv_mem_commutator hu hv one_ne_zero one_ne_zero
      refine Q₂_le_of_two hq2 hE1 ht1 ?_
      rcases hh with hQ1 | hμ
      · have hy := hyQ1 hQ1
        subst hy
        have hx : x = 1 := (h01 x).resolve_left (hxy.resolve_right (fun h => h rfl))
        subst hx
        rcases h01 s with rfl | rfl
        · exact hhH
        · exact absurd (by rw [qe_one_zero_one]; exact hcomm e₂_ne_zero e₁_add_e₂_ne_zero) hodd'
      · have hx := hxμ hμ
        subst hx
        have hy : y = 1 := (h01 y).resolve_left (hxy.resolve_left (fun h => h rfl))
        subst hy
        rcases h01 s with rfl | rfl
        · have h1 := ht1 _ _ _ (hE1 _ _ _ hhH)
          rwa [zero_add, show (1 : F) + 1 = 0 by linear_combination h2'] at h1
        · refine absurd ?_ hodd'
          rw [qe_zero_one_one]
          exact hcomm f₂_ne_zero (fun h => by simpa using congrFun h (.inl 0))
  have hQ₂' : qPoint (F ∙ e₁ F) ≤ H := by rw [← pt₀_eq_span]; exact hQ₂
  obtain ⟨e, heH, hep, hel⟩ := h4
  set u := mat e *ᵥ e₁ F with hu
  have hspan : (pt₀ F).map (mulVecLin (mat e)) = F ∙ u := by
    rw [pt₀_eq_span, map_span_eq]
  have hu0 : u ≠ 0 := S59.mulVec_ne_zero e e₁_ne_zero
  have hu1 : u ∉ F ∙ e₁ F := by
    intro hmem
    refine hep ?_
    rw [hspan]
    refine eq_pt₀_of_le ?_ (isPoint_ne_bot (isPoint_span hu0))
    rw [pt₀_eq_span, Submodule.span_singleton_le_iff_mem]
    exact hmem
  have hQu : qPoint (F ∙ u) ≤ H := by
    rw [hu, ← S59.qPoint_span_map_conj]
    exact S59.map_conj_le_of_mem hQ₂' heH
  rw [hspan] at hel
  rw [eq_top_iff]
  rcases hel with hl | hl
  · have hul : u ∈ ln₀ F := (Submodule.span_singleton_le_iff_mem _ _).1 hl
    have hw0 : mat n *ᵥ u ≠ 0 := S59.mulVec_ne_zero n hu0
    have hQw : qPoint (F ∙ (mat n *ᵥ u)) ≤ H := by
      rw [← S59.qPoint_span_map_conj]
      exact S59.map_conj_le_of_mem hQu hnH
    have hopp : ¬ (F ∙ (mat n *ᵥ u)) ≤ perp (F ∙ u) := fun hle =>
      form_mulVec_ne_zero_of_mem_ln₀ hnμ hnQ hul hu1
        (mem_perp_span.1 (hle (Submodule.mem_span_singleton_self _)))
    exact (qPoint_sup_qPoint_eq_top (isPoint_span hu0) (isPoint_span hw0) hopp).ge.trans
      (sup_le hQu hQw)
  · have huμ : u ∈ mu₀ F := (Submodule.span_singleton_le_iff_mem _ _).1 hl
    obtain ⟨y, hyH, hyQ, hy1⟩ := hup 1
    have hw0 : mat y *ᵥ u ≠ 0 := S59.mulVec_ne_zero y hu0
    have hQw : qPoint (F ∙ (mat y *ᵥ u)) ≤ H := by
      rw [← S59.qPoint_span_map_conj]
      exact S59.map_conj_le_of_mem hQu hyH
    have hopp : ¬ (F ∙ (mat y *ᵥ u)) ≤ perp (F ∙ u) := fun hle =>
      form_mulVec_ne_zero_of_mem_mu₀ hyQ hy1 huμ hu1
        (mem_perp_span.1 (hle (Submodule.mem_span_singleton_self _)))
    exact (qPoint_sup_qPoint_eq_top (isPoint_span hu0) (isPoint_span hw0) hopp).ge.trans
      (sup_le hQu hQw)

end Std

theorem map_eq_of_mem_fixer {W : Submodule F (V4 F)} {g : Sp4 F} (hg : g ∈ fixer W) :
    W.map (mulVecLin (mat g)) = W :=
  mem_stab_iff.1 (fixer_le_stab W hg)

theorem exists_map_frame {γ l₁ l₂ : Submodule F (V4 F)} (hγ : IsPoint γ) (hl₁ : IsLine l₁)
    (hl₂ : IsLine l₂) (hγ₁ : γ ≤ l₁) (hγ₂ : γ ≤ l₂) (h12 : l₁ ≠ l₂) :
    ∃ φ : Sp4 F, (pt₀ F).map (mulVecLin (mat φ)) = γ ∧ (ln₀ F).map (mulVecLin (mat φ)) = l₁ ∧
      (mu₀ F).map (mulVecLin (mat φ)) = l₂ := by
  obtain ⟨φ₀, hφp, hφl⟩ := exists_map_flag hγ hl₁ hγ₁
  set m := l₂.map (mulVecLin (mat φ₀⁻¹)) with hm
  have hmL : IsLine m := isLine_map hl₂ φ₀⁻¹
  have hpm : pt₀ F ≤ m := by
    have h1 : γ.map (mulVecLin (mat φ₀⁻¹)) = pt₀ F := by rw [← hφp, map_map_mat_inv']
    rw [← h1, hm]
    exact Submodule.map_mono hγ₂
  have hmne : ¬ m ≤ ln₀ F := fun hle => h12 (by
    have := congrArg (Submodule.map (mulVecLin (mat φ₀))) (IsLine.eq_of_le hmL isLine_ln₀ hle)
    rw [hm, map_map_mat_inv, hφl] at this
    exact this.symm)
  obtain ⟨w, hwm, hwl⟩ := Set.not_subset.1 hmne
  have hw2 : w (.inr 0) = 0 := mem_perp_pt₀.1 (le_perp_of_le hmL hpm hwm)
  have hw3 : w (.inr 1) ≠ 0 := fun h3 => hwl (mem_ln₀.2 ⟨hw2, h3⟩)
  set t := w (.inl 1) / w (.inr 1) with ht
  set k := transv (e₂ F) t with hk
  have hkQ : k ∈ Q₁ F := transv_e₂_mem_Q₁ t
  have hke : mat k *ᵥ e₁ F = e₁ F := hkQ _ (mem_ln₀.2 ⟨by simp, by simp⟩)
  have hkf : mat k *ᵥ f₂ F = (w (.inr 1))⁻¹ • (w - w (.inl 0) • e₁ F) := by
    rw [hk, transv_mulVec, form_e₂]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [ht, hw2, hw3]
    field_simp
  have hkm : (mu₀ F).map (mulVecLin (mat k)) = m := by
    refine IsLine.eq_of_le (isLine_map isLine_mu₀ k) hmL ?_
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rcases hv with rfl | rfl
    · rw [mulVecLin_apply, hke]
      exact hpm (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
    · rw [mulVecLin_apply, hkf]
      refine m.smul_mem _ (m.sub_mem hwm (m.smul_mem _ ?_))
      exact hpm (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
  refine ⟨φ₀ * k, ?_, ?_, ?_⟩
  · rw [map_mat_mul, map_eq_of_mem_fixer (fixer_antitone pt₀_le_ln₀ hkQ), hφp]
  · rw [map_mat_mul, map_eq_of_mem_fixer hkQ, hφl]
  · rw [map_mat_mul, hkm, hm, map_map_mat_inv]

variable [CharP F 2]

theorem eq_top_of_frame' {γ l₁ l₂ : Submodule F (V4 F)}
    (hq : (∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ Nat.card F = 2)
    (hγ : IsPoint γ) (hl₁ : IsLine l₁) (hl₂ : IsLine l₂) (hγ₁ : γ ≤ l₁) (hγ₂ : γ ≤ l₂)
    (h12 : l₁ ≠ l₂) {H : Subgroup (Sp4 F)}
    (h1 : ∀ k ∈ qLine l₁, ∃ y ∈ H, y ∈ qLine l₁ ∧ y * k⁻¹ ∈ qPoint γ)
    (h2 : ∃ n ∈ H, n ∈ qLine l₂ ∧ n ∉ qPoint γ)
    (h3 : ∃ h ∈ H, h ∈ qPoint γ ∧ h ∉ xPoint γ ∧
      ((∃ t : F, t ≠ 0 ∧ t ≠ 1) ∨ h ∉ commutator (Sp4 F)) ∧ (h ∈ qLine l₁ ∨ h ∈ qLine l₂))
    (h4 : ∃ e ∈ H, γ.map (mulVecLin (mat e)) ≠ γ ∧
      (γ.map (mulVecLin (mat e)) ≤ l₁ ∨ γ.map (mulVecLin (mat e)) ≤ l₂)) : H = ⊤ := by
  obtain ⟨φ, hφp, hφ₁, hφ₂⟩ := exists_map_frame hγ hl₁ hl₂ hγ₁ hγ₂ h12
  have hQ1 : qLine l₁ = (Q₁ F).map (MulAut.conj φ).toMonoidHom := by rw [← hφ₁, qLine_map_eq]
  have hQ2 : qLine l₂ = (qLine (mu₀ F)).map (MulAut.conj φ).toMonoidHom := by
    rw [← hφ₂, qLine_map]
  have hQp : qPoint γ = (Q₂ F).map (MulAut.conj φ).toMonoidHom := by rw [← hφp, qPoint_map_eq]
  have hXp : xPoint γ = (X₂ F).map (MulAut.conj φ).toMonoidHom := by rw [← hφp, X₂_map_conj]
  set H₀ := H.map (MulAut.conj φ⁻¹).toMonoidHom with hH₀
  have hmem : ∀ {x : Sp4 F}, x ∈ H₀ ↔ φ * x * φ⁻¹ ∈ H := fun {x} => by
    rw [hH₀, mem_map_conj, inv_inv]
  have hconj : ∀ {K : Subgroup (Sp4 F)} {x : Sp4 F},
      x ∈ K.map (MulAut.conj φ).toMonoidHom ↔ φ⁻¹ * x * φ ∈ K := fun {_ _} => mem_map_conj
  have hφφ : ∀ x : Sp4 F, φ⁻¹ * (φ * x * φ⁻¹) * φ = x := fun x => by group
  refine eq_top_of_map_conj φ⁻¹ (eq_top_std' hq ?_ ?_ ?_ ?_)
  · intro k₀ hk₀
    obtain ⟨y, hyH, hyQ, hyk⟩ := h1 (φ * k₀ * φ⁻¹) (by rw [hQ1, hconj, hφφ]; exact hk₀)
    refine ⟨φ⁻¹ * y * φ, hmem.2 (by convert hyH using 1; group), ?_, ?_⟩
    · rw [hQ1, hconj] at hyQ
      exact hyQ
    · rw [hQp, hconj] at hyk
      convert hyk using 1
      group
  · obtain ⟨n, hnH, hnQ, hnγ⟩ := h2
    refine ⟨φ⁻¹ * n * φ, hmem.2 (by convert hnH using 1; group), ?_, ?_⟩
    · rw [hQ2, hconj] at hnQ
      exact hnQ
    · rwa [hQp, hconj] at hnγ
  · obtain ⟨h, hhH, hhQ, hhX, hodd, hhl⟩ := h3
    refine ⟨φ⁻¹ * h * φ, hmem.2 (by convert hhH using 1; group), ?_, ?_, ?_, ?_⟩
    · rwa [hQp, hconj] at hhQ
    · rwa [hXp, hconj] at hhX
    · refine hodd.imp id fun hc hc' => hc ?_
      have := (inferInstance : (commutator (Sp4 F)).Normal).conj_mem _ hc' φ
      convert this using 1
      group
    · rcases hhl with hl | hl
      · rw [hQ1, hconj] at hl
        exact Or.inl hl
      · rw [hQ2, hconj] at hl
        exact Or.inr hl
  · obtain ⟨e, heH, hep, hel⟩ := h4
    have hmap : (pt₀ F).map (mulVecLin (mat (φ⁻¹ * e * φ))) =
        (γ.map (mulVecLin (mat e))).map (mulVecLin (mat φ⁻¹)) := by
      rw [map_mat_mul, map_mat_mul, hφp]
    refine ⟨φ⁻¹ * e * φ, hmem.2 (by convert heH using 1; group), ?_, ?_⟩
    · rw [hmap]
      intro h
      apply hep
      have := congrArg (Submodule.map (mulVecLin (mat φ))) h
      rwa [map_map_mat_inv, hφp] at this
    · rw [hmap]
      rcases hel with hl | hl
      · refine Or.inl ((Submodule.map_mono hl).trans (le_of_eq ?_))
        rw [← hφ₁, map_map_mat_inv']
      · refine Or.inr ((Submodule.map_mono hl).trans (le_of_eq ?_))
        rw [← hφ₂, map_map_mat_inv']

end CFSG.Quasithin.MS93.S5
