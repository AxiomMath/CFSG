module

public import CFSG.LocalAnalysis.StandardType.GGQ2PlaneRaw
public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG CFSG.Assembly Module
open CFSG.StandardType (GGLabelIso)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def equivLabels {t : ℕ} (k : PlaneKind) (c : Code t) : Set LargeEvenLabel :=
  {lab | GGLabelIso (label k c) lab}

private lemma l02qfrp_sq_eq_one (a : F) (ha : a ≠ 0) : a * a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · decide
  · decide

private noncomputable def l02qfrp_centToProd {t : ℕ} (k : PlaneKind) (e : V t) (i₀ : Fin t) :
    cent k (Code.extension e) →ₗ[F] (F × ({i : Fin t // i ∉ Code.extSupport e} → F)) where
  toFun w := (e i₀ * (w : V t) i₀,
    fun (i : {i : Fin t // i ∉ Code.extSupport e}) => (w : V t) i.1)
  map_add' w₁ w₂ := by
    apply Prod.ext
    · simp [mul_add]
    · funext i; simp
  map_smul' c w := by
    apply Prod.ext
    · simp [mul_comm, mul_left_comm, mul_assoc]
    · funext i; simp

private lemma l02qfrp_centToProd_injective {t : ℕ} (k : PlaneKind) (e : V t) (i₀ : Fin t)
    (hi₀ : i₀ ∈ Code.extSupport e) :
    Function.Injective (l02qfrp_centToProd k e i₀) := by
  intro w₁ w₂ h
  apply Subtype.ext
  funext i
  have h1 : e i₀ * (w₁ : V t) i₀ = e i₀ * (w₂ : V t) i₀ := congrArg Prod.fst h
  have h2 : (fun (i : {i : Fin t // i ∉ Code.extSupport e}) => (w₁ : V t) i.1) =
      (fun (i : {i : Fin t // i ∉ Code.extSupport e}) => (w₂ : V t) i.1) :=
    congrArg Prod.snd h
  by_cases hi : i ∈ Code.extSupport e
  · have hw1 := (mem_cent_extension k e (w₁ : V t)).mp w₁.2
    have hw2 := (mem_cent_extension k e (w₂ : V t)).mp w₂.2
    have hc1 : e i * (w₁ : V t) i = e i₀ * (w₁ : V t) i₀ := hw1 i hi i₀ hi₀
    have hc2 : e i * (w₂ : V t) i = e i₀ * (w₂ : V t) i₀ := hw2 i hi i₀ hi₀
    have hsq : e i * e i = 1 := l02qfrp_sq_eq_one (e i) (by simpa using hi)
    calc (w₁ : V t) i = (e i * e i) * (w₁ : V t) i := by rw [hsq, one_mul]
      _ = e i * (e i * (w₁ : V t) i) := by ring
      _ = e i * (e i₀ * (w₁ : V t) i₀) := by rw [hc1]
      _ = e i * (e i₀ * (w₂ : V t) i₀) := by rw [h1]
      _ = e i * (e i * (w₂ : V t) i) := by rw [← hc2]
      _ = (e i * e i) * (w₂ : V t) i := by ring
      _ = (w₂ : V t) i := by rw [hsq, one_mul]
  · have := congrFun h2 ⟨i, hi⟩
    simpa using this

private lemma l02qfrp_centToProd_surjective {t : ℕ} (k : PlaneKind) (e : V t) (i₀ : Fin t)
    (hi₀ : i₀ ∈ Code.extSupport e) :
    Function.Surjective (l02qfrp_centToProd k e i₀) := by
  intro p
  refine ⟨⟨fun i => if h : i ∈ Code.extSupport e then p.1 * e i else p.2 ⟨i, h⟩, ?_⟩, ?_⟩
  · rw [mem_cent_extension]
    intro i hi j hj
    simp only [dif_pos hi, dif_pos hj]
    calc e i * (p.1 * e i) = p.1 * (e i * e i) := by ring
      _ = p.1 * 1 := by rw [l02qfrp_sq_eq_one (e i) (by simpa using hi)]
      _ = p.1 * (e j * e j) := by rw [l02qfrp_sq_eq_one (e j) (by simpa using hj)]
      _ = e j * (p.1 * e j) := by ring
  · apply Prod.ext
    · dsimp [l02qfrp_centToProd]
      rw [dif_pos hi₀]
      calc e i₀ * (p.1 * e i₀) = p.1 * (e i₀ * e i₀) := by ring
        _ = p.1 * 1 := by rw [l02qfrp_sq_eq_one (e i₀) (by simpa using hi₀)]
        _ = p.1 := mul_one p.1
    · funext i
      dsimp [l02qfrp_centToProd]
      rw [dif_neg i.2]

private lemma l02qfrp_label_extension_tag {t : ℕ} (k : PlaneKind) (e : V t) :
    (label k (Code.extension e)).tag = .A ∨ (label k (Code.extension e)).tag = .twA := by
  cases k <;> simp [label]

private lemma l02qfrp_label_extension_rank {t : ℕ} (k : PlaneKind) (e : V t) :
    (label k (Code.extension e)).rank = (Code.extSupport e).card - 1 := by
  cases k <;> simp [label]

private lemma l02qfrp_not_admissible_zero_empty {t : ℕ} (k : PlaneKind) :
    ¬ admissible k (Code.zero (∅ : Finset (Fin t))) := by
  cases k with
  | linear ε => fin_cases ε <;> norm_num [admissible]
  | symplectic => norm_num [admissible]
  | orthogonal δ => fin_cases δ <;> norm_num [admissible]

private lemma l02qfrp_ggLabelIso_eq_of_rank_ge_four {lab lab' : LargeEvenLabel}
    (htag : lab.tag = .A ∨ lab.tag = .twA) (hrank : 4 ≤ lab.rank)
    (h : GGLabelIso lab lab') : lab' = lab := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · exact h.symm
  · rcases h.1 with hB | hC
    · rcases htag with hA | htwA
      · rw [hA] at hB; cases hB
      · rw [htwA] at hB; cases hB
    · rcases htag with hA | htwA
      · rw [hA] at hC; cases hC
      · rw [htwA] at hC; cases hC
  · obtain ⟨h1, _⟩ := h; rw [h1] at hrank; simp at hrank
  · obtain ⟨h1, _⟩ := h; rw [h1] at hrank; simp at hrank
  · obtain ⟨h1, _⟩ := h; rw [h1] at hrank; simp at hrank
  · obtain ⟨h1, _⟩ := h; rw [h1] at hrank; simp at hrank
  · obtain ⟨h1, _⟩ := h; rw [h1] at hrank; simp at hrank
  · obtain ⟨_, h2⟩ := h; rw [h2] at hrank; simp at hrank

private lemma l02qfrp_not_twoNodeLabels {labK labJ : LargeEvenLabel}
    (hK : labK.tag = .A ∨ labK.tag = .twA)
    (hJ : labJ.tag = .A ∨ labJ.tag = .twA)
    (hr : ¬ labK.rank = labJ.rank + 2) :
    ¬ TwoNodeLabels 3 labK labJ := by
  unfold TwoNodeLabels
  rintro (⟨hJ1, hK1, hrank, _⟩ | ⟨hJ2, hK2, hrank, _⟩ | ⟨hJ3, _⟩ | ⟨hJ4, _⟩)
  · exact hr hrank
  · exact hr hrank
  · rcases hJ with h | h <;> rw [h] at hJ3 <;> cases hJ3
  · rcases hJ with h | h <;> rw [h] at hJ4 <;> cases hJ4

theorem occurs_le_cent {t : ℕ} (k : PlaneKind) (W : Submodule F (V t)) (c : Code t)
    (h : occurs W c) : W ≤ cent k c := by
  intro w hw
  cases c with
  | zero S =>
      rw [mem_cent_zero]
      intro i hi
      exact (h i).mp hi ⟨w, hw⟩
  | extension e =>
      rw [mem_cent_extension]
      obtain ⟨he, χ, hχ, hsupp, hoff⟩ := h
      intro i hi j hj
      have hi' : e i ≠ 0 := by simpa using hi
      have hj' : e j ≠ 0 := by simpa using hj
      have hwi : (w : V t) i = e i * χ ⟨w, hw⟩ := by
        have h1 := congrArg (fun f => f ⟨w, hw⟩) (hsupp i hi')
        simpa [evalRestr] using h1
      have hwj : (w : V t) j = e j * χ ⟨w, hw⟩ := by
        have h1 := congrArg (fun f => f ⟨w, hw⟩) (hsupp j hj')
        simpa [evalRestr] using h1
      have hχi : e i * (w : V t) i = χ ⟨w, hw⟩ := by
        rw [hwi, ← mul_assoc, l02qfrp_sq_eq_one (e i) hi', one_mul]
      have hχj : e j * (w : V t) j = χ ⟨w, hw⟩ := by
        rw [hwj, ← mul_assoc, l02qfrp_sq_eq_one (e j) hj', one_mul]
      rw [hχi, hχj]

theorem finrank_cent_extension {t : ℕ} (k : PlaneKind) (e : V t) (he : e ≠ 0) :
    finrank F (cent k (Code.extension e)) = 1 + (t - (Code.extSupport e).card) := by
  have hSne : (Code.extSupport e).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply he
    funext i
    have : i ∉ Code.extSupport e := by rw [h]; simp
    simpa [Code.extSupport] using this
  obtain ⟨i₀, hi₀⟩ := hSne
  have hequiv : cent k (Code.extension e) ≃ₗ[F]
      (F × ({i : Fin t // i ∉ Code.extSupport e} → F)) :=
    LinearEquiv.ofBijective (l02qfrp_centToProd k e i₀)
      ⟨l02qfrp_centToProd_injective k e i₀ hi₀, l02qfrp_centToProd_surjective k e i₀ hi₀⟩
  rw [hequiv.finrank_eq, Module.finrank_prod, Module.finrank_self,
      Module.finrank_fintype_fun_eq_card]
  congr 1
  rw [Fintype.card_subtype]
  have hcompl : (Finset.univ.filter fun i : Fin t => i ∉ Code.extSupport e) =
      (Code.extSupport e)ᶜ := by
    ext i; simp
  rw [hcompl, Finset.card_compl]
  simp

theorem plane_noInternalTwoNode {t : ℕ} (ht : 4 ≤ t) (k : PlaneKind) (v : V t) (hv : v ≠ 0)
    (U : Submodule F (V t)) (hU : finrank F U = 2) (hvU : v ∈ U) (c j : Code t)
    (hc : admissible k c) (hj : admissible k j)
    (hocc_c : occurs (Submodule.span F {v}) c) (hocc_j : occurs U j)
    (hcent_c : cent k c = Submodule.span F {v}) (hcent_j : cent k j ≤ U)
    (hin : v ∈ inside k c) :
    ∀ labK ∈ equivLabels k c, ∀ labJ ∈ equivLabels k j,
      ¬ CFSG.StandardType.GGQ2Frame.TwoNodeLabels 3 labK labJ := by
  have hcj : cent k j = U := le_antisymm hcent_j (occurs_le_cent k U j hocc_j)
  have hc_ext : ∃ e, c = Code.extension e := by
    cases c with
    | zero S =>
        exfalso
        have hv_cent : v ∈ cent k (Code.zero S) := by
          rw [hcent_c]
          exact Submodule.mem_span_singleton_self v
        have hv_zero : ∀ i ∈ S, v i = 0 := (mem_cent_zero k S v).mp hv_cent
        have hv_supp : vSupport v ⊆ S := (mem_inside_zero k S v).mp hin
        have hne : (vSupport v).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro h
          apply hv
          funext i
          have : i ∉ vSupport v := by rw [h]; simp
          simpa [vSupport] using this
        obtain ⟨i, hi⟩ := hne
        have hiS : i ∈ S := hv_supp hi
        have hvi : v i = 0 := hv_zero i hiS
        have hvine : v i ≠ 0 := by simpa [vSupport] using hi
        exact hvine hvi
    | extension e => exact ⟨e, rfl⟩
  obtain ⟨e, rfl⟩ := hc_ext
  have he : e ≠ 0 := hc.1
  have hS_card : (Code.extSupport e).card = t := by
    have hfr := finrank_cent_extension k e he
    rw [hcent_c, finrank_span_singleton hv] at hfr
    have hle : (Code.extSupport e).card ≤ t := by
      simpa using Finset.card_le_univ (Code.extSupport e)
    omega
  have hS_univ : Code.extSupport e = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa using hS_card
  have hei : ∀ i, e i ≠ 0 := by
    intro i
    have : i ∈ Code.extSupport e := by rw [hS_univ]; exact Finset.mem_univ i
    simpa using this
  have he_cent : e ∈ cent k (Code.extension e) := by
    rw [mem_cent_extension]
    intro i hi j hj
    rw [l02qfrp_sq_eq_one (e i) (hei i), l02qfrp_sq_eq_one (e j) (hei j)]
  have he_span : e ∈ Submodule.span F {v} := by
    rw [← hcent_c]
    exact he_cent
  obtain ⟨a, ha_span⟩ := Submodule.mem_span_singleton.mp he_span
  have ha : ∀ i, e i = a * v i := by
    intro i
    have := congrArg (fun w => w i) ha_span
    simpa using this.symm
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact he (by rw [← ha_span]; simp)
  have hsq_a : a * a = 1 := l02qfrp_sq_eq_one a ha0
  have hv_e : ∀ i, v i = a * e i := by
    intro i
    calc v i = (a * a) * v i := by rw [hsq_a, one_mul]
      _ = a * (a * v i) := by ring
      _ = a * e i := by rw [← ha i]
  have hv_ne : ∀ i, v i ≠ 0 := by
    intro i hvi
    have heq : e i = a * v i := by
      calc e i = a * (a * e i) := by rw [← mul_assoc, hsq_a, one_mul]
        _ = a * v i := by rw [← hv_e i]
    rw [hvi, mul_zero] at heq
    exact hei i heq
  have hsum : (∑ i : Fin t, e i * v i) = 0 := ((mem_inside_extension k e v).mp hin).2
  have hsum_const : (∑ i : Fin t, a) = 0 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro i _
    calc a = a * 1 := (mul_one a).symm
      _ = a * (e i * e i) := by rw [l02qfrp_sq_eq_one (e i) (hei i)]
      _ = e i * (a * e i) := by ring
      _ = e i * v i := by rw [← hv_e i]
  have hta : (t : F) * a = 0 := by
    have h := hsum_const
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h
    simpa [nsmul_eq_mul] using h
  have htF : (t : F) = 0 := by
    have h := congrArg (fun x : F => x * a) hta
    rw [zero_mul] at h
    rwa [mul_assoc, hsq_a, mul_one] at h
  have h3 : 3 ∣ t := (CharP.cast_eq_zero_iff (ZMod 3) 3 t).mp htF
  have h6 : 6 ≤ t := by
    obtain ⟨m, hm⟩ := h3
    omega
  have hj_ext : ∃ f, j = Code.extension f := by
    cases j with
    | zero T =>
        exfalso
        have hT_empty : T = ∅ := by
          ext i
          constructor
          · intro hiT
            have hvi : v i = 0 := by
              simpa using (hocc_j i).mp hiT ⟨v, hvU⟩
            exact (hv_ne i hvi).elim
          · intro hi
            simp at hi
        rw [hT_empty] at hj
        exact l02qfrp_not_admissible_zero_empty k hj
    | extension f => exact ⟨f, rfl⟩
  obtain ⟨f, rfl⟩ := hj_ext
  have hf : f ≠ 0 := hj.1
  have hT_card : (Code.extSupport f).card = t - 1 := by
    have hfr := finrank_cent_extension k f hf
    rw [hcj, hU] at hfr
    have hle : (Code.extSupport f).card ≤ t := by
      simpa using Finset.card_le_univ (Code.extSupport f)
    omega
  have hlabK_tag := l02qfrp_label_extension_tag k e
  have hlabK_rank : (label k (Code.extension e)).rank = t - 1 := by
    rw [l02qfrp_label_extension_rank k e, hS_card]
  have hlabJ_tag := l02qfrp_label_extension_tag k f
  have hlabJ_rank : (label k (Code.extension f)).rank = t - 2 := by
    rw [l02qfrp_label_extension_rank k f, hT_card]
    omega
  have hr : ¬ (label k (Code.extension e)).rank = (label k (Code.extension f)).rank + 2 := by
    rw [hlabK_rank, hlabJ_rank]
    omega
  have hbase : ¬ TwoNodeLabels 3 (label k (Code.extension e)) (label k (Code.extension f)) :=
    l02qfrp_not_twoNodeLabels hlabK_tag hlabJ_tag hr
  intro labK hK labJ hJ h2
  have hKeq : labK = label k (Code.extension e) :=
    l02qfrp_ggLabelIso_eq_of_rank_ge_four hlabK_tag (by rw [hlabK_rank]; omega) hK
  have hJeq : labJ = label k (Code.extension f) :=
    l02qfrp_ggLabelIso_eq_of_rank_ge_four hlabJ_tag (by rw [hlabJ_rank]; omega) hJ
  rw [hKeq, hJeq] at h2
  exact hbase h2

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw
