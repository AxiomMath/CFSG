module

public import CFSG.Monster.Griess.TrialityBasis.Labels

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Subgroup

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

abbrev LtPair : Type := {p : Fin 24 × Fin 24 // p.1 < p.2}

abbrev OctadWord : Type := {d : C // hammingNorm (d : Fin 24 → ZMod 2) = 8}

abbrev octSupp (d : OctadWord) : Finset (Fin 24) := supp ((d : C) : Fin 24 → ZMod 2)

abbrev OctIdx : Type := Σ d : OctadWord, Octad.EvenQuot (octSupp d)

abbrev ShortLabel : Type := LtPair ⊕ LtPair ⊕ (C₀ × Fin 24) ⊕ OctIdx

noncomputable instance : DecidableEq OctIdx := inferInstance

noncomputable instance : DecidableEq ShortLabel :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance (@instDecidableEqSum _ _ inferInstance inferInstance))

theorem card_octSupp (d : OctadWord) : (octSupp d).card = 8 := by
  rw [card_supp]
  exact d.2

@[expose] noncomputable def octRep (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    Finset (Fin 24) :=
  (Octad.exists_cls_eq v).choose

theorem octRep_spec (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    octRep d v ⊆ octSupp d ∧ Even (octRep d v).card ∧ Octad.cls (octSupp d) (octRep d v) = v :=
  (Octad.exists_cls_eq v).choose_spec

@[expose] noncomputable def rOctQ (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) : Q :=
  rOct d (octRep d v)

theorem octRep_cls {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    octRep d (Octad.cls (octSupp d) δ) = δ ∨
      octRep d (Octad.cls (octSupp d) δ) = octSupp d \ δ := by
  obtain ⟨h1, h2, h3⟩ := octRep_spec d (Octad.cls (octSupp d) δ)
  exact (Octad.cls_eq_cls_iff hδ he h1 h2).1 h3.symm

theorem rOctQ_cls {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) : rOctQ d (Octad.cls (octSupp d) δ) = rOct d δ := by
  rcases octRep_cls hδ he with h | h
  · exact congrArg (rOct d) h
  · exact (congrArg (rOct d) h).trans (rOct_compl d.2 hδ he)

@[expose] noncomputable def labelElt : ShortLabel → Q
  | .inl p => rMinus p.1.1 p.1.2
  | .inr (.inl p) => rPlus p.1.1 p.1.2
  | .inr (.inr (.inl q)) => rOdd q.1 q.2
  | .inr (.inr (.inr o)) => rOctQ o.1 o.2

@[expose] noncomputable def labelVec : ShortLabel → Fin 24 → ℤ
  | .inl p => vMinus p.1.1 p.1.2
  | .inr (.inl p) => vPlus p.1.1 p.1.2
  | .inr (.inr (.inl q)) => oddMin q.2 ((q.1 : C) : Fin 24 → ZMod 2)
  | .inr (.inr (.inr o)) => vOct ((o.1 : C) : Fin 24 → ZMod 2) (octRep o.1 o.2)

theorem labelVec_mem : ∀ l : ShortLabel, labelVec l ∈ minVecs
  | .inl p => vMinus_mem p.2
  | .inr (.inl p) => vPlus_mem p.2
  | .inr (.inr (.inl q)) => oddMin_mem q.1 q.2
  | .inr (.inr (.inr o)) =>
    vOct_mem (o.1 : C).2 o.1.2 (octRep_spec o.1 o.2).1 (octRep_spec o.1 o.2).2.1

theorem phi0_labelElt : ∀ l : ShortLabel, phi0 (coordOf (labelElt l)) = classOf (labelVec l)
  | .inl p => phi0_coordOf_rMinus p.2
  | .inr (.inl p) => phi0_coordOf_rPlus p.2
  | .inr (.inr (.inl q)) => phi0_coordOf_rOdd q.1 q.2
  | .inr (.inr (.inr o)) =>
    phi0_coordOf_rOct o.1.2 (octRep_spec o.1 o.2).1 (octRep_spec o.1 o.2).2.1

theorem centralCoord_labelElt : ∀ l : ShortLabel, centralCoord (labelElt l) = 0
  | .inl _ => centralCoord_rMinus _ _
  | .inr (.inl _) => centralCoord_rPlus _ _
  | .inr (.inr (.inl _)) => centralCoord_rOdd _ _
  | .inr (.inr (.inr _)) => centralCoord_rOct _ _

theorem isShortCoord_labelElt (l : ShortLabel) : IsShortCoord (coordOf (labelElt l)) :=
  ⟨labelVec l, labelVec_mem l, (phi0_labelElt l).symm⟩

@[expose] noncomputable def labelIdx (l : ShortLabel) : ShortIdx :=
  ⟨coordOf (labelElt l), isShortCoord_labelElt l⟩

private theorem neg_one_pow_add_one : ∀ t : ZMod 2, (-1 : ℤ) ^ (t + 1).val = -(-1) ^ t.val := by
  decide

theorem oddMin_add_Ω (i : Fin 24) (x : Fin 24 → ZMod 2) : oddMin i (x + Ω) = -oddMin i x := by
  funext k
  simp only [oddMin, Pi.add_apply, Pi.neg_apply, Ω]
  rw [neg_one_pow_add_one]
  ring

theorem neg_vOct {d : Fin 24 → ZMod 2} {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) :
    -vOct d δ = vOct d (supp d \ δ) := by
  funext k
  simp only [vOct, liftℤ, Octad.ind, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mem_sdiff]
  by_cases hk : k ∈ supp d
  · have hdk : d k = 1 := by
      rcases zmod2_cases (d k) with h | h
      · exact absurd h (mem_supp_iff.1 hk)
      · exact h
    rw [hdk]
    by_cases hkδ : k ∈ δ
    · simp only [hkδ, hk, ite_true, not_true_eq_false, and_false, ite_false]
      rfl
    · simp only [hkδ, hk, ite_false, not_false_eq_true, and_self, ite_true]
      rfl
  · have hdk : d k = 0 := by
      by_contra h
      exact hk (mem_supp_iff.2 h)
    have hkδ : k ∉ δ := fun h => hk (hδ h)
    simp [hk, hkδ, hdk, bitLift]

theorem compl_subset_supp (d : Fin 24 → ZMod 2) (δ : Finset (Fin 24)) : supp d \ δ ⊆ supp d :=
  Finset.sdiff_subset

theorem mem_fam₁Dom' {i j : Fin 24} (hij : i < j) (s : Bool × Bool) :
    ((i, j), s) ∈ (fam₁Dom : Set _) := Finset.mem_coe.2 (mem_fam₁Dom.2 hij)

theorem mem_fam₂Dom' {d : Fin 24 → ZMod 2} (hd : d ∈ C) (hw : hammingNorm d = 8)
    {δ : Finset (Fin 24)} (hδ : δ ⊆ supp d) (he : Even δ.card) :
    (⟨d, δ⟩ : Σ _ : Fin 24 → ZMod 2, Finset (Fin 24)) ∈ (fam₂Dom : Set _) :=
  Finset.mem_coe.2 (mem_fam₂Dom.2 ⟨⟨hd, hw⟩, hδ, he⟩)

@[expose] def labelFamily : ShortLabel → Set (Fin 24 → ℤ)
  | .inl _ => minFamily₁
  | .inr (.inl _) => minFamily₁
  | .inr (.inr (.inl _)) => minFamily₃
  | .inr (.inr (.inr _)) => minFamily₂

theorem labelVec_mem_family :
    ∀ l : ShortLabel, labelVec l ∈ labelFamily l ∧ -labelVec l ∈ labelFamily l
  | .inl p => by
    refine ⟨?_, ?_⟩
    · change vMinus _ _ ∈ minFamily₁
      rw [vMinus_eq_fam₁Param]
      exact fam₁Param_mem p.2
    · change -vMinus _ _ ∈ minFamily₁
      rw [neg_vMinus_eq_fam₁Param]
      exact fam₁Param_mem p.2
  | .inr (.inl p) => by
    refine ⟨?_, ?_⟩
    · change vPlus _ _ ∈ minFamily₁
      rw [vPlus_eq_fam₁Param]
      exact fam₁Param_mem p.2
    · change -vPlus _ _ ∈ minFamily₁
      rw [neg_vPlus_eq_fam₁Param]
      exact fam₁Param_mem p.2
  | .inr (.inr (.inl q)) => by
    refine ⟨⟨q.2, _, (q.1 : C).2, rfl⟩, ?_⟩
    change -oddMin _ _ ∈ minFamily₃
    rw [← oddMin_add_Ω]
    exact ⟨q.2, _, C.add_mem (q.1 : C).2 Ω_mem_C, rfl⟩
  | .inr (.inr (.inr o)) => by
    obtain ⟨h1, h2, -⟩ := octRep_spec o.1 o.2
    refine ⟨?_, ?_⟩
    · change vOct _ _ ∈ minFamily₂
      rw [vOct_eq_fam₂Vec h1]
      exact fam₂Vec_mem (o.1 : C).2 o.1.2 h1 h2
    · change -vOct _ _ ∈ minFamily₂
      rw [neg_vOct h1, vOct_eq_fam₂Vec (compl_subset_supp _ _)]
      exact fam₂Vec_mem (o.1 : C).2 o.1.2 (compl_subset_supp _ _)
        (Octad.even_card_sdiff (by rw [card_octSupp]; decide) h1 h2)

private theorem not_pm_of_disjoint {F F' : Set (Fin 24 → ℤ)} (hF : Disjoint F F')
    {v v' : Fin 24 → ℤ} (hv : v ∈ F ∧ -v ∈ F) (hv' : v' ∈ F') : ¬(v' = v ∨ v' = -v) := by
  rintro (h | h) <;> subst h
  · exact Set.disjoint_left.1 hF hv.1 hv'
  · exact Set.disjoint_left.1 hF hv.2 hv'

theorem ltPair_eq {p q : LtPair} (h₁ : p.1.1 = q.1.1) (h₂ : p.1.2 = q.1.2) : p = q :=
  Subtype.ext (Prod.ext h₁ h₂)

theorem eq_of_labelVec {l l' : ShortLabel}
    (h : labelVec l' = labelVec l ∨ labelVec l' = -labelVec l) : l = l' := by
  rcases l with p | p | q | o <;> rcases l' with p' | p' | q' | o'
  · change vMinus _ _ = vMinus _ _ ∨ vMinus _ _ = -vMinus _ _ at h
    rw [neg_vMinus_eq_fam₁Param, vMinus_eq_fam₁Param, vMinus_eq_fam₁Param] at h
    rcases h with h | h
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp only [Prod.mk.injEq] at this
      exact congrArg Sum.inl (ltPair_eq this.1.1.symm this.1.2.symm)
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp at this
  · change vPlus _ _ = vMinus _ _ ∨ vPlus _ _ = -vMinus _ _ at h
    rw [neg_vMinus_eq_fam₁Param, vPlus_eq_fam₁Param, vMinus_eq_fam₁Param] at h
    rcases h with h | h <;>
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp at this
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₃ (labelVec_mem_family (.inl p))
      (labelVec_mem_family (.inr (.inr (.inl q')))).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₂ (labelVec_mem_family (.inl p))
      (labelVec_mem_family (.inr (.inr (.inr o')))).1)
  · change vMinus _ _ = vPlus _ _ ∨ vMinus _ _ = -vPlus _ _ at h
    rw [neg_vPlus_eq_fam₁Param, vPlus_eq_fam₁Param, vMinus_eq_fam₁Param] at h
    rcases h with h | h <;>
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp at this
  · change vPlus _ _ = vPlus _ _ ∨ vPlus _ _ = -vPlus _ _ at h
    rw [neg_vPlus_eq_fam₁Param, vPlus_eq_fam₁Param, vPlus_eq_fam₁Param] at h
    rcases h with h | h
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp only [Prod.mk.injEq] at this
      exact congrArg (fun p => Sum.inr (Sum.inl p)) (ltPair_eq this.1.1.symm this.1.2.symm)
    · have := fam₁Param_injOn (mem_fam₁Dom' p'.2 _) (mem_fam₁Dom' p.2 _) h
      simp at this
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₃ (labelVec_mem_family (.inr (.inl p)))
      (labelVec_mem_family (.inr (.inr (.inl q')))).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₂ (labelVec_mem_family (.inr (.inl p)))
      (labelVec_mem_family (.inr (.inr (.inr o')))).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₃.symm
      (labelVec_mem_family (.inr (.inr (.inl q)))) (labelVec_mem_family (.inl p')).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₃.symm
      (labelVec_mem_family (.inr (.inr (.inl q)))) (labelVec_mem_family (.inr (.inl p'))).1)
  · change oddMin _ _ = oddMin _ _ ∨ oddMin _ _ = -oddMin _ _ at h
    rw [← oddMin_add_Ω] at h
    rcases h with h | h
    · have := @oddMin_injective (_, _) (_, _) h
      simp only [Prod.mk.injEq] at this
      have hc : q'.1 = q.1 := Subtype.ext (Subtype.ext this.2)
      exact congrArg (fun q => Sum.inr (Sum.inr (Sum.inl q))) (Prod.ext hc.symm this.1.symm)
    · have := @oddMin_injective (_, _) (_, _) h
      simp only [Prod.mk.injEq] at this
      have hc : (q'.1 : C) = (q.1 : C) + ΩC := Subtype.ext this.2
      have h0 := congrArg μ₀ hc
      rw [map_add, μ₀_coe, μ₀_coe, μ₀_ΩC] at h0
      exact absurd h0 (by decide)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₂₃.symm
      (labelVec_mem_family (.inr (.inr (.inl q)))) (labelVec_mem_family (.inr (.inr (.inr o')))).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₂.symm
      (labelVec_mem_family (.inr (.inr (.inr o)))) (labelVec_mem_family (.inl p')).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₁₂.symm
      (labelVec_mem_family (.inr (.inr (.inr o)))) (labelVec_mem_family (.inr (.inl p'))).1)
  · exact absurd h (not_pm_of_disjoint disjoint_minFamily₂₃
      (labelVec_mem_family (.inr (.inr (.inr o)))) (labelVec_mem_family (.inr (.inr (.inl q')))).1)
  · obtain ⟨d, v⟩ := o
    obtain ⟨d', v'⟩ := o'
    change vOct _ _ = vOct _ _ ∨ vOct _ _ = -vOct _ _ at h
    obtain ⟨h1, h2, h3⟩ := octRep_spec d v
    obtain ⟨h1', h2', h3'⟩ := octRep_spec d' v'
    rw [neg_vOct h1, vOct_eq_fam₂Vec h1', vOct_eq_fam₂Vec h1,
      vOct_eq_fam₂Vec (compl_subset_supp _ _)] at h
    have hm := mem_fam₂Dom' (d' : C).2 d'.2 h1' h2'
    rcases h with h | h
    · have := fam₂Vec_injOn hm (mem_fam₂Dom' (d : C).2 d.2 h1 h2) h
      rw [Sigma.mk.inj_iff] at this
      have hd : d' = d := Subtype.ext (Subtype.ext this.1)
      subst hd
      have hδ : octRep d' v' = octRep d' v := eq_of_heq this.2
      rw [← h3, ← h3', hδ]
    · have := fam₂Vec_injOn hm (mem_fam₂Dom' (d : C).2 d.2 (compl_subset_supp _ _)
        (Octad.even_card_sdiff (by rw [card_octSupp]; decide) h1 h2)) h
      rw [Sigma.mk.inj_iff] at this
      have hd : d' = d := Subtype.ext (Subtype.ext this.1)
      subst hd
      have hδ : octRep d' v' = octSupp d' \ octRep d' v := eq_of_heq this.2
      rw [← h3, ← h3', hδ, Octad.cls_compl (by rw [card_octSupp]; decide) h1 h2]

theorem labelIdx_injective : Function.Injective labelIdx := by
  intro l l' h
  have hcl : classOf (labelVec l) = classOf (labelVec l') :=
    (phi0_labelElt l).symm.trans ((congrArg phi0 (congrArg Subtype.val h)).trans (phi0_labelElt l'))
  exact eq_of_labelVec ((classOf_eq_iff (labelVec_mem l) (labelVec_mem l')).1 hcl)

theorem exists_fam₁Param {u : Fin 24 → ℤ} (hu : u ∈ minFamily₁) :
    ∃ p : (Fin 24 × Fin 24) × (Bool × Bool), p.1.1 < p.1.2 ∧ fam₁Param p = u := by
  obtain ⟨hcard, hval⟩ := hu
  obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ k, u k ≠ 0 ↔ k = a ∨ k = b := fun k => by
    have := congrArg (k ∈ ·) hS
    simpa using this
  obtain ⟨i, j, hij, hsupp⟩ : ∃ i j : Fin 24, i < j ∧ ∀ k, u k ≠ 0 ↔ k = i ∨ k = j := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, hmem⟩
    · exact ⟨b, a, h, fun k => (hmem k).trans or_comm⟩
  refine ⟨((i, j), (decide (u i = -4), decide (u j = -4))), hij, ?_⟩
  funext k
  have hne : i ≠ j := ne_of_lt hij
  by_cases hk1 : k = i
  · subst hk1
    simp only [fam₁Param, ite_true, hne, ite_false, add_zero, Code.sgn]
    rcases hval k ((hsupp k).2 (Or.inl rfl)) with h | h <;> rw [h] <;> norm_num
  · by_cases hk2 : k = j
    · subst hk2
      simp only [fam₁Param, hk1, ite_false, ite_true, zero_add, Code.sgn]
      rcases hval k ((hsupp k).2 (Or.inr rfl)) with h | h <;> rw [h] <;> norm_num
    · simp only [fam₁Param, hk1, hk2, ite_false, add_zero]
      by_contra h
      rcases (hsupp k).1 (Ne.symm h) with h' | h'
      · exact hk1 h'
      · exact hk2 h'

theorem exists_label_of_mem_minVecs {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ∃ l : ShortLabel, labelVec l = u ∨ labelVec l = -u := by
  rcases mem_families_of_mem_minVecs hu with (h | h) | h
  · obtain ⟨⟨⟨i, j⟩, s, t⟩, hij, rfl⟩ := exists_fam₁Param h
    have hij' : i < j := hij
    cases s <;> cases t
    · exact ⟨.inr (.inl ⟨(i, j), hij'⟩), Or.inl (vPlus_eq_fam₁Param i j)⟩
    · exact ⟨.inl ⟨(i, j), hij'⟩, Or.inl (vMinus_eq_fam₁Param i j)⟩
    · refine ⟨.inl ⟨(i, j), hij'⟩, Or.inr ?_⟩
      change vMinus i j = _
      rw [← neg_vMinus_eq_fam₁Param, neg_neg]
    · refine ⟨.inr (.inl ⟨(i, j), hij'⟩), Or.inr ?_⟩
      change vPlus i j = _
      rw [← neg_vPlus_eq_fam₁Param, neg_neg]
  · obtain ⟨d, hd, hw, hon, hoff, heven⟩ := h
    set T : Finset (Fin 24) := Finset.univ.filter fun i => u i = -2 with hT
    have hTs : T ⊆ supp d := by
      intro i hi
      rw [hT, Finset.mem_filter] at hi
      rw [mem_supp_iff]
      intro h0
      rw [hoff i h0] at hi
      norm_num at hi
    have hu' : fam₂Vec d T = u := by
      funext i
      simp only [fam₂Vec, hT, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases h0 : d i = 0
      · simp [h0, hoff i h0]
      · simp only [h0, ite_false]
        rcases hon i h0 with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num
    let D : OctadWord := ⟨⟨d, hd⟩, hw⟩
    refine ⟨.inr (.inr (.inr ⟨D, Octad.cls (octSupp D) T⟩)), ?_⟩
    change vOct d (octRep D (Octad.cls (octSupp D) T)) = u ∨
      vOct d (octRep D (Octad.cls (octSupp D) T)) = -u
    rcases octRep_cls (d := D) hTs heven with h | h
    · rw [h, vOct_eq_fam₂Vec hTs, hu']
      exact Or.inl rfl
    · rw [h, ← neg_vOct hTs, vOct_eq_fam₂Vec hTs, hu']
      exact Or.inr rfl
  · obtain ⟨i, x, hx, rfl⟩ := h
    let c : C₀ := π₀ ⟨x, hx⟩
    have hc : ((c : C) : Fin 24 → ZMod 2) = x + μ₀ ⟨x, hx⟩ • Ω := by
      rw [coe_π₀]
      rfl
    refine ⟨.inr (.inr (.inl (c, i))), ?_⟩
    change oddMin i ((c : C) : Fin 24 → ZMod 2) = _ ∨ oddMin i ((c : C) : Fin 24 → ZMod 2) = _
    rw [hc]
    rcases zmod2_cases (μ₀ ⟨x, hx⟩) with h | h
    · left
      rw [h, zero_smul, add_zero]
    · right
      rw [h, one_smul, oddMin_add_Ω]

theorem labelIdx_surjective : Function.Surjective labelIdx := by
  intro c
  obtain ⟨u, hu, hcl⟩ := c.2
  obtain ⟨l, hl⟩ := exists_label_of_mem_minVecs hu
  refine ⟨l, Subtype.ext (phi0_injective ?_)⟩
  exact (phi0_labelElt l).trans (((classOf_eq_iff hu (labelVec_mem l)).2 hl).symm.trans hcl)

theorem labelIdx_bijective : Function.Bijective labelIdx :=
  ⟨labelIdx_injective, labelIdx_surjective⟩

@[expose] noncomputable def labelEquiv : ShortLabel ≃ ShortIdx :=
  Equiv.ofBijective labelIdx labelIdx_bijective

theorem labelEquiv_apply (l : ShortLabel) : labelEquiv l = labelIdx l := rfl

theorem mk_eq_mk_iff_coordOf (r r' : Q) :
    (QuotientGroup.mk r : Q ⧸ center Q) = QuotientGroup.mk r' ↔ coordOf r = coordOf r' := by
  constructor
  · intro h
    apply phi0_injective
    exact (toAdd_phi_mk r).symm.trans
      ((congrArg (fun c => Multiplicative.toAdd (phi c)) h).trans (toAdd_phi_mk r'))
  · intro h
    apply phi.injective
    apply Multiplicative.toAdd.injective
    exact (toAdd_phi_mk r).trans ((congrArg phi0 h).trans (toAdd_phi_mk r').symm)

theorem isShort_labelElt (l : ShortLabel) : IsShort (QuotientGroup.mk (labelElt l)) :=
  (isShort_mk_iff _).2 (isShortCoord_labelElt l)

theorem mk_labelElt_eq_iff (l l' : ShortLabel) :
    (QuotientGroup.mk (labelElt l) : Q ⧸ center Q) = QuotientGroup.mk (labelElt l') ↔ l = l' := by
  rw [mk_eq_mk_iff_coordOf]
  constructor
  · intro h
    exact labelIdx_injective (Subtype.ext h)
  · rintro rfl
    rfl

theorem exists_labelElt_of_isShort {c : Q ⧸ center Q} (hc : IsShort c) :
    ∃ l : ShortLabel, QuotientGroup.mk (labelElt l) = c := by
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective c
  have h : IsShortCoord (coordOf r) := (isShort_mk_iff r).1 ((congrArg IsShort hr).mpr hc)
  obtain ⟨l, hl⟩ := labelIdx_surjective ⟨coordOf r, h⟩
  exact ⟨l, ((mk_eq_mk_iff_coordOf _ _).2 (congrArg Subtype.val hl)).trans hr⟩

theorem mk_rOct_eq_iff {d d' : OctadWord} {δ δ' : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) (hδ' : δ' ⊆ octSupp d') (he' : Even δ'.card) :
    (QuotientGroup.mk (rOct d δ) : Q ⧸ center Q) = QuotientGroup.mk (rOct d' δ') ↔
      d = d' ∧ (δ' = δ ∨ δ' = octSupp d \ δ) := by
  have e₁ : rOct d δ = labelElt (.inr (.inr (.inr ⟨d, Octad.cls (octSupp d) δ⟩))) :=
    (rOctQ_cls hδ he).symm
  have e₂ : rOct d' δ' = labelElt (.inr (.inr (.inr ⟨d', Octad.cls (octSupp d') δ'⟩))) :=
    (rOctQ_cls hδ' he').symm
  rw [e₁, e₂, mk_labelElt_eq_iff]
  constructor
  · intro h
    have h' := Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))
    rw [Sigma.mk.inj_iff] at h'
    obtain ⟨rfl, h2⟩ := h'
    exact ⟨rfl, (Octad.cls_eq_cls_iff hδ he hδ' he').1 (eq_of_heq h2)⟩
  · rintro ⟨rfl, h⟩
    have := (Octad.cls_eq_cls_iff hδ he hδ' he').2 h
    rw [this]

end CFSG.Monster.Griess
