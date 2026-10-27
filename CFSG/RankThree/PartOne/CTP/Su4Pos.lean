module

public import CFSG.RankThree.PartOne.CTP.Su4Plane

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} [NeZero p] {ζ : K}

theorem su4_pos_LS [CharP K 2] (hσ : IsUnitaryInvolution σ) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ l : K, l ^ p = 1 → σ l = l) {gB : SUid σ 4} (hgB : gB ^ p = 1)
    {W : Submodule K (Fin 4 → K)} (hdim : Module.finrank K W = 2)
    (hnd : ∀ w ∈ W, (∀ u ∈ W, herm σ u w = 0) → w = 0) (hWstab : ∀ v ∈ W, gB • v ∈ W)
    {l : K} (hl : l ≠ 1) (hlp : l ^ p = 1) (hL2 : Module.finrank K (eigU gB l) = 2)
    (hL2' : Module.finrank K (eigU gB l⁻¹) = 2) (hcompl : IsCompl (eigU gB l) (eigU gB l⁻¹))
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eigU gB μ = ⊥) :
    ∃ b : Fin 4 → (Fin 4 → K),
      (∀ i j, herm σ (b i) (b j) = if j = Fin.rev i then 1 else 0) ∧
      Submodule.span K {b 0, b 1} = eigU gB l ∧ Submodule.span K {b 2, b 3} = eigU gB l⁻¹ ∧
      Submodule.span K {b 1, b 2} = W := by
  classical
  have hinv := hσ.invol
  have hl' : l⁻¹ ≠ 1 := fun h => hl (inv_eq_one.mp h)
  have hlp' : (l⁻¹) ^ p = 1 := by rw [inv_pow, hlp, inv_one]
  have hσl := hfix l hlp
  have hσl' := hfix _ hlp'
  have hLiso : ∀ x ∈ eigU gB l, ∀ y ∈ eigU gB l, herm σ x y = 0 := fun x hx y hy =>
    herm_eigU_self_eq_zero gB hl hσl hx hy
  have hL'iso : ∀ x ∈ eigU gB l⁻¹, ∀ y ∈ eigU gB l⁻¹, herm σ x y = 0 := fun x hx y hy =>
    herm_eigU_self_eq_zero gB hl' hσl' hx hy
  have hsplit := le_iSup_inf_eigU hζ hgB hWstab
  have hWne : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  have hWL' : W ⊓ eigU gB l⁻¹ ≠ ⊥ := by
    intro h0
    apply hWne
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_inf_add_of_stableU hzero hsplit hv
    have hb0 : b = 0 := by
      have : b ∈ W ⊓ eigU gB l⁻¹ := hb
      rw [h0] at this
      exact (Submodule.mem_bot K).mp this
    rw [hb0, add_zero] at hab
    subst hab
    refine (Submodule.mem_bot K).mpr (hnd a ha.1 fun w hw => ?_)
    obtain ⟨a', ha', b', hb', hab'⟩ := exists_mem_inf_add_of_stableU hzero hsplit hw
    have hb'0 : b' = 0 := by
      have : b' ∈ W ⊓ eigU gB l⁻¹ := hb'
      rw [h0] at this
      exact (Submodule.mem_bot K).mp this
    rw [hb'0, add_zero] at hab'
    subst hab'
    exact hLiso a' ha'.2 a ha.2
  have hWL : W ⊓ eigU gB l ≠ ⊥ := by
    intro h0
    apply hWne
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mem_inf_add_of_stableU hzero hsplit hv
    have ha0 : a = 0 := by
      have : a ∈ W ⊓ eigU gB l := ha
      rw [h0] at this
      exact (Submodule.mem_bot K).mp this
    rw [ha0, zero_add] at hab
    subst hab
    refine (Submodule.mem_bot K).mpr (hnd b hb.1 fun w hw => ?_)
    obtain ⟨a', ha', b', hb', hab'⟩ := exists_mem_inf_add_of_stableU hzero hsplit hw
    have ha'0 : a' = 0 := by
      have : a' ∈ W ⊓ eigU gB l := ha'
      rw [h0] at this
      exact (Submodule.mem_bot K).mp this
    rw [ha'0, zero_add] at hab'
    subst hab'
    exact hL'iso b' hb'.2 b hb.2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWL
  obtain ⟨u', hu', hu'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWL'
  have huL : u ∈ eigU gB l := hu.2
  have huW : u ∈ W := hu.1
  have hu'L : u' ∈ eigU gB l⁻¹ := hu'.2
  have hu'W : u' ∈ W := hu'.1
  have hdisj : Disjoint (eigU gB l) (eigU gB l⁻¹) := hcompl.disjoint
  have hu'ns : u' ∉ Submodule.span K {u} := by
    intro h
    have h1 : u' ∈ eigU gB l :=
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huL)) h
    exact hu'0 (Submodule.disjoint_def.mp hdisj u' h1 hu'L)
  have hspanW : Submodule.span K {u, u'} = W := by
    have hle : Submodule.span K {u, u'} ≤ W := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact huW
      · exact hu'W)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hu0 hu'ns, hdim])
  have hhuu' : herm σ u u' ≠ 0 := by
    intro h0
    apply hWne
    have hWiso : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0 := by
      intro x hx y hy
      rw [← hspanW] at hx hy
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
      obtain ⟨s', t', rfl⟩ := Submodule.mem_span_pair.mp hy
      have h1 : herm σ u' u = 0 := herm_eq_zero_comm σ hinv h0
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right,
        hLiso u huL u huL, hL'iso u' hu'L u' hu'L, h0, h1]
      ring
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot K).mpr (hnd v hv fun w hw => hWiso w hw v hv)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, c₀ = herm σ u u' := ⟨_, rfl⟩
  have hhuu'' : c₀ ≠ 0 := by rw [hc₀]; exact hhuu'
  obtain ⟨u'', hu''def⟩ : ∃ u'' : Fin 4 → K, u'' = c₀⁻¹ • u' := ⟨_, rfl⟩
  have hu''L : u'' ∈ eigU gB l⁻¹ := by rw [hu''def]; exact Submodule.smul_mem _ _ hu'L
  have hu''W : u'' ∈ W := by rw [hu''def]; exact W.smul_mem _ hu'W
  have huu'' : herm σ u u'' = 1 := by
    rw [hu''def, herm_smul_right, ← hc₀, inv_mul_cancel₀ hhuu'']
  have hu''u : herm σ u'' u = 1 := by rw [herm_conj σ hinv, huu'', map_one]
  have hu''0 : u'' ≠ 0 := fun h => by rw [h, herm_zero_right] at huu''; exact zero_ne_one huu''
  have hu''ns : u'' ∉ Submodule.span K {u} := by
    intro h
    have h1 : u'' ∈ eigU gB l :=
      (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huL)) h
    exact hu''0 (Submodule.disjoint_def.mp hdisj u'' h1 hu''L)
  obtain ⟨e, he, heu⟩ : ∃ e ∈ eigU gB l, e ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    have hle : eigU gB l ≤ Submodule.span K {u} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at this
    omega
  obtain ⟨f, hf, hfu⟩ : ∃ f ∈ eigU gB l⁻¹, f ∉ Submodule.span K {u''} := by
    by_contra hcon
    push Not at hcon
    have hle : eigU gB l⁻¹ ≤ Submodule.span K {u''} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu''0] at this
    omega
  obtain ⟨e₀, he₀def⟩ : ∃ e₀ : Fin 4 → K, e₀ = e - σ (herm σ e u'') • u := ⟨_, rfl⟩
  have he₀L : e₀ ∈ eigU gB l := by
    rw [he₀def]
    exact Submodule.sub_mem _ he (Submodule.smul_mem _ _ huL)
  have he₀u'' : herm σ e₀ u'' = 0 := by
    rw [he₀def, herm_sub_left, herm_smul_left, hinv, huu'', mul_one, sub_self]
  have he₀ns : e₀ ∉ Submodule.span K {u} := by
    intro h
    apply heu
    have : e = e₀ + σ (herm σ e u'') • u := by rw [he₀def]; abel
    rw [this]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  have he₀0 : e₀ ≠ 0 := fun h => he₀ns (h ▸ Submodule.zero_mem _)
  obtain ⟨f₀, hf₀def⟩ : ∃ f₀ : Fin 4 → K, f₀ = f - herm σ u f • u'' := ⟨_, rfl⟩
  have hf₀L' : f₀ ∈ eigU gB l⁻¹ := by
    rw [hf₀def]
    exact Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hu''L)
  have huf₀ : herm σ u f₀ = 0 := by
    rw [hf₀def, herm_sub_right, herm_smul_right, huu'', mul_one, sub_self]
  have hf₀ns : f₀ ∉ Submodule.span K {u''} := by
    intro h
    apply hfu
    have : f = f₀ + herm σ u f • u'' := by rw [hf₀def]; abel
    rw [this]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u''))
  have hf₀0 : f₀ ≠ 0 := fun h => hf₀ns (h ▸ Submodule.zero_mem _)
  have hLspan : Submodule.span K {u, e₀} = eigU gB l := by
    have hle : Submodule.span K {u, e₀} ≤ eigU gB l := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact huL
      · exact he₀L)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hu0 he₀ns, hL2])
  have hL'span₀ : Submodule.span K {u'', f₀} = eigU gB l⁻¹ := by
    have hle : Submodule.span K {u'', f₀} ≤ eigU gB l⁻¹ := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hu''L
      · exact hf₀L')
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hu''0 hf₀ns, hL2'])
  have hef : herm σ e₀ f₀ ≠ 0 := by
    intro h
    apply he₀0
    refine eq_zero_of_herm σ fun y => ?_
    have hy : y ∈ eigU gB l ⊔ eigU gB l⁻¹ := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x, hx, x', hx', rfl⟩ := Submodule.mem_sup.mp hy
    rw [herm_add_right, hLiso e₀ he₀L x hx, zero_add]
    rw [← hL'span₀] at hx'
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx'
    rw [herm_add_right, herm_smul_right, herm_smul_right, he₀u'', h]
    ring
  obtain ⟨f₁, hf₁def⟩ : ∃ f₁ : Fin 4 → K, f₁ = (herm σ e₀ f₀)⁻¹ • f₀ := ⟨_, rfl⟩
  have hf₁L' : f₁ ∈ eigU gB l⁻¹ := by rw [hf₁def]; exact Submodule.smul_mem _ _ hf₀L'
  have hef₁ : herm σ e₀ f₁ = 1 := by rw [hf₁def, herm_smul_right, inv_mul_cancel₀ hef]
  have huf₁ : herm σ u f₁ = 0 := by rw [hf₁def, herm_smul_right, huf₀, mul_zero]
  have hf₁ns : f₁ ∉ Submodule.span K {u''} := by
    intro h
    apply hf₀ns
    have : f₀ = herm σ e₀ f₀ • f₁ := by rw [hf₁def, smul_smul, mul_inv_cancel₀ hef, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h
  have hf₁0 : f₁ ≠ 0 := fun h => hf₁ns (h ▸ Submodule.zero_mem _)
  have hL'span : Submodule.span K {u'', f₁} = eigU gB l⁻¹ := by
    have hle : Submodule.span K {u'', f₁} ≤ eigU gB l⁻¹ := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hu''L
      · exact hf₁L')
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hu''0 hf₁ns, hL2'])
  have hWspan : Submodule.span K {u, u''} = W := by
    have hle : Submodule.span K {u, u''} ≤ W := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact huW
      · exact hu''W)
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [finrank_span_pair_of_not_mem hu0 hu''ns, hdim])
  refine ⟨![e₀, u, u'', f₁], ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [Fin.rev]
    · exact hLiso e₀ he₀L e₀ he₀L
    · exact hLiso e₀ he₀L u huL
    · exact he₀u''
    · exact hef₁
    · exact hLiso u huL e₀ he₀L
    · exact hLiso u huL u huL
    · exact huu''
    · exact huf₁
    · rw [herm_conj σ hinv, he₀u'', map_zero]
    · exact hu''u
    · exact hL'iso u'' hu''L u'' hu''L
    · exact hL'iso u'' hu''L f₁ hf₁L'
    · rw [herm_conj σ hinv, hef₁, map_one]
    · rw [herm_conj σ hinv, huf₁, map_zero]
    · exact hL'iso f₁ hf₁L' u'' hu''L
    · exact hL'iso f₁ hf₁L' f₁ hf₁L'
  · simpa [Set.pair_comm] using hLspan
  · simpa using hL'span
  · simpa using hWspan

end CFSG.RankThree.PartOne.CTP
