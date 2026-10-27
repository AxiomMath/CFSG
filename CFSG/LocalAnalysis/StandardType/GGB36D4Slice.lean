module

public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqD4s_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k + 1, ?_⟩
      rw [pow_succ]; omega
    · left
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k - 1, ?_⟩
      rw [pow_succ]; omega

private theorem ltqD4s_kacRE {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : GGKacRE lab 3 := by
  refine ⟨by norm_num, by norm_num, ltqD4s_three_dvd lab.n, ?_⟩
  rcases htag with h | h
  · exact Or.inr (Or.inl ⟨Or.inl h, Or.inl rfl⟩)
  · exact Or.inr (Or.inl ⟨Or.inr h, Or.inl rfl⟩)

private theorem ltqD4s_compList (hRE : GGK0CompRE) {lab : LargeEvenLabel}
    (hΛ : LargeEvenInLambda2 lab) (htag : lab.tag = .E6 ∨ lab.tag = .twE6) :
    GGCompList lab 3 (fun l => ∃ D : GGKacDatum, GGKacValid lab 3 D ∧
      ∃ o ∈ D.orbits, o.qs = true ∧ lab.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
        l = o.lab) := by
  have hRE' : GGKacRE lab 3 := ltqD4s_kacRE hΛ htag
  unfold GGCompList LargeEvenLabelAll
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (hRE 3 lab hΛ hRE' Q hQ)
  rintro R _ I F ⟨hQ', hbody⟩
  refine ⟨hQ', ?_⟩
  intro L' _ _ ψ hψ hker hcomm e hep hne hind J hJ
  obtain ⟨D, hValid, ha, hb, hc⟩ := hbody L' ψ hψ hker hcomm e hep hind
  obtain ⟨o, ho, hqs, hdvd, hΛo, hlabo⟩ := ha J hJ
  exact ⟨o.lab, ⟨D, hValid, o, ho, hqs, hdvd, hΛo, rfl⟩, hlabo⟩

private theorem ltqD4s_fin_false2 :
    ∀ D' ∈ ggKacTable .E6 false 3 2, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → o'.lab.n / 2 = 1 := by
  decide

private theorem ltqD4s_fin_true1 :
    ∀ D' ∈ ggKacTable .E6 true 3 1, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → o'.lab.n / 1 = 1 := by
  decide

private theorem ltqD4s_fin_false1 :
    ∀ D' ∈ ggKacTable .E6 false 3 1, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → False := by
  decide

private theorem ltqD4s_fin_true2 :
    ∀ D' ∈ ggKacTable .E6 true 3 2, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → False := by
  decide

private theorem ltqD4s_shape_of {n : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .D)
    (hrank : lab.rank = 4) : ggKacShapeLabel n lab = (.D, 4, lab.n / n) := by
  unfold ggKacShapeLabel
  rw [htag, hrank]

private theorem ltqD4s_shape_eq {n k : ℕ} {o : GGKacOrbit}
    (h : ggKacShapeLabel n o.lab = (.D, 4, k)) :
    o.lab.tag = .D ∧ o.lab.rank = 4 ∧ o.lab.n / n = k := by
  unfold ggKacShapeLabel at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩

private theorem ltqD4s_extract {tw : Bool} {n n₀ : ℕ}
    (hshape : (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable .E6 tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (htagD : o.lab.tag = .D) (hrankD : o.lab.rank = 4)
    (hfin : ∀ D' ∈ ggKacTable .E6 tw 3 n₀, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → o'.lab.n / n₀ = 1) :
    o.lab.n / n = 1 := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hshapeOrb : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) : Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using this.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  have hshapeR : ggKacShapeLabel n₀ o'.lab = (.D, 4, o.lab.n / n) := by
    rw [heqo, ltqD4s_shape_of htagD hrankD]
  obtain ⟨htag', hrank', hn'⟩ := ltqD4s_shape_eq hshapeR
  have h1 := hfin D' hD'mem o' ho' htag' hrank'
  exact hn'.symm.trans h1

private theorem ltqD4s_extract_false {tw : Bool} {n n₀ : ℕ}
    (hshape : (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable .E6 tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (htagD : o.lab.tag = .D) (hrankD : o.lab.rank = 4)
    (hfin : ∀ D' ∈ ggKacTable .E6 tw 3 n₀, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → False) : False := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable .E6 tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hshapeOrb : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) : Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using this.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  have hshapeR : ggKacShapeLabel n₀ o'.lab = (.D, 4, o.lab.n / n) := by
    rw [heqo, ltqD4s_shape_of htagD hrankD]
  obtain ⟨htag', hrank', -⟩ := ltqD4s_shape_eq hshapeR
  exact hfin D' hD'mem o' ho' htag' hrank'

private theorem ltqD4s_shape {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6)
    {D : GGKacDatum} (hValid : GGKacValid lab 3 D)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (hqs : o.qs = true)
    (htagD : o.lab.tag = .D) (hrankD : o.lab.rank = 4)
    (hdvd : lab.n ∣ o.lab.n) :
    o.lab.n = lab.n ∧ (lab.tag = .E6 → 3 ∣ 2 ^ lab.n - 1) ∧
      (lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1) := by
  have hn : 1 ≤ lab.n := hΛ.1
  obtain ⟨T, tw, hTtw, hDmem⟩ := hValid
  have hon : o.lab.n / lab.n = 1 → o.lab.n = lab.n := by
    intro hm
    have h := Nat.div_mul_cancel hdvd
    rw [hm] at h
    simpa using h.symm
  rcases htag with hE6 | hTw
  · have hTtw' : ggKacTypeOfLabel lab = some (.E6, false) := by
      obtain ⟨t, r, nn⟩ := lab
      simp only at hE6
      subst hE6
      rfl
    rw [hTtw'] at hTtw
    simp only [Option.some.injEq, Prod.mk.injEq] at hTtw
    obtain ⟨rfl, rfl⟩ := hTtw
    rcases ltqD4s_three_dvd lab.n with h3 | h3
    · have hshape := ggKacTable_shape .E6 false (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      have hdiv := ltqD4s_extract hshape hDmem ho htagD hrankD ltqD4s_fin_false2
      refine ⟨hon hdiv, fun _ => h3, ?_⟩
      intro htw
      rw [hE6] at htw
      exact absurd htw (by decide)
    · have hshape := ggKacTable_shape .E6 false (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      exact (ltqD4s_extract_false hshape hDmem ho htagD hrankD ltqD4s_fin_false1).elim
  · have hTtw' : ggKacTypeOfLabel lab = some (.E6, true) := by
      obtain ⟨t, r, nn⟩ := lab
      simp only at hTw
      subst hTw
      rfl
    rw [hTtw'] at hTtw
    simp only [Option.some.injEq, Prod.mk.injEq] at hTtw
    obtain ⟨rfl, rfl⟩ := hTtw
    rcases ltqD4s_three_dvd lab.n with h3 | h3
    · have hshape := ggKacTable_shape .E6 true (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      exact (ltqD4s_extract_false hshape hDmem ho htagD hrankD ltqD4s_fin_true2).elim
    · have hshape := ggKacTable_shape .E6 true (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      have hdiv := ltqD4s_extract hshape hDmem ho htagD hrankD ltqD4s_fin_true1
      refine ⟨hon hdiv, ?_, fun _ => h3⟩
      intro hE
      rw [hTw] at hE
      exact absurd hE (by decide)

private theorem ltqD4s_rig {labX : LargeEvenLabel} (htag : labX.tag = .E6 ∨ labX.tag = .twE6) :
    ∀ l : LargeEvenLabel, LargeEvenInLambda2 l → GGLabelIso labX l → l = labX := by
  intro l _ hiso
  obtain ⟨tx, rx, nx⟩ := labX
  obtain ⟨t, r, n⟩ := l
  rcases htag with h | h <;>
    (subst h
     unfold GGLabelIso at hiso
     rcases hiso with h | h | h | h | h | h | h | h <;> simp_all)

private theorem ltqD4s_iso_D4 {lab l : LargeEvenLabel} (htag : lab.tag = .D)
    (hrank : lab.rank = 4) (h : GGLabelIso lab l) : l = ⟨.D, 4, lab.n⟩ := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := l
  simp only at htag hrank
  subst htag
  subst hrank
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem ltqD4s_label_eq_D {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (hr : lab.rank = 4) : lab = ⟨.D, 4, lab.n⟩ := by
  obtain ⟨t, r, n⟩ := lab
  simp only at ht hr
  subst ht
  subst hr
  rfl

private theorem ltqD4s_label_eq_zero {lab : LargeEvenLabel} {t : LargeEvenLieTag} {n : ℕ}
    (ht : lab.tag = t) (hr : lab.rank = 0) (hn : lab.n = n) : lab = ⟨t, 0, n⟩ := by
  obtain ⟨t', r, n'⟩ := lab
  simp only at ht hr hn
  subst ht
  subst hr
  subst hn
  rfl

private theorem ltqD4s_rank_zero {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : lab.rank = 0 := by
  rcases htag with h | h
  · unfold LargeEvenInLambda2 at hΛ
    rw [h] at hΛ
    exact hΛ.2
  · unfold LargeEvenInLambda2 at hΛ
    rw [h] at hΛ
    exact hΛ.2

private theorem ltqD4s_row_E6 {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    GGTablePRow 3 ⟨.D, 4, n⟩ ⟨.E6, 0, n⟩ := by
  unfold GGTablePRow
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))))))))
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact h
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))

private theorem ltqD4s_row_twE6 {n : ℕ} (h : 3 ∣ 2 ^ n + 1) :
    GGTablePRow 3 ⟨.D, 4, n⟩ ⟨.twE6, 0, n⟩ := by
  unfold GGTablePRow
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))))))))
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact h
  · refine Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

theorem ggTablePKnownR_b36D4E6
    (hRE : GGK0CompRE) : GGTablePKnownR GGRegimeB36D4E6 := by
  intro p hp hp2 X _ _ A Ab σ J n hd labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hp3, htagJ, hrankJ, htagX⟩ := hr
  subst hp3
  have hcomp := ltqD4s_compList hRE hΛX htagX
  have hrig := ltqD4s_rig htagX
  obtain ⟨l, hSl, hlabel⟩ := GGCompList.of_basicB hcomp hΛX hrig hd.1 hhX
  obtain ⟨D, hValid, o, ho, hqs, hdvd, hΛo, hl⟩ := hSl
  have hΛl : LargeEvenInLambda2 l := hl.symm ▸ hΛo
  have hiso : GGLabelIso labJ l :=
    ggLabelRigidInput_holds labJ l (↥J ⧸ Subgroup.center ↥J) hΛJ hΛl hhJ hlabel
  have hD4 : l = ⟨.D, 4, labJ.n⟩ := ltqD4s_iso_D4 htagJ hrankJ hiso
  have hoD4 : o.lab = ⟨.D, 4, labJ.n⟩ := hl ▸ hD4
  have htagD : o.lab.tag = .D := by rw [hoD4]
  have hrankD : o.lab.rank = 4 := by rw [hoD4]
  have hon : o.lab.n = labJ.n := by rw [hoD4]
  obtain ⟨honX, hresE6, hresTw⟩ := ltqD4s_shape hΛX htagX hValid ho hqs htagD hrankD hdvd
  have hneq : labJ.n = labX.n := hon.symm.trans honX
  refine ⟨labJ, labX, hΛJ, hΛX, ?_, hhJ, hhX⟩
  rw [ltqD4s_label_eq_D htagJ hrankJ]
  have hrankX : labX.rank = 0 := ltqD4s_rank_zero hΛX htagX
  rcases htagX with hE6 | hTw
  · have hres : 3 ∣ 2 ^ labJ.n - 1 := by rw [hneq]; exact hresE6 hE6
    have hX : labX = ⟨.E6, 0, labJ.n⟩ := ltqD4s_label_eq_zero hE6 hrankX hneq.symm
    rw [hX]
    exact ltqD4s_row_E6 hres
  · have hres : 3 ∣ 2 ^ labJ.n + 1 := by rw [hneq]; exact hresTw hTw
    have hX : labX = ⟨.twE6, 0, labJ.n⟩ := ltqD4s_label_eq_zero hTw hrankX hneq.symm
    rw [hX]
    exact ltqD4s_row_twE6 hres

end CFSG.StandardType

end
