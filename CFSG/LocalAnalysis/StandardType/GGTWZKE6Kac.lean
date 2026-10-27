module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRowCover1585Holds
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltrcov_checks_false2 :
    ∀ s ∈ ltrcov_shapes false 2,
      (((s.1 = .A ∨ s.1 = .twA) → ¬ 3 ∣ s.2.1 + 3) ∧
        (s.1 = .D → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 2)) := by decide

private theorem ltrcov_checks_false1 :
    ∀ s ∈ ltrcov_shapes false 1,
      (((s.1 = .A ∨ s.1 = .twA) → ¬ 3 ∣ s.2.1 + 3) ∧
        (s.1 = .D → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 2)) := by decide

private theorem ltrcov_checks_true2 :
    ∀ s ∈ ltrcov_shapes true 2,
      (((s.1 = .A ∨ s.1 = .twA) → ¬ 3 ∣ s.2.1 + 3) ∧
        (s.1 = .D → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 2)) := by decide

private theorem ltrcov_checks_true1 :
    ∀ s ∈ ltrcov_shapes true 1,
      (((s.1 = .A ∨ s.1 = .twA) → ¬ 3 ∣ s.2.1 + 3) ∧
        (s.1 = .D → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 2)) := by decide

private theorem shape_facts_of_mem {n : ℕ} {o : GGKacOrbit}
    {shapes : List (LargeEvenLieTag × ℕ × ℕ)}
    (hcheck : ∀ s ∈ shapes,
      (((s.1 = .A ∨ s.1 = .twA) → ¬ 3 ∣ s.2.1 + 3) ∧
        (s.1 = .D → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 3) ∧
        (s.1 = .twD → s.2.1 ≠ 2)))
    (hmem : ggKacShapeLabel n o.lab ∈ shapes) :
    (((o.lab.tag = .A ∨ o.lab.tag = .twA) → ¬ 3 ∣ o.lab.rank + 3) ∧
      (o.lab.tag = .D → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 2)) := by
  rcases o with ⟨⟨tag, r, nn⟩, q⟩
  have h := hcheck _ hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro (rfl | rfl)
    · have h' := h.1 (by simp [ggKacShapeLabel])
      simpa [ggKacShapeLabel] using h'
    · have h' := h.1 (by simp [ggKacShapeLabel])
      simpa [ggKacShapeLabel] using h'
  · intro htag
    subst htag
    have h' := h.2.1 (by simp [ggKacShapeLabel])
    simpa [ggKacShapeLabel] using h'
  · intro htag
    subst htag
    have h' := h.2.2.1 (by simp [ggKacShapeLabel])
    simpa [ggKacShapeLabel] using h'
  · intro htag
    subst htag
    have h' := h.2.2.2 (by simp [ggKacShapeLabel])
    simpa [ggKacShapeLabel] using h'

private theorem E6_orbit_facts {tw : Bool} {n : ℕ} (hn : 1 ≤ n)
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n) {o : GGKacOrbit}
    (ho : o ∈ D.orbits) :
    (((o.lab.tag = .A ∨ o.lab.tag = .twA) → ¬ 3 ∣ o.lab.rank + 3) ∧
      (o.lab.tag = .D → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 2)) := by
  rcases tw with _ | _
  · rcases ltrcov_three_dvd n with hminus | hplus
    · have hshape := ggKacTable_shape .E6 false (p := 3) (n := n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨hminus, by norm_num⟩)
      obtain ⟨D', hD', o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
      have hmem : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 2 := by
        rw [heqo]; exact ltrcov_shapes_false2 D' hD' o' ho'
      exact shape_facts_of_mem ltrcov_checks_false2 hmem
    · have hshape := ggKacTable_shape .E6 false (p := 3) (n := n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨hplus, by norm_num⟩)
      obtain ⟨D', hD', o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
      have hmem : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 1 := by
        rw [heqo]; exact ltrcov_shapes_false1 D' hD' o' ho'
      exact shape_facts_of_mem ltrcov_checks_false1 hmem
  · rcases ltrcov_three_dvd n with hminus | hplus
    · have hshape := ggKacTable_shape .E6 true (p := 3) (n := n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨hminus, by norm_num⟩)
      obtain ⟨D', hD', o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
      have hmem : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 2 := by
        rw [heqo]; exact ltrcov_shapes_true2 D' hD' o' ho'
      exact shape_facts_of_mem ltrcov_checks_true2 hmem
    · have hshape := ggKacTable_shape .E6 true (p := 3) (n := n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨hplus, by norm_num⟩)
      obtain ⟨D', hD', o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
      have hmem : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 1 := by
        rw [heqo]; exact ltrcov_shapes_true1 D' hD' o' ho'
      exact shape_facts_of_mem ltrcov_checks_true1 hmem

theorem ggKacTable_E6_rank_not_dvd_three {tw : Bool} {n : ℕ} (hn : 1 ≤ n)
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n) {o : GGKacOrbit}
    (ho : o ∈ D.orbits) (htag : o.lab.tag = .A ∨ o.lab.tag = .twA) :
    ¬ 3 ∣ o.lab.rank + 3 :=
  (E6_orbit_facts hn hD ho).1 htag

theorem ggKacTable_E6_small_D {tw : Bool} {n : ℕ} (hn : 1 ≤ n)
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n) {o : GGKacOrbit}
    (ho : o ∈ D.orbits) :
    (o.lab.tag = .D → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 3) ∧
      (o.lab.tag = .twD → o.lab.rank ≠ 2) :=
  ⟨(E6_orbit_facts hn hD ho).2.1, (E6_orbit_facts hn hD ho).2.2.1,
    (E6_orbit_facts hn hD ho).2.2.2⟩

private theorem eq_of_ggLabelIso_of_tagA {lab lab' : LargeEvenLabel}
    (htag : lab.tag = .A ∨ lab.tag = .twA)
    (hD3 : lab'.tag = .D → lab'.rank ≠ 3)
    (hTwD3 : lab'.tag = .twD → lab'.rank ≠ 3)
    (hTwD2 : lab'.tag = .twD → lab'.rank ≠ 2)
    (hiso : GGLabelIso lab lab') : lab = lab' := by
  rcases lab with ⟨t, r, f⟩
  rcases lab' with ⟨t', r', f'⟩
  change t = .A ∨ t = .twA at htag
  rcases htag with ht | ht
  · subst t
    simp only [GGLabelIso] at hiso
    rcases hiso with he | h | h | h | h | h | h | h <;> simp_all
  · subst t
    simp only [GGLabelIso] at hiso
    rcases hiso with he | h | h | h | h | h | h | h <;> simp_all

theorem ggTWZKE6Kac_false {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (_hH : GGResHyp 3 B Bs x L D J y K)
    {labJ labK : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hKΛ : LargeEvenInLambda2 labK)
    (hJHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hKtag : labK.tag = .E6 ∨ labK.tag = .twE6)
    (hpJ : 3 ∣ labJ.rank + 3)
    {Dk : GGKacDatum} (hDk : GGKacValid labK 3 Dk)
    {o : GGKacOrbit} (ho : o ∈ Dk.orbits)
    (hoΛ : LargeEvenInLambda2 o.lab)
    (hoHas : GGHasLabel o.lab (J ⧸ Subgroup.center J))
    (hRig : GGLabelRigidInput) :
    False := by
  classical
  obtain ⟨T, tw, hT, hDmem⟩ := hDk
  rcases labK with ⟨tagK, rK, nK⟩
  rcases hKtag with hK | hK
  · subst hK
    simp only [ggKacTypeOfLabel] at hT
    cases hT
    have hn : 1 ≤ nK := hKΛ.1
    have hsmall := ggKacTable_E6_small_D (n := nK) hn hDmem ho
    have hiso := hRig labJ o.lab (J ⧸ Subgroup.center J) hJΛ hoΛ hJHas hoHas
    have hEq : labJ = o.lab :=
      eq_of_ggLabelIso_of_tagA hJtag hsmall.1 hsmall.2.1 hsmall.2.2 hiso
    have hnot := ggKacTable_E6_rank_not_dvd_three (n := nK) hn hDmem ho
    have htagO : o.lab.tag = .A ∨ o.lab.tag = .twA := by simpa [hEq] using hJtag
    have hpO : 3 ∣ o.lab.rank + 3 := by simpa [hEq] using hpJ
    exact (hnot htagO) hpO
  · subst hK
    simp only [ggKacTypeOfLabel] at hT
    cases hT
    have hn : 1 ≤ nK := hKΛ.1
    have hsmall := ggKacTable_E6_small_D (n := nK) hn hDmem ho
    have hiso := hRig labJ o.lab (J ⧸ Subgroup.center J) hJΛ hoΛ hJHas hoHas
    have hEq : labJ = o.lab :=
      eq_of_ggLabelIso_of_tagA hJtag hsmall.1 hsmall.2.1 hsmall.2.2 hiso
    have hnot := ggKacTable_E6_rank_not_dvd_three (n := nK) hn hDmem ho
    have htagO : o.lab.tag = .A ∨ o.lab.tag = .twA := by simpa [hEq] using hJtag
    have hpO : 3 ∣ o.lab.rank + 3 := by simpa [hEq] using hpJ
    exact (hnot htagO) hpO

end CFSG.StandardType

end
