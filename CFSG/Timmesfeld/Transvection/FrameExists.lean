module

public import CFSG.Timmesfeld.Transvection.LineGroup
public import CFSG.Timmesfeld.Transvection.FrameBasic

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

structure IsMaxFrame (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H) : Prop
    extends IsFrame Δ P Q where
  maximal : ∀ X ∈ Δ, ¬ ∀ i, Commuting X (P i) ∧ Commuting X (Q i)

theorem IsSmallFrame.toIsMaxFrame [Finite H] (hΔ : IsTransvectionClass Δ) {r : ℕ}
    {P Q : Fin r → Subgroup H} {k : Fin r} (h : IsSmallFrame Δ P Q k) :
    IsMaxFrame Δ P Q where
  toIsFrame := h.toIsFrame
  maximal := by
    intro X hX hc
    have hle := h.residue X hX fun i _ => hc i
    obtain ⟨x, hx, hx1⟩ := hΔ.root.exists_ne_one hX
    have hcen : Commuting (P k ⊔ Q k) X := ((hc k).1.sup_right (hc k).2).symm
    exact hx1 (Opposite.eq_one_of_mem_centralizer (hΔ.root.mul_self _ (h.memP k)) (h.opposite k)
      (hle hx) (commuting_iff_le_centralizer.1 hcen hx))

private structure StepData {H : Type*} [Group H] (Δ : Set (Subgroup H)) {r : ℕ}
    (P Q : Fin r → Subgroup H) (X Z : Subgroup H) (i : Fin r) where
  p : Subgroup H
  q : Subgroup H
  mem_p : p ∈ Δ
  mem_q : q ∈ Δ
  opposite : Opposite p q
  commZ_p : Commuting Z p
  commZ_q : Commuting Z q
  commX_p : Commuting p X
  commX_q : Commuting q X
  rel_p : p = P i ∨ p = Q i ∨ p ∈ lineOf Δ (P i) X ∨ p ∈ lineOf Δ (Q i) X
  rel_q : q = P i ∨ q = Q i ∨ q ∈ lineOf Δ (P i) X ∨ q ∈ lineOf Δ (Q i) X

private theorem commuting_frame_of_mem_relation {H : Type*} [Group H] {Δ : Set (Subgroup H)}
    {r : ℕ} {P Q : Fin r → Subgroup H} {X : Subgroup H} (hF : IsFrame Δ P Q)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) {i j : Fin r} (hij : i ≠ j)
    {w : Subgroup H}
    (hw : w = P i ∨ w = Q i ∨ w ∈ lineOf Δ (P i) X ∨ w ∈ lineOf Δ (Q i) X) :
    Commuting w (P j) ∧ Commuting w (Q j) := by
  rcases hw with h | h | h | h
  · subst h
    exact ⟨hF.commuting_PP hij, hF.commuting_PQ hij⟩
  · subst h
    exact ⟨hF.commuting_QP hij, hF.commuting_QQ hij⟩
  · exact ⟨(h.2 (P j) (hF.memP j) (hF.commuting_PP hij).symm ((hXc j).1).symm).symm,
      (h.2 (Q j) (hF.memQ j) (hF.commuting_PQ hij).symm ((hXc j).2).symm).symm⟩
  · exact ⟨(h.2 (P j) (hF.memP j) (hF.commuting_QP hij).symm ((hXc j).1).symm).symm,
      (h.2 (Q j) (hF.memQ j) (hF.commuting_QQ hij).symm ((hXc j).2).symm).symm⟩

private theorem replacement_exists_of_commutes_both {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hF : IsFrame Δ P Q)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) {i : Fin r}
    (hboth : Commuting Z (P i) ∧ Commuting Z (Q i)) :
    Nonempty (StepData Δ P Q X Z i) :=
  ⟨⟨P i, Q i, hF.memP i, hF.memQ i, hF.opposite i, hboth.1, hboth.2,
    (hXc i).1.symm, (hXc i).2.symm, Or.inl rfl, Or.inr (Or.inl rfl)⟩⟩

private theorem replacement_exists_of_commutes_left [Finite H] {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hML : MeetsLines Δ) (hF : IsFrame Δ P Q) (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ)
    (hXZ : Opposite X Z) (i : Fin r) (hQiX : Q i ≠ X)
    (hP : Commuting Z (P i)) :
    Nonempty (StepData Δ P Q X Z i) := by
  obtain ⟨D, hDline, hZD⟩ := hML (Q i) (hF.memQ i) X hX hQiX ((hXc i).2).symm Z hZ
  have hQiD : Commuting (Q i) D :=
    (commuting_of_mem_lineOf' hΔ (hF.memQ i) hX ((hXc i).2).symm hDline).1
  have hXD : Commuting X D :=
    (commuting_of_mem_lineOf' hΔ (hF.memQ i) hX ((hXc i).2).symm hDline).2
  have hDnePi : D ≠ P i := by
    intro h
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) (h ▸ hQiD).symm
  have hDneX : D ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite hXZ (h ▸ hZD).symm
  have hnot : ¬ Commuting (P i) D := by
    intro hPD
    have hDlineX : D ∈ lineOf Δ X (Q i) := by rw [lineOf_comm]; exact hDline
    have heq : lineOf Δ X D = lineOf Δ X (Q i) :=
      lineOf_eq_of_mem_of_ne hΔ hpts hX (hF.memQ i) hQiX.symm (hXc i).2 hDlineX hDneX
    have hQi' : Q i ∈ lineOf Δ X D := heq ▸ right_mem_lineOf (hF.memQ i)
    exact ModelRank.not_commuting_of_opposite (hF.opposite i)
      (hQi'.2 (P i) (hF.memP i) (hXc i).1.symm hPD)
  have hopp : Opposite (P i) D := by
    rcases hΔ.commuting_or_opposite (hF.memP i) hDline.1 hDnePi.symm with hc | ho
    · exact absurd hc hnot
    · exact ho
  exact ⟨⟨P i, D, hF.memP i, hDline.1, hopp, hP, hZD, (hXc i).1.symm, hXD.symm,
    Or.inl rfl, Or.inr (Or.inr (Or.inr hDline))⟩⟩

private theorem replacement_exists_of_commutes_right [Finite H] {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hML : MeetsLines Δ) (hF : IsFrame Δ P Q) (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ)
    (hXZ : Opposite X Z) (i : Fin r) (hPiX : P i ≠ X)
    (hQ : Commuting Z (Q i)) :
    Nonempty (StepData Δ P Q X Z i) := by
  obtain ⟨D, hDline, hZD⟩ := hML (P i) (hF.memP i) X hX hPiX ((hXc i).1).symm Z hZ
  have hPiD : Commuting (P i) D :=
    (commuting_of_mem_lineOf' hΔ (hF.memP i) hX ((hXc i).1).symm hDline).1
  have hXD : Commuting X D :=
    (commuting_of_mem_lineOf' hΔ (hF.memP i) hX ((hXc i).1).symm hDline).2
  have hDneQi : D ≠ Q i := by
    intro h
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) (h ▸ hPiD)
  have hDneX : D ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite hXZ (h ▸ hZD).symm
  have hnot : ¬ Commuting D (Q i) := by
    intro hDQ
    have hDlineX : D ∈ lineOf Δ X (P i) := by rw [lineOf_comm]; exact hDline
    have heq : lineOf Δ X D = lineOf Δ X (P i) :=
      lineOf_eq_of_mem_of_ne hΔ hpts hX (hF.memP i) hPiX.symm (hXc i).1 hDlineX hDneX
    have hPi' : P i ∈ lineOf Δ X D := heq ▸ right_mem_lineOf (hF.memP i)
    have hcomm : Commuting (Q i) (P i) :=
      commuting_of_commuting_of_mem_lineOf hΔ hpts hX hDline.1 hDneX.symm hXD
        (left_mem_lineOf hX) (right_mem_lineOf hDline.1) hDneX.symm hPi'
        (hF.memQ i) (hXc i).2.symm hDQ.symm
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) hcomm.symm
  have hopp : Opposite D (Q i) := by
    rcases hΔ.commuting_or_opposite hDline.1 (hF.memQ i) hDneQi with hc | ho
    · exact absurd hc hnot
    · exact ho
  exact ⟨⟨D, Q i, hDline.1, hF.memQ i, hopp, hZD, hQ, hXD.symm, (hXc i).2.symm,
    Or.inr (Or.inr (Or.inl hDline)), Or.inr (Or.inl rfl)⟩⟩

private theorem replacement_exists_of_commutes_neither [Finite H] {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ)
    (hML : MeetsLines Δ) (hF : IsFrame Δ P Q) (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ)
    (hXZ : Opposite X Z) (i : Fin r) (hPiX : P i ≠ X) (hQiX : Q i ≠ X)
    (hP : ¬ Commuting Z (P i)) (hQ : ¬ Commuting Z (Q i)) :
    Nonempty (StepData Δ P Q X Z i) := by
  obtain ⟨D, hDline, hZD⟩ := hML (P i) (hF.memP i) X hX hPiX ((hXc i).1).symm Z hZ
  obtain ⟨D', hD'line, hZD'⟩ := hML (Q i) (hF.memQ i) X hX hQiX ((hXc i).2).symm Z hZ
  have hPiD : Commuting (P i) D :=
    (commuting_of_mem_lineOf' hΔ (hF.memP i) hX ((hXc i).1).symm hDline).1
  have hXD : Commuting X D :=
    (commuting_of_mem_lineOf' hΔ (hF.memP i) hX ((hXc i).1).symm hDline).2
  have hQiD' : Commuting (Q i) D' :=
    (commuting_of_mem_lineOf' hΔ (hF.memQ i) hX ((hXc i).2).symm hD'line).1
  have hXD' : Commuting X D' :=
    (commuting_of_mem_lineOf' hΔ (hF.memQ i) hX ((hXc i).2).symm hD'line).2
  have hDneX : D ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite hXZ (h ▸ hZD).symm
  have hD'neX : D' ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite hXZ (h ▸ hZD').symm
  have hDnePi : D ≠ P i := by
    intro h
    exact hP (h ▸ hZD)
  have hD'neQi : D' ≠ Q i := by
    intro h
    exact hQ (h ▸ hZD')
  have hnot : ¬ Commuting D D' := by
    intro hDD'
    have hDlineX : D ∈ lineOf Δ X (P i) := by rw [lineOf_comm]; exact hDline
    have heq : lineOf Δ X D = lineOf Δ X (P i) :=
      lineOf_eq_of_mem_of_ne hΔ hpts hX (hF.memP i) hPiX.symm (hXc i).1 hDlineX hDneX
    have hPi_line : P i ∈ lineOf Δ X D := heq ▸ right_mem_lineOf (hF.memP i)
    have hD'Pi : Commuting D' (P i) :=
      commuting_of_commuting_of_mem_lineOf hΔ hpts hX hDline.1 hDneX.symm hXD
        (left_mem_lineOf hX) (right_mem_lineOf hDline.1) hDneX.symm hPi_line
        hD'line.1 hXD'.symm hDD'.symm
    have hD'lineX : D' ∈ lineOf Δ X (Q i) := by rw [lineOf_comm]; exact hD'line
    have heq' : lineOf Δ X D' = lineOf Δ X (Q i) :=
      lineOf_eq_of_mem_of_ne hΔ hpts hX (hF.memQ i) hQiX.symm (hXc i).2 hD'lineX hD'neX
    have hQi_line : Q i ∈ lineOf Δ X D' := heq' ▸ right_mem_lineOf (hF.memQ i)
    have hPiQi : Commuting (P i) (Q i) :=
      commuting_of_commuting_of_mem_lineOf hΔ hpts hX hD'line.1 hD'neX.symm hXD'
        (left_mem_lineOf hX) (right_mem_lineOf hD'line.1) hD'neX.symm hQi_line
        (hF.memP i) (hXc i).1.symm hD'Pi.symm
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) hPiQi
  have hne : D ≠ D' := by
    rintro rfl
    exact hnot (hΔ.root.commuting_self hDline.1)
  have hopp : Opposite D D' := by
    rcases hΔ.commuting_or_opposite hDline.1 hD'line.1 hne with hc | ho
    · exact absurd hc hnot
    · exact ho
  exact ⟨⟨D, D', hDline.1, hD'line.1, hopp, hZD, hZD', hXD.symm, hXD'.symm,
    Or.inr (Or.inr (Or.inl hDline)), Or.inr (Or.inr (Or.inr hD'line))⟩⟩

private theorem step_exists [Finite H] {Δ : Set (Subgroup H)} {r : ℕ}
    {P Q : Fin r → Subgroup H} {X Z : Subgroup H} (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsFrame Δ P Q) (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ) (hXZ : Opposite X Z)
    (i : Fin r) : Nonempty (StepData Δ P Q X Z i) := by
  have hPiX : P i ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) (h ▸ (hXc i).2)
  have hQiX : Q i ≠ X := by
    intro h
    exact ModelRank.not_commuting_of_opposite (hF.opposite i) ((h ▸ (hXc i).1).symm)
  by_cases hboth : Commuting Z (P i) ∧ Commuting Z (Q i)
  · exact replacement_exists_of_commutes_both hF hXc hboth
  · by_cases hP : Commuting Z (P i)
    · exact replacement_exists_of_commutes_left hΔ hpts hML hF hX hXc hZ hXZ i hQiX hP
    · by_cases hQ : Commuting Z (Q i)
      · exact replacement_exists_of_commutes_right hΔ hpts hML hF hX hXc hZ hXZ i hPiX hQ
      · exact replacement_exists_of_commutes_neither hΔ hpts hML hF hX hXc hZ hXZ i hPiX
          hQiX hP hQ

private theorem replacement_pairs_commute {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hF : IsFrame Δ P Q)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i))
    (step : (i : Fin r) → StepData Δ P Q X Z i) :
    ∀ i j : Fin r, i ≠ j →
      Commuting (step i).p (step j).p ∧ Commuting (step i).p (step j).q ∧
        Commuting (step i).q (step j).p ∧ Commuting (step i).q (step j).q := by
  intro i j hij
  have hframe_comm : ∀ (i k : Fin r), k ≠ i →
      Commuting (step i).p (P k) ∧ Commuting (step i).p (Q k) ∧
        Commuting (step i).q (P k) ∧ Commuting (step i).q (Q k) := by
    intro i k hk
    have hp := commuting_frame_of_mem_relation hF hXc hk.symm (step i).rel_p
    have hq := commuting_frame_of_mem_relation hF hXc hk.symm (step i).rel_q
    exact ⟨hp.1, hp.2, hq.1, hq.2⟩
  have hf := hframe_comm i j hij.symm
  have key : ∀ w : Subgroup H, w ∈ Δ → Commuting w X → Commuting w (P j) →
      Commuting w (Q j) → Commuting w (step j).p ∧ Commuting w (step j).q := by
    intro w hw hwX hwPj hwQj
    have keyp : Commuting w (step j).p := by
      rcases (step j).rel_p with h | h | h | h
      · rw [h]; exact hwPj
      · rw [h]; exact hwQj
      · exact h.2 w hw hwPj hwX
      · exact h.2 w hw hwQj hwX
    have keyq : Commuting w (step j).q := by
      rcases (step j).rel_q with h | h | h | h
      · rw [h]; exact hwPj
      · rw [h]; exact hwQj
      · exact h.2 w hw hwPj hwX
      · exact h.2 w hw hwQj hwX
    exact ⟨keyp, keyq⟩
  have h1 := key (step i).p (step i).mem_p (step i).commX_p hf.1 hf.2.1
  have h2 := key (step i).q (step i).mem_q (step i).commX_q hf.2.2.1 hf.2.2.2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

private theorem exists_frame_succ_of_replacement {r : ℕ} {P Q : Fin r → Subgroup H}
    {X Z : Subgroup H} (hX : X ∈ Δ) (hZ : Z ∈ Δ) (hXZ : Opposite X Z)
    (step : (i : Fin r) → StepData Δ P Q X Z i)
    (hpt_comm : ∀ i j : Fin r, i ≠ j →
      Commuting (step i).p (step j).p ∧ Commuting (step i).p (step j).q ∧
        Commuting (step i).q (step j).p ∧ Commuting (step i).q (step j).q) :
    ∃ P' Q' : Fin (r + 1) → Subgroup H,
      IsFrame Δ P' Q' ∧ P' (Fin.last r) = X ∧ Q' (Fin.last r) = Z := by
  classical
  let P' : Fin (r + 1) → Subgroup H :=
    fun i => if h : (i : ℕ) < r then (step ⟨i, h⟩).p else X
  let Q' : Fin (r + 1) → Subgroup H :=
    fun i => if h : (i : ℕ) < r then (step ⟨i, h⟩).q else Z
  have hP'_cast : ∀ k : Fin r, P' k.castSucc = (step k).p := fun k => by simp [P', k.isLt]
  have hQ'_cast : ∀ k : Fin r, Q' k.castSucc = (step k).q := fun k => by simp [Q', k.isLt]
  have hP'_last : P' (Fin.last r) = X := by simp [P', Fin.last]
  have hQ'_last : Q' (Fin.last r) = Z := by simp [Q', Fin.last]
  have hXp : ∀ k : Fin r, Commuting X (step k).p := fun k => (step k).commX_p.symm
  have hXq : ∀ k : Fin r, Commuting X (step k).q := fun k => (step k).commX_q.symm
  have hZp : ∀ k : Fin r, Commuting Z (step k).p := fun k => (step k).commZ_p
  have hZq : ∀ k : Fin r, Commuting Z (step k).q := fun k => (step k).commZ_q
  refine ⟨P', Q', ?_, hP'_last, hQ'_last⟩
  refine { memP := ?_, memQ := ?_, opposite := ?_, commuting := ?_ }
  · intro i
    refine Fin.lastCases (motive := fun i => P' i ∈ Δ) ?_ ?_ i
    · rw [hP'_last]; exact hX
    · intro k; rw [hP'_cast k]; exact (step k).mem_p
  · intro i
    refine Fin.lastCases (motive := fun i => Q' i ∈ Δ) ?_ ?_ i
    · rw [hQ'_last]; exact hZ
    · intro k; rw [hQ'_cast k]; exact (step k).mem_q
  · intro i
    refine Fin.lastCases (motive := fun i => Opposite (P' i) (Q' i)) ?_ ?_ i
    · rw [hP'_last, hQ'_last]; exact hXZ
    · intro k; rw [hP'_cast k, hQ'_cast k]; exact (step k).opposite
  · intro i j hij
    refine Fin.lastCases (motive := fun i => i ≠ j →
      Commuting (P' i ⊔ Q' i) (P' j ⊔ Q' j)) ?_ ?_ i hij
    · intro hlast
      have hjlast : j ≠ Fin.last r := fun h => hlast h.symm
      obtain ⟨l, rfl⟩ : ∃ l : Fin r, j = l.castSucc :=
        ⟨j.castPred hjlast, (Fin.castSucc_castPred j hjlast).symm⟩
      rw [hP'_last, hQ'_last, hP'_cast l, hQ'_cast l]
      exact Commuting.sup_left ((hXp l).sup_right (hXq l)) ((hZp l).sup_right (hZq l))
    · intro k hk
      by_cases hjlast : j = Fin.last r
      · subst hjlast
        rw [hP'_cast k, hQ'_cast k, hP'_last, hQ'_last]
        exact Commuting.sup_left ((hXp k).symm.sup_right (hZp k).symm)
          ((hXq k).symm.sup_right (hZq k).symm)
      · obtain ⟨l, rfl⟩ : ∃ l : Fin r, j = l.castSucc :=
          ⟨j.castPred hjlast, (Fin.castSucc_castPred j hjlast).symm⟩
        have hkl : k ≠ l := fun h => hk (by rw [h])
        rw [hP'_cast k, hQ'_cast k, hP'_cast l, hQ'_cast l]
        have h4 := hpt_comm k l hkl
        exact Commuting.sup_left (h4.1.sup_right h4.2.1)
          (h4.2.2.1.sup_right h4.2.2.2)

theorem IsFrame.exists_succ_last [Finite H] {Δ : Set (Subgroup H)} (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) {r : ℕ} {P Q : Fin r → Subgroup H}
    (hF : IsFrame Δ P Q) {X Z : Subgroup H} (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ) (hXZ : Opposite X Z) :
    ∃ P' Q' : Fin (r + 1) → Subgroup H,
      IsFrame Δ P' Q' ∧ P' (Fin.last r) = X ∧ Q' (Fin.last r) = Z := by
  classical
  let step : (i : Fin r) → StepData Δ P Q X Z i :=
    fun i => Classical.choice (step_exists hΔ hpts hML hF hX hXc hZ hXZ i)
  exact exists_frame_succ_of_replacement hX hZ hXZ step
    (replacement_pairs_commute hF hXc step)

theorem IsFrame.exists_succ [Finite H] {Δ : Set (Subgroup H)} (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) {r : ℕ} {P Q : Fin r → Subgroup H}
    (hF : IsFrame Δ P Q) {X Z : Subgroup H} (hX : X ∈ Δ)
    (hXc : ∀ i, Commuting X (P i) ∧ Commuting X (Q i)) (hZ : Z ∈ Δ) (hXZ : Opposite X Z) :
    ∃ P' Q' : Fin (r + 1) → Subgroup H, IsFrame Δ P' Q' := by
  obtain ⟨P', Q', hF', -⟩ := hF.exists_succ_last hΔ hpts hML hX hXc hZ hXZ
  exact ⟨P', Q', hF'⟩

theorem exists_isMaxFrame (h : TransvectionHyp H Δ) (hML : MeetsLines Δ) :
    ∃ r, 2 ≤ r ∧ ∃ P Q : Fin r → Subgroup H, IsMaxFrame Δ P Q := by
  classical
  haveI := h.finite
  have hΔ := h.cls
  have hiso : NoIsolated Δ := hΔ.noIsolated h.points h.rank
  obtain ⟨A, hA, B, hB, hAB, hcAB⟩ := h.rank
  obtain ⟨W, hW, hAW⟩ := hiso A hA
  obtain ⟨D, hDline, hWD⟩ := hML A hA B hB hAB hcAB W hW
  have hAD : Commuting A D := (commuting_of_mem_lineOf' hΔ hA hB hcAB hDline).1
  obtain ⟨Z, hZ, hDZ⟩ := hiso D hDline.1
  let P₁ : Fin 1 → Subgroup H := fun _ => A
  let Q₁ : Fin 1 → Subgroup H := fun _ => W
  have hF₁ : IsFrame Δ P₁ Q₁ :=
    { memP := fun _ => hA
      memQ := fun _ => hW
      opposite := fun _ => hAW
      commuting := fun i j hij => absurd (Subsingleton.elim i j) hij }
  have hXc₁ : ∀ i : Fin 1, Commuting D (P₁ i) ∧ Commuting D (Q₁ i) :=
    fun _ => ⟨hAD.symm, hWD.symm⟩
  obtain ⟨P₂, Q₂, hF₂⟩ := hF₁.exists_succ hΔ h.points hML hDline.1 hXc₁ hZ hDZ
  have hframe_card_le : ∀ n, (∃ P Q : Fin n → Subgroup H, IsFrame Δ P Q) →
      n ≤ Nat.card (Subgroup H) := by
    intro n hFn
    obtain ⟨P, Q, hF⟩ := hFn
    have hinj : Function.Injective P := by
      intro i j hij
      by_contra hne
      have hcomm : Commuting (P j) (Q i) :=
        (hF.commuting j i (Ne.symm hne)).mono le_sup_left le_sup_right
      rw [← hij] at hcomm
      exact ModelRank.not_commuting_of_opposite (hF.opposite i) hcomm
    have hcard := Nat.card_le_card_of_injective P hinj
    simpa using hcard
  have key : ∀ k, ∀ r, r ≤ Nat.card (Subgroup H) + 2 → Nat.card (Subgroup H) + 2 - r = k →
      (∃ P Q : Fin r → Subgroup H, IsFrame Δ P Q) →
      ∃ r' : ℕ, ∃ P Q : Fin r' → Subgroup H, r ≤ r' ∧ IsMaxFrame Δ P Q := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro r hr hk hFr
      obtain ⟨P, Q, hF⟩ := hFr
      by_cases hmax : ∀ X ∈ Δ, ¬ ∀ i, Commuting X (P i) ∧ Commuting X (Q i)
      · exact ⟨r, P, Q, le_rfl, { toIsFrame := hF, maximal := hmax }⟩
      · push Not at hmax
        obtain ⟨X, hX, hXc⟩ := hmax
        obtain ⟨Z', hZ', hXZ'⟩ := hiso X hX
        obtain ⟨P', Q', hF'⟩ := hF.exists_succ hΔ h.points hML hX hXc hZ' hXZ'
        have hr' : r + 1 ≤ Nat.card (Subgroup H) := hframe_card_le (r + 1) ⟨P', Q', hF'⟩
        obtain ⟨r'', P'', Q'', hr'', hmax''⟩ :=
          ih (Nat.card (Subgroup H) + 2 - (r + 1)) (by omega) (r + 1) (by omega) rfl
            ⟨P', Q', hF'⟩
        exact ⟨r'', P'', Q'', by omega, hmax''⟩
  obtain ⟨r, P, Q, hr, hmax⟩ :=
    key (Nat.card (Subgroup H) + 2 - 2) 2 (by omega) rfl ⟨P₂, Q₂, hF₂⟩
  exact ⟨r, hr, P, Q, hmax⟩

theorem IsMaxFrame.opposite_of_mem_residue (hΔ : IsTransvectionClass Δ) (hML : MeetsLines Δ)
    {r : ℕ} {P Q : Fin r → Subgroup H} (hF : IsMaxFrame Δ P Q) (k : Fin r) {X Y : Subgroup H}
    (hX : X ∈ Δ) (hY : Y ∈ Δ) (hXk : ∀ i, i ≠ k → Commuting X (P i) ∧ Commuting X (Q i))
    (hYk : ∀ i, i ≠ k → Commuting Y (P i) ∧ Commuting Y (Q i)) (hXY : X ≠ Y) : Opposite X Y := by
  rcases hΔ.commuting_or_opposite hX hY hXY with hc | ho
  · exfalso
    have hres : ∀ Z ∈ lineOf Δ X Y, ∀ i, i ≠ k → Commuting Z (P i) ∧ Commuting Z (Q i) := by
      intro Z hZ i hi
      exact ⟨(hZ.2 (P i) (hF.memP i) ((hXk i hi).1).symm ((hYk i hi).1).symm).symm,
        (hZ.2 (Q i) (hF.memQ i) ((hXk i hi).2).symm ((hYk i hi).2).symm).symm⟩
    have hcontra : ∀ Z ∈ Δ, (∀ i, i ≠ k → Commuting Z (P i) ∧ Commuting Z (Q i)) →
        Commuting Z (P k) → Commuting Z (Q k) → False := by
      intro Z hZ hZres hZP hZQ
      exact hF.maximal Z hZ fun i => by
        by_cases hik : i = k
        · subst hik; exact ⟨hZP, hZQ⟩
        · exact hZres i hik
    obtain ⟨Dp, hDp_line, hDpPk⟩ := hML X hX Y hY hXY hc (P k) (hF.memP k)
    by_cases hDp : Dp = P k
    ·
      obtain ⟨Dq, hDq_line, hDqQk⟩ := hML X hX Y hY hXY hc (Q k) (hF.memQ k)
      by_cases hDq : Dq = Q k
      ·
        exact ModelRank.not_commuting_of_opposite (hF.opposite k)
          (commuting_of_mem_lineOf_of_mem_lineOf hΔ hX hY hc
            (hDp ▸ hDp_line) (hDq ▸ hDq_line))
      ·
        have hDqPk : ¬ Commuting Dq (P k) := by
          intro hP
          exact hcontra Dq hDq_line.1 (hres Dq hDq_line) hP hDqQk.symm
        have hres3 : ∀ Z ∈ lineOf Δ Dq (Q k), ∀ i, i ≠ k →
            Commuting Z (P i) ∧ Commuting Z (Q i) := by
          intro Z hZ i hi
          exact ⟨(hZ.2 (P i) (hF.memP i) ((hres Dq hDq_line i hi).1).symm
              (hF.commuting_PQ hi)).symm,
            (hZ.2 (Q i) (hF.memQ i) ((hres Dq hDq_line i hi).2).symm
              (hF.commuting_QQ hi)).symm⟩
        obtain ⟨E, hE_line, hEPk⟩ :=
          hML Dq hDq_line.1 (Q k) (hF.memQ k) hDq hDqQk.symm (P k) (hF.memP k)
        have hEQk : Commuting E (Q k) :=
          (commuting_of_mem_lineOf' hΔ hDq_line.1 (hF.memQ k) hDqQk.symm hE_line).2.symm
        exact hcontra E hE_line.1 (hres3 E hE_line) hEPk.symm hEQk
    ·
      have hres2 : ∀ Z ∈ lineOf Δ Dp (P k), ∀ i, i ≠ k →
          Commuting Z (P i) ∧ Commuting Z (Q i) := by
        intro Z hZ i hi
        exact ⟨(hZ.2 (P i) (hF.memP i) ((hres Dp hDp_line i hi).1).symm
            (hF.commuting_PP hi)).symm,
          (hZ.2 (Q i) (hF.memQ i) ((hres Dp hDp_line i hi).2).symm
            (hF.commuting_QP hi)).symm⟩
      obtain ⟨E, hE_line, hEQk⟩ :=
        hML Dp hDp_line.1 (P k) (hF.memP k) hDp hDpPk.symm (Q k) (hF.memQ k)
      have hEPk : Commuting E (P k) :=
        (commuting_of_mem_lineOf' hΔ hDp_line.1 (hF.memP k) hDpPk.symm hE_line).2.symm
      exact hcontra E hE_line.1 (hres2 E hE_line) hEPk hEQk.symm
  · exact ho

end CFSG.Timmesfeld.Transvection
