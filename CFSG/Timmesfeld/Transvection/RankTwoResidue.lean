module

public import CFSG.Timmesfeld.Transvection.FrameResidue

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H] {Δ : Set (Subgroup H)}

@[expose] def rankTwoResidue (Δ : Set (Subgroup H)) {r : ℕ} (P Q : Fin r → Subgroup H)
    (j k : Fin r) : Set (Subgroup H) :=
  {X | X ∈ Δ ∧ ∀ i, i ≠ j → i ≠ k → Commuting X (P i) ∧ Commuting X (Q i)}

variable {r : ℕ} {P Q : Fin r → Subgroup H}

theorem frameResidue_subset_rankTwoResidue_left (j k : Fin r) :
    frameResidue Δ P Q j ⊆ rankTwoResidue Δ P Q j k :=
  fun _ hX => ⟨hX.1, fun i hij _ => hX.2 i hij⟩

theorem frameResidue_subset_rankTwoResidue_right (j k : Fin r) :
    frameResidue Δ P Q k ⊆ rankTwoResidue Δ P Q j k :=
  fun _ hX => ⟨hX.1, fun i _ hik => hX.2 i hik⟩

theorem mem_frameResidue_of_mem_rankTwoResidue_left {j k : Fin r} {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hP : Commuting X (P k)) (hQ : Commuting X (Q k)) :
    X ∈ frameResidue Δ P Q j :=
  ⟨hX.1, fun i hij => by
    by_cases hik : i = k
    · rw [hik]
      exact ⟨hP, hQ⟩
    · exact hX.2 i hij hik⟩

theorem mem_frameResidue_of_mem_rankTwoResidue_right {j k : Fin r} {X : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hP : Commuting X (P j)) (hQ : Commuting X (Q j)) :
    X ∈ frameResidue Δ P Q k :=
  ⟨hX.1, fun i hik => by
    by_cases hij : i = j
    · rw [hij]
      exact ⟨hP, hQ⟩
    · exact hX.2 i hij hik⟩

theorem IsFrame.memP_rankTwoResidue_left (hF : IsFrame Δ P Q) (j k : Fin r) :
    P j ∈ rankTwoResidue Δ P Q j k :=
  frameResidue_subset_rankTwoResidue_left (Δ := Δ) (P := P) (Q := Q) j k
    (hF.memP_frameResidue j)

theorem IsFrame.memQ_rankTwoResidue_left (hF : IsFrame Δ P Q) (j k : Fin r) :
    Q j ∈ rankTwoResidue Δ P Q j k :=
  frameResidue_subset_rankTwoResidue_left (Δ := Δ) (P := P) (Q := Q) j k
    (hF.memQ_frameResidue j)

theorem IsFrame.memP_rankTwoResidue_right (hF : IsFrame Δ P Q) (j k : Fin r) :
    P k ∈ rankTwoResidue Δ P Q j k :=
  frameResidue_subset_rankTwoResidue_right (Δ := Δ) (P := P) (Q := Q) j k
    (hF.memP_frameResidue k)

theorem IsFrame.memQ_rankTwoResidue_right (hF : IsFrame Δ P Q) (j k : Fin r) :
    Q k ∈ rankTwoResidue Δ P Q j k :=
  frameResidue_subset_rankTwoResidue_right (Δ := Δ) (P := P) (Q := Q) j k
    (hF.memQ_frameResidue k)

theorem IsFrame.lineOf_subset_rankTwoResidue (hF : IsFrame Δ P Q) {j k : Fin r}
    {X Y : Subgroup H} (hX : X ∈ rankTwoResidue Δ P Q j k)
    (hY : Y ∈ rankTwoResidue Δ P Q j k) :
    lineOf Δ X Y ⊆ rankTwoResidue Δ P Q j k := by
  intro D hD
  refine ⟨hD.1, fun i hij hik => ⟨?_, ?_⟩⟩
  · exact (hD.2 (P i) (hF.memP i) (hX.2 i hij hik).1.symm (hY.2 i hij hik).1.symm).symm
  · exact (hD.2 (Q i) (hF.memQ i) (hX.2 i hij hik).2.symm (hY.2 i hij hik).2.symm).symm

theorem IsFrame.mem_frameResidue_of_mem_lineOf (hF : IsFrame Δ P Q) (hΔ : IsTransvectionClass Δ)
    {j k : Fin r} {X Y : Subgroup H} (hX : X ∈ rankTwoResidue Δ P Q j k)
    (hcX : Commuting (P k) X) (hY : Y ∈ lineOf Δ (P k) X) (hYQ : Commuting Y (Q k)) :
    Y ∈ frameResidue Δ P Q j :=
  mem_frameResidue_of_mem_rankTwoResidue_left
    (hF.lineOf_subset_rankTwoResidue (hF.memP_rankTwoResidue_right j k) hX hY)
    (commuting_of_mem_lineOf' hΔ (hF.memP k) hX.1 hcX hY).1.symm hYQ

theorem IsMaxFrame.false_of_lineOf_ne [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    {X₁ X₂ : Subgroup H} (hX₁ : X₁ ∈ rankTwoResidue Δ P Q j k)
    (hX₂ : X₂ ∈ rankTwoResidue Δ P Q j k) (hX₁k : X₁ ≠ P k) (hX₂k : X₂ ≠ P k)
    (hc₁ : Commuting (P k) X₁) (hc₂ : Commuting (P k) X₂) (hc : Commuting X₁ X₂)
    (hne : lineOf Δ (P k) X₁ ≠ lineOf Δ (P k) X₂) : False := by
  obtain ⟨Y₁, hY₁, hY₁Q⟩ :=
    hML (P k) (hF.memP k) X₁ hX₁.1 (Ne.symm hX₁k) hc₁ (Q k) (hF.memQ k)
  obtain ⟨Y₂, hY₂, hY₂Q⟩ :=
    hML (P k) (hF.memP k) X₂ hX₂.1 (Ne.symm hX₂k) hc₂ (Q k) (hF.memQ k)
  have hR₁ := hF.toIsFrame.mem_frameResidue_of_mem_lineOf hΔ hX₁ hc₁ hY₁ hY₁Q.symm
  have hR₂ := hF.toIsFrame.mem_frameResidue_of_mem_lineOf hΔ hX₂ hc₂ hY₂ hY₂Q.symm
  have hPY₁ := (commuting_of_mem_lineOf' hΔ (hF.memP k) hX₁.1 hc₁ hY₁).1
  have hY₁k : Y₁ ≠ P k := fun e =>
    ModelRank.not_commuting_of_opposite (hF.opposite k) (by rw [← e]; exact hY₁Q.symm)
  have hY₂k : Y₂ ≠ P k := fun e =>
    ModelRank.not_commuting_of_opposite (hF.opposite k) (by rw [← e]; exact hY₂Q.symm)
  have hY₁₂ : Y₁ ≠ Y₂ := by
    intro e
    have h1 := lineOf_eq_of_mem_of_ne hΔ hpts (hF.memP k) hX₁.1 (Ne.symm hX₁k) hc₁ hY₁ hY₁k
    have h2 := lineOf_eq_of_mem_of_ne hΔ hpts (hF.memP k) hX₂.1 (Ne.symm hX₂k) hc₂ hY₂ hY₂k
    rw [e] at h1
    exact hne (h1.symm.trans h2)
  have hX₂Y₁ : Commuting X₂ Y₁ := hY₁.2 X₂ hX₂.1 hc₂.symm hc.symm
  have hY₁Y₂ : Commuting Y₁ Y₂ := hY₂.2 Y₁ hY₁.1 hPY₁.symm hX₂Y₁.symm
  exact ModelRank.not_commuting_of_opposite
    (hF.opposite_of_mem_frameResidue hΔ hML hR₁ hR₂ hY₁₂) hY₁Y₂

private theorem IsMaxFrame.not_forall_commuting_of_not_mem [Finite H]
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} {X Y : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k)
    (hXY : X ≠ Y) (hcXY : Commuting X Y) (hPk : P k ∉ lineOf Δ X Y) :
    ¬ ∀ D ∈ lineOf Δ X Y, Commuting (P k) D := by
  intro hall
  have hXk : X ≠ P k := fun h => hPk (by rw [← h]; exact left_mem_lineOf hX.1)
  have hYk : Y ≠ P k := fun h => hPk (by rw [← h]; exact right_mem_lineOf hY.1)
  refine hF.false_of_lineOf_ne hΔ hpts hML hX hY hXk hYk
    (hall X (left_mem_lineOf hX.1)) (hall Y (right_mem_lineOf hY.1)) hcXY ?_
  intro heq
  have hYl : Y ∈ lineOf Δ (P k) X := by rw [heq]; exact right_mem_lineOf hY.1
  have hl := lineOf_eq_of_mem hΔ hpts (hF.memP k) hX.1 (Ne.symm hXk)
    (hall X (left_mem_lineOf hX.1)) (right_mem_lineOf hX.1) hYl hXY
  exact hPk (by rw [hl]; exact left_mem_lineOf (hF.memP k))

private theorem IsMaxFrame.false_of_mem_of_forall_commuting [Finite H]
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} {X Y W : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k)
    (hXY : X ≠ Y) (hcXY : Commuting X Y) (hW : W ∈ rankTwoResidue Δ P Q j k)
    (hWM : W ∉ lineOf Δ X Y) (hWc : ∀ D ∈ lineOf Δ X Y, Commuting W D)
    (hPk : P k ∈ lineOf Δ X Y) : False := by
  have hR := hF.toIsFrame.lineOf_subset_rankTwoResidue hX hY
  obtain ⟨X', hX'M, hX'k⟩ : ∃ X' ∈ lineOf Δ X Y, X' ≠ P k := by
    by_cases hXP : X = P k
    · exact ⟨Y, right_mem_lineOf hY.1, fun h => hXY (hXP.trans h.symm)⟩
    · exact ⟨X, left_mem_lineOf hX.1, hXP⟩
  have hM := lineOf_eq_of_mem hΔ hpts hX.1 hY.1 hXY hcXY hPk hX'M (Ne.symm hX'k)
  have hWk : W ≠ P k := fun h => hWM (h ▸ hPk)
  refine hF.false_of_lineOf_ne hΔ hpts hML hW (hR hX'M) hWk hX'k
    (hWc (P k) hPk).symm
    (commuting_of_mem_lineOf_of_mem_lineOf hΔ hX.1 hY.1 hcXY hPk hX'M)
    (hWc X' hX'M) ?_
  intro heq
  exact hWM (by rw [← hM, ← heq]; exact right_mem_lineOf hW.1)

private theorem IsMaxFrame.false_of_not_forall_commuting [Finite H]
    (hΔ : IsTransvectionClass Δ) (hpts : PointsDetermined Δ) (hML : MeetsLines Δ)
    (hF : IsMaxFrame Δ P Q) {j k : Fin r} {X Y W : Subgroup H}
    (hX : X ∈ rankTwoResidue Δ P Q j k) (hY : Y ∈ rankTwoResidue Δ P Q j k)
    (hXY : X ≠ Y) (hcXY : Commuting X Y) (hW : W ∈ rankTwoResidue Δ P Q j k)
    (hWM : W ∉ lineOf Δ X Y) (hWc : ∀ D ∈ lineOf Δ X Y, Commuting W D)
    (hPk : P k ∉ lineOf Δ X Y) (hnot : ¬ ∀ D ∈ lineOf Δ X Y, Commuting (P k) D) : False := by
  have hR := hF.toIsFrame.lineOf_subset_rankTwoResidue hX hY
  have hcomm : ∀ {D D' : Subgroup H}, D ∈ lineOf Δ X Y → D' ∈ lineOf Δ X Y →
      Commuting D D' := fun hD hD' =>
    commuting_of_mem_lineOf_of_mem_lineOf hΔ hX.1 hY.1 hcXY hD hD'
  obtain ⟨E, hEM, hPE⟩ := hML X hX.1 Y hY.1 hXY hcXY (P k) (hF.memP k)
  obtain ⟨V, hVM, hVE⟩ : ∃ V ∈ lineOf Δ X Y, V ≠ E := by
    by_cases hXE : X = E
    · exact ⟨Y, right_mem_lineOf hY.1, fun h => hXY (hXE.trans h.symm)⟩
    · exact ⟨X, left_mem_lineOf hX.1, hXE⟩
  have hZV : W ≠ V := fun h => hWM (h ▸ hVM)
  have hcZV : Commuting W V := hWc V hVM
  obtain ⟨X₁, hX₁N, hPX₁⟩ := hML W hW.1 V (hR hVM).1 hZV hcZV (P k) (hF.memP k)
  have hX₁M : ∀ D ∈ lineOf Δ X Y, Commuting D X₁ := fun D hD =>
    (commuting_of_commuting_ends hX.1 hY.1 (hWc X (left_mem_lineOf hX.1))
      (hWc Y (right_mem_lineOf hY.1)) (hcomm hVM (left_mem_lineOf hX.1))
      (hcomm hVM (right_mem_lineOf hY.1)) hX₁N hD).symm
  have hX₁R := hF.toIsFrame.lineOf_subset_rankTwoResidue hW (hR hVM) hX₁N
  have hX₁k : X₁ ≠ P k := by
    intro h
    exact hnot fun D hD => by rw [← h]; exact (hX₁M D hD).symm
  have hEk : E ≠ P k := fun h => hPk (by rw [← h]; exact hEM)
  have hX₁E : X₁ ≠ E := by
    intro h
    have h1 := lineOf_eq_of_mem hΔ hpts hW.1 (hR hVM).1 hZV hcZV (h ▸ hX₁N)
      (right_mem_lineOf (hR hVM).1) hVE.symm
    have h2 := lineOf_eq_of_mem hΔ hpts hX.1 hY.1 hXY hcXY hEM hVM hVE.symm
    exact hWM (by rw [← h2, h1]; exact left_mem_lineOf hW.1)
  refine hF.false_of_lineOf_ne hΔ hpts hML hX₁R (hR hEM) hX₁k hEk hPX₁ hPE
    (hX₁M E hEM).symm ?_
  intro hl
  have hEl : E ∈ lineOf Δ (P k) X₁ := by rw [hl]; exact right_mem_lineOf (hR hEM).1
  have hl' := lineOf_eq_of_mem hΔ hpts (hF.memP k) hX₁R.1 (Ne.symm hX₁k) hPX₁
    (right_mem_lineOf hX₁R.1) hEl hX₁E
  have hPl : P k ∈ lineOf Δ X₁ E := by rw [hl']; exact left_mem_lineOf (hF.memP k)
  exact hnot fun D hD => (hPl.2 D (hR hD).1 (hX₁M D hD) (hcomm hD hEM)).symm

theorem IsMaxFrame.mem_lineOf_of_mem_rankTwoResidue [Finite H] (hΔ : IsTransvectionClass Δ)
    (hpts : PointsDetermined Δ) (hML : MeetsLines Δ) (hF : IsMaxFrame Δ P Q) {j k : Fin r}
    {X Y W : Subgroup H} (hX : X ∈ rankTwoResidue Δ P Q j k)
    (hY : Y ∈ rankTwoResidue Δ P Q j k) (hXY : X ≠ Y) (hcXY : Commuting X Y)
    (hW : W ∈ rankTwoResidue Δ P Q j k) (hWX : Commuting W X) (hWY : Commuting W Y) :
    W ∈ lineOf Δ X Y := by
  by_contra hWM
  have hWc : ∀ D ∈ lineOf Δ X Y, Commuting W D := fun D hD => hD.2 W hW.1 hWX hWY
  by_cases hPk : P k ∈ lineOf Δ X Y
  · exact hF.false_of_mem_of_forall_commuting hΔ hpts hML hX hY hXY hcXY hW hWM hWc hPk
  · exact hF.false_of_not_forall_commuting hΔ hpts hML hX hY hXY hcXY hW hWM hWc hPk
      (hF.not_forall_commuting_of_not_mem hΔ hpts hML hX hY hXY hcXY hPk)

end CFSG.Timmesfeld.Transvection
