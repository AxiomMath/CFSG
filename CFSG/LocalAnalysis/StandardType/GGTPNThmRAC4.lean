module

public import CFSG.LocalAnalysis.StandardType.GGTPNThmRACore
public import CFSG.LocalAnalysis.StandardType.GGB36Defs
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggKacRA_b36_sum_eq_length (ds : List ℕ) (h : ∀ x ∈ ds, x = 1) :
    ds.sum = ds.length := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    have hx : x = 1 := h x (by simp)
    have hxs : ∀ y ∈ xs, y = 1 := fun y hy => h y (by simp [hy])
    simp [hx, ih hxs, Nat.add_comm]

private theorem ggKacRA_b36_labelIso_A {labL labJ' labJ : LargeEvenLabel}
    (hL : labL.tag = .E6 ∨ labL.tag = .twE6) (hJ : GGB36JLabel labL labJ)
    (ht : labJ'.tag = .A) (hr : labJ'.rank = 1 ∨ labJ'.rank = 3 ∨ labJ'.rank = 4) :
    ¬ GGLabelIso labJ' labJ := by
  intro hiso
  obtain ⟨t', r', n'⟩ := labJ'
  obtain ⟨tL, rL, nL⟩ := labL
  simp only at ht hr hL
  rcases hL with hE | hE
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hbad, -⟩ | ⟨hbad, -⟩
    · rcases h with h | h | h | h | h <;>
        (rcases hr with rfl | rfl | rfl <;>
          rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | ⟨-, h⟩ <;>
        (rcases hr with rfl | rfl | rfl <;>
          rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · simp_all
    · simp_all
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨hbad, -⟩ | ⟨hbad, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · simp_all
    · simp_all
    · rcases h with h | h <;>
        (rcases hr with rfl | rfl | rfl <;>
          rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | h | h | h | ⟨-, h⟩ <;>
        (rcases hr with rfl | rfl | rfl <;>
          rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))

private theorem ggKacRA_b36_labelIso_twA_rankThree {labL labJ' labJ : LargeEvenLabel}
    (hL : labL.tag = .E6 ∨ labL.tag = .twE6) (hJ : GGB36JLabel labL labJ)
    (ht : labJ'.tag = .twA) (hr : labJ'.rank = 3) :
    ¬ GGLabelIso labJ' labJ := by
  intro hiso
  obtain ⟨t', r', n'⟩ := labJ'
  obtain ⟨tL, rL, nL⟩ := labL
  simp only at ht hr hL
  rcases hL with hE | hE
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hbad, -⟩ | ⟨hbad, -⟩
    · rcases h with h | h | h | h | h <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | ⟨-, h⟩ <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · simp_all
    · simp_all
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨hbad, -⟩ | ⟨hbad, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · simp_all
    · simp_all
    · rcases h with h | h <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | h | h | h | ⟨-, h⟩ <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))

private theorem ggKacRA_b36_labelIso_twA_rankFour {labL labJ' labJ : LargeEvenLabel}
    (hL : labL.tag = .E6 ∨ labL.tag = .twE6) (hJ : GGB36JLabel labL labJ)
    (ht : labJ'.tag = .twA) (hr : labJ'.rank = 4) (hn : 2 ≤ labJ'.n) :
    ¬ GGLabelIso labJ' labJ := by
  intro hiso
  obtain ⟨t', r', n'⟩ := labJ'
  obtain ⟨tL, rL, nL⟩ := labL
  simp only at ht hr hn hL
  rcases hL with hE | hE
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨hbad, -⟩ | ⟨hbad, -⟩
    · rcases h with h | h | h | h | h <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | ⟨-, h⟩ <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · simp_all
    · simp_all
  · subst tL
    unfold GGB36JLabel at hJ
    rcases hJ with ⟨hbad, -⟩ | ⟨hbad, -⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · simp_all
    · simp_all
    · rcases h with h | h <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))
    · rcases h with h | h | h | h | h | ⟨-, h⟩ <;>
        (rw [h] at hiso <;>
          unfold GGLabelIso at hiso <;>
          (rcases hiso with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> simp_all))

private theorem ggKacRA_b36_row_twA41 :
    GGTablePRow 3 (⟨.twA, 4, 1⟩ : LargeEvenLabel) ⟨.twA, 5, 1⟩ := by
  unfold GGTablePRow
  right; right; right; right; right; right; right; left
  exact ⟨rfl, by norm_num, by norm_num, Or.inl rfl⟩

private theorem ggKacRA_b36_N {tX : LargeEvenLieTag} {rX nX : ℕ}
    (hRA : GGKacRA (⟨tX, rX, nX⟩ : LargeEvenLabel) 3) (h5 : rX ≤ 5) :
    rX + 1 = 3 ∨ rX + 1 = 6 := by
  have h := hRA
  unfold GGKacRA at h
  dsimp only at h
  rcases h with ⟨-, hdvd, -⟩ | ⟨-, hdvd, -⟩ <;>
    obtain ⟨k, hk⟩ := hdvd <;> omega

private theorem ggKacRA_b36_tag {tX : LargeEvenLieTag} {rX nX : ℕ}
    (hRA : GGKacRA (⟨tX, rX, nX⟩ : LargeEvenLabel) 3) : tX = .A ∨ tX = .twA := by
  have h := hRA
  unfold GGKacRA at h
  dsimp only at h
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

private theorem ggKacRA_b36_sum_pos {tX : LargeEvenLieTag} {nX : ℕ} {ds : List ℕ}
    (hne : ds ≠ []) (hmem : ∀ x ∈ ds, x = 1 ∨ (tX = .twA ∧ nX = 1 ∧ (x = 2 ∨ x = 3))) :
    1 ≤ ds.sum := by
  obtain ⟨z, zs, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hz := hmem z (by simp)
  rcases hz with rfl | ⟨-, -, hz⟩
  · simp
  · rcases hz with rfl | rfl <;> simp only [List.sum_cons] <;> omega

private theorem ggKacRA_b36_ds_one_of_tagA {nX : ℕ} {ds : List ℕ}
    (hmem : ∀ x ∈ ds, x = 1 ∨ (LargeEvenLieTag.A = .twA ∧ nX = 1 ∧ (x = 2 ∨ x = 3))) :
    ∀ x ∈ ds, x = 1 := by
  intro x hx
  rcases hmem x hx with h1 | ⟨hbad, -, -⟩
  · exact h1
  · exact absurd hbad (by simp)

private theorem ggKacRA_b36_ds_one_of_ne_one {nX : ℕ} {ds : List ℕ} (hn1 : nX ≠ 1)
    (hmem : ∀ x ∈ ds, x = 1 ∨ (LargeEvenLieTag.twA = .twA ∧ nX = 1 ∧ (x = 2 ∨ x = 3))) :
    ∀ x ∈ ds, x = 1 := by
  intro x hx
  rcases hmem x hx with h1 | ⟨-, hbad, -⟩
  · exact h1
  · exact absurd hbad hn1

private theorem ggKacRA_b36_split_tagA {X : Type} [Group X] {J : Subgroup X}
    {labL labJ : LargeEvenLabel} {a rX nX : ℕ} {ds : List ℕ}
    (hrig : GGLabelRigidInput) (hLtag : labL.tag = .E6 ∨ labL.tag = .twE6)
    (hJLabel : GGB36JLabel labL labJ) (hΛJ : LargeEvenInLambda2 labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hN : rX + 1 = 3 ∨ rX + 1 = 6) (hsum : rX + 1 = a + ds.sum)
    (hlen12 : ds.length = 1 ∨ ds.length = 2) (hds1 : ∀ x ∈ ds, x = 1)
    (hΛ : LargeEvenInLambda2 (⟨.A, a - 1, nX⟩ : LargeEvenLabel))
    (hh : GGHasLabel (⟨.A, a - 1, nX⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) :
    GGTPNRow 3 J := by
  have hsum_eq : ds.sum = ds.length := ggKacRA_b36_sum_eq_length ds hds1
  have ha : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 := by
    rcases hN with h3 | h6 <;> rcases hlen12 with hl | hl <;> omega
  rcases ha with rfl | rfl | rfl | rfl
  · simp [LargeEvenInLambda2] at hΛ
  · have hΛJ' : LargeEvenInLambda2 (⟨.A, 1, nX⟩ : LargeEvenLabel) := by simpa using hΛ
    have hhJ' : GGHasLabel (⟨.A, 1, nX⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
    have hiso : GGLabelIso (⟨.A, 1, nX⟩ : LargeEvenLabel) labJ :=
      hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
    exact (ggKacRA_b36_labelIso_A hLtag hJLabel rfl (Or.inl rfl) hiso).elim
  · have hΛJ' : LargeEvenInLambda2 (⟨.A, 3, nX⟩ : LargeEvenLabel) := by simpa using hΛ
    have hhJ' : GGHasLabel (⟨.A, 3, nX⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
    have hiso : GGLabelIso (⟨.A, 3, nX⟩ : LargeEvenLabel) labJ :=
      hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
    exact (ggKacRA_b36_labelIso_A hLtag hJLabel rfl (Or.inr (Or.inl rfl)) hiso).elim
  · have hΛJ' : LargeEvenInLambda2 (⟨.A, 4, nX⟩ : LargeEvenLabel) := by simpa using hΛ
    have hhJ' : GGHasLabel (⟨.A, 4, nX⟩ : LargeEvenLabel)
        (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
    have hiso : GGLabelIso (⟨.A, 4, nX⟩ : LargeEvenLabel) labJ :=
      hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
    exact (ggKacRA_b36_labelIso_A hLtag hJLabel rfl (Or.inr (Or.inr rfl)) hiso).elim

private theorem ggKacRA_b36_split_twA_q2 {X : Type} [Group X] {J : Subgroup X}
    {labL labJ : LargeEvenLabel} {a rX : ℕ} {ds : List ℕ}
    (hrig : GGLabelRigidInput) (hLtag : labL.tag = .E6 ∨ labL.tag = .twE6)
    (hJLabel : GGB36JLabel labL labJ) (hΛJ : LargeEvenInLambda2 labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hΛX : LargeEvenInLambda2 (⟨.twA, rX, 1⟩ : LargeEvenLabel))
    (hhX : GGHasLabel (⟨.twA, rX, 1⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X))
    (hN : rX + 1 = 3 ∨ rX + 1 = 6) (hsum : rX + 1 = a + ds.sum) (hpos : 1 ≤ ds.sum)
    (hbr : (LargeEvenInLambda2 (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.twA, a - 1, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) ∨
      (LargeEvenLieTag.twA = .twA ∧ a = 2 ∧
        LargeEvenInLambda2 (⟨.A, 1, 1⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.A, 1, 1⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))) :
    GGTPNRow 3 J := by
  have ha5 : a ≤ 5 := by
    rcases hN with h3 | h6 <;> omega
  have ha : a = 3 ∨ a = 4 ∨ a = 5 ∨ a ≤ 2 := by omega
  rcases ha with rfl | rfl | rfl | ha2
  · rcases hbr with ⟨hΛ, -⟩ | ⟨-, hbad, -, -⟩
    · simp [LargeEvenInLambda2] at hΛ
    · omega
  · rcases hbr with ⟨hΛ, hh⟩ | ⟨-, hbad, -, -⟩
    · have hΛJ' : LargeEvenInLambda2 (⟨.twA, 3, 1⟩ : LargeEvenLabel) := by simpa using hΛ
      have hhJ' : GGHasLabel (⟨.twA, 3, 1⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
      have hiso : GGLabelIso (⟨.twA, 3, 1⟩ : LargeEvenLabel) labJ :=
        hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
      exact (ggKacRA_b36_labelIso_twA_rankThree hLtag hJLabel rfl rfl hiso).elim
    · omega
  · rcases hbr with ⟨hΛ, hh⟩ | ⟨-, hbad, -, -⟩
    · have hΛJ' : LargeEvenInLambda2 (⟨.twA, 4, 1⟩ : LargeEvenLabel) := by simpa using hΛ
      have hhJ' : GGHasLabel (⟨.twA, 4, 1⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
      have hrX : rX = 5 := by omega
      subst hrX
      exact ⟨⟨.twA, 4, 1⟩, ⟨.twA, 5, 1⟩, hΛJ', hΛX, ggKacRA_b36_row_twA41, hhJ', hhX⟩
    · omega
  · rcases hbr with ⟨hΛ, -⟩ | ⟨-, -, hΛ, -⟩
    · simp only [LargeEvenInLambda2] at hΛ
      omega
    · simp [LargeEvenInLambda2] at hΛ

private theorem ggKacRA_b36_split_twA_q4 {X : Type} [Group X] {J : Subgroup X}
    {labL labJ : LargeEvenLabel} {a rX nX : ℕ} {ds : List ℕ}
    (hrig : GGLabelRigidInput) (hLtag : labL.tag = .E6 ∨ labL.tag = .twE6)
    (hJLabel : GGB36JLabel labL labJ) (hΛJ : LargeEvenInLambda2 labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hN : rX + 1 = 3 ∨ rX + 1 = 6) (hsum : rX + 1 = a + ds.sum)
    (hlen12 : ds.length = 1 ∨ ds.length = 2) (hds1 : ∀ x ∈ ds, x = 1) (hn2 : 2 ≤ nX)
    (hbr : (LargeEvenInLambda2 (⟨.twA, a - 1, nX⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.twA, a - 1, nX⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J)) ∨
      (LargeEvenLieTag.twA = .twA ∧ a = 2 ∧
        LargeEvenInLambda2 (⟨.A, 1, nX⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.A, 1, nX⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J))) :
    GGTPNRow 3 J := by
  have hsum_eq : ds.sum = ds.length := ggKacRA_b36_sum_eq_length ds hds1
  have ha : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 5 := by
    rcases hN with h3 | h6 <;> rcases hlen12 with hl | hl <;> omega
  rcases ha with rfl | rfl | rfl | rfl
  · rcases hbr with ⟨hΛ, -⟩ | ⟨-, hbad, -, -⟩
    · simp [LargeEvenInLambda2] at hΛ
    · omega
  · rcases hbr with ⟨hΛ, -⟩ | ⟨-, -, hΛ, hh⟩
    · simp [LargeEvenInLambda2] at hΛ
    · have hΛJ' : LargeEvenInLambda2 (⟨.A, 1, nX⟩ : LargeEvenLabel) := by simpa using hΛ
      have hhJ' : GGHasLabel (⟨.A, 1, nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
      have hiso : GGLabelIso (⟨.A, 1, nX⟩ : LargeEvenLabel) labJ :=
        hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
      exact (ggKacRA_b36_labelIso_A hLtag hJLabel rfl (Or.inl rfl) hiso).elim
  · rcases hbr with ⟨hΛ, hh⟩ | ⟨-, hbad, -, -⟩
    · have hΛJ' : LargeEvenInLambda2 (⟨.twA, 3, nX⟩ : LargeEvenLabel) := by simpa using hΛ
      have hhJ' : GGHasLabel (⟨.twA, 3, nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
      have hiso : GGLabelIso (⟨.twA, 3, nX⟩ : LargeEvenLabel) labJ :=
        hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
      exact (ggKacRA_b36_labelIso_twA_rankThree hLtag hJLabel rfl rfl hiso).elim
    · omega
  · rcases hbr with ⟨hΛ, hh⟩ | ⟨-, hbad, -, -⟩
    · have hΛJ' : LargeEvenInLambda2 (⟨.twA, 4, nX⟩ : LargeEvenLabel) := by simpa using hΛ
      have hhJ' : GGHasLabel (⟨.twA, 4, nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := by simpa using hh
      have hiso : GGLabelIso (⟨.twA, 4, nX⟩ : LargeEvenLabel) labJ :=
        hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
      exact (ggKacRA_b36_labelIso_twA_rankFour hLtag hJLabel rfl rfl hn2 hiso).elim
    · omega

private theorem ggKacRA_b36_nonsplit {X : Type} [Group X] {J : Subgroup X}
    {labL labJ : LargeEvenLabel} {tX : LargeEvenLieTag} {rX nX : ℕ}
    (hrig : GGLabelRigidInput) (hLtag : labL.tag = .E6 ∨ labL.tag = .twE6)
    (hJLabel : GGB36JLabel labL labJ) (hΛJ : LargeEvenInLambda2 labJ)
    (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hN : rX + 1 = 3 ∨ rX + 1 = 6) (hge : 2 ≤ (rX + 1) / 3)
    (hbr : (tX = .A ∨ (rX + 1) / 3 = 2) ∧
        LargeEvenInLambda2 (⟨.A, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.A, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) ∨
      (tX = .twA ∧ 3 ≤ (rX + 1) / 3 ∧
        LargeEvenInLambda2 (⟨.twA, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel) ∧
        GGHasLabel (⟨.twA, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J))) : GGTPNRow 3 J := by
  rcases hN with h3 | h6
  · rw [h3] at hge
    norm_num at hge
  · have hb : (rX + 1) / 3 = 2 := by rw [h6]
    rcases hbr with ⟨-, hΛ, hh⟩ | ⟨-, hge3, -, -⟩
    · have hlab : (⟨.A, (rX + 1) / 3 - 1, 3 * nX⟩ : LargeEvenLabel) =
          ⟨.A, 1, 3 * nX⟩ := by rw [hb]
      rw [hlab] at hΛ hh
      have hΛJ' : LargeEvenInLambda2 (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel) := hΛ
      have hhJ' : GGHasLabel (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel)
          (↥J ⧸ Subgroup.center ↥J) := hh
      have hiso : GGLabelIso (⟨.A, 1, 3 * nX⟩ : LargeEvenLabel) labJ :=
        hrig _ _ _ hΛJ' hΛJ hhJ' hhJ
      exact (ggKacRA_b36_labelIso_A hLtag hJLabel rfl (Or.inl rfl) hiso).elim
    · rw [hb] at hge3
      omega

theorem ggTPNRow_b36JCl_ra
    {S : ℕ → LargeEvenLabel → Prop} {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X} (hloc : GGTPNLocalCore 3 A σ J) (h8 : GGTPNOnlyComp 3 σ J)
    (hm : GGTPNMarked 3 S A) {labJ labX : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX)
    (hJ : ∃ labL : LargeEvenLabel, (labL.tag = .E6 ∨ labL.tag = .twE6) ∧ GGB36JLabel labL labJ)
    (hRA : GGKacRA labX 3) (h5 : labX.rank ≤ 5) (hhJ : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hhX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    GGTPNRow 3 J := by
  obtain ⟨tX, rX, nX⟩ := labX
  dsimp only at *
  obtain ⟨labL, hLtag, hJLabel⟩ := hJ
  have hN : rX + 1 = 3 ∨ rX + 1 = 6 := ggKacRA_b36_N hRA h5
  have htagX : tX = .A ∨ tX = .twA := ggKacRA_b36_tag hRA
  have hrig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hm' : GGTPNMarked 3 (fun _ lab => lab = ⟨tX, rX, nX⟩) A :=
    ggTPNMarked_eq_of_ggKacRA hrig Nat.prime_three hm hΛX hRA hhX
  have hcore := split_or_fieldType_of_ggKacRA (p := 3) Nat.prime_three hloc h8 hRA hm'
  rcases hcore with ⟨a, ds, hsum, hne, hlen, hmem, hbr⟩ | ⟨hge, -, hbr⟩
  · have hlen12 : ds.length = 1 ∨ ds.length = 2 := by
      have hpos : 0 < ds.length := List.length_pos_iff.mpr hne
      omega
    dsimp only at hmem hbr
    have hpos : 1 ≤ ds.sum := ggKacRA_b36_sum_pos hne hmem
    rcases htagX with htA | htT
    · subst tX
      rcases hbr with ⟨hΛ, hh⟩ | ⟨hbad, -⟩
      · exact ggKacRA_b36_split_tagA hrig hLtag hJLabel hΛJ hhJ hN hsum hlen12
          (ggKacRA_b36_ds_one_of_tagA hmem) hΛ hh
      · exact absurd hbad (by simp)
    · subst tX
      by_cases hn1 : nX = 1
      · subst nX
        exact ggKacRA_b36_split_twA_q2 hrig hLtag hJLabel hΛJ hhJ hΛX hhX hN hsum hpos hbr
      · have hn2 : 2 ≤ nX := by
          have h1 : 1 ≤ nX := hΛX.1
          omega
        exact ggKacRA_b36_split_twA_q4 hrig hLtag hJLabel hΛJ hhJ hN hsum hlen12
          (ggKacRA_b36_ds_one_of_ne_one hn1 hmem) hn2 hbr
  · dsimp only at hbr
    exact ggKacRA_b36_nonsplit hrig hLtag hJLabel hΛJ hhJ hN hge hbr

end CFSG.StandardType

end
