module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthShape
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShape
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJA1
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJA2
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoD4Odd
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoG2
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoTriD4
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoTwA2
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2

private theorem orthLeaf_charP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ}
    (hk : 1 ≤ k) (h : Nat.card F = 2 ^ k) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, h]
  apply Nat.mod_eq_zero_of_dvd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨2 ^ t, by rw [pow_succ]; ring⟩

private theorem orthLeaf_split_D {r n : ℕ}
    (h : LargeEvenSplit 3 (⟨.D, r, n⟩ : LargeEvenLabel)) : 3 ∣ 2 ^ n - 1 ∨ n = 1 := by
  unfold LargeEvenSplit at h
  rcases h with ⟨-, h3⟩ | ⟨huntw, -⟩ | ⟨hD, -⟩ | ⟨hn, -⟩
  · exact Or.inl h3
  · exact absurd trivial huntw
  · exact absurd hD (by simp)
  · exact Or.inr hn

private theorem orthLeaf_odd_not_three_dvd {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  intro h
  have hz : ((2 ^ n - 1 : ℕ) : ZMod 3) = 0 :=
    (ZMod.natCast_eq_zero_iff (2 ^ n - 1) 3).2 h
  rw [Nat.cast_sub (Nat.one_le_two_pow)] at hz
  push_cast at hz
  have hpow : (2 : ZMod 3) ^ n = -1 := by
    have h2 : (2 : ZMod 3) = -1 := by decide
    rw [h2]
    exact hn.neg_one_pow
  rw [hpow] at hz
  have hc : ((-1 : ZMod 3) - 1) = 1 := by decide
  rw [hc] at hz
  exact one_ne_zero hz

private def orthLeaf_SymLabelShape (s : LargeEvenLabel) : Prop :=
  s.tag = .A ∨ (s.tag = .twA ∧ 3 ≤ s.rank) ∨ s.tag = .B ∨ s.tag = .C ∨
    ((s.tag = .D ∨ s.tag = .twD) ∧ 4 ≤ s.rank)

private theorem orthLeaf_no_g2 {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : GGLabelG2 t) (h : GGLabelIso s t) : False := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelG2, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all

private theorem orthLeaf_no_triD4 {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : t.tag = .triD4) (h : GGLabelIso s t) : False := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all

private theorem orthLeaf_no_twA_two {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : t.tag = .twA) (hr : t.rank = 2) (h : GGLabelIso s t) : False := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthLeaf_A2_shape {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : GGLabelA2 t) (h : GGLabelIso s t) : s.tag = .A ∧ s.rank = 2 := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelA2, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthLeaf_eq_of_A1_shape {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : t.tag = .A) (hr : t.rank = 1) (h : GGLabelIso s t) : s = t := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthLeaf_D4_of_iso {s t : LargeEvenLabel} (hs : orthLeaf_SymLabelShape s)
    (ht : t.tag = .D) (hr : t.rank = 4) (h : GGLabelIso s t) : s = ⟨.D, 4, t.n⟩ := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthLeaf_D_left {lab : LargeEvenLabel} {r n : ℕ} (hr : r ≠ 3)
    (h : GGLabelIso (⟨.D, r, n⟩ : LargeEvenLabel) lab) : lab = ⟨.D, r, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all <;> omega

private theorem orthLeaf_exists_label_of_marking {K : Type} [Group K] {P : LargeEvenMarkProp K}
    (h : LargeEvenMarking K P) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : K ⧸ Subgroup.center K ≃* R),
      LargeEvenInLambda2 lab ∧ P lab R I F θ ∧ GGHasLabel lab (K ⧸ Subgroup.center K) := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨hs, hna, hθ⟩ := hQ
  obtain ⟨θ, hP⟩ := hθ
  refine ⟨lab, R, hR, I, F, θ, hlab, hP, ?_⟩
  exact CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ hQ' => by
    obtain ⟨-, -, hθ'⟩ := hQ'
    obtain ⟨θ', -⟩ := hθ'
    exact ⟨θ'⟩) hraw

private theorem orthLeaf_lab_of_eq_marking {K : Type} [Group K] {lab : LargeEvenLabel}
    (h : LargeEvenMarking K (fun l _ _ _ _ _ => l = lab)) :
    LargeEvenInLambda2 lab ∧ GGHasLabel lab (K ⧸ Subgroup.center K) := by
  obtain ⟨-, lab0, hlab0, hraw0⟩ := h
  obtain ⟨R, hR, I, F, hQ0⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw0
  obtain ⟨-, -, hθ0⟩ := hQ0
  obtain ⟨θ0, hEq⟩ := hθ0
  subst hEq
  refine ⟨hlab0, ?_⟩
  exact CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ hQ' => by
    obtain ⟨-, -, hθ'⟩ := hQ'
    obtain ⟨θ', -⟩ := hθ'
    exact ⟨θ'⟩) hraw0

private theorem orthLeaf_ggMarkingAll_of_label_eq
    {K : Type} [Group K] {lab : LargeEvenLabel}
    (hmark : LargeEvenMarking K (fun l _ _ _ _ _ => l = lab))
    {H Q : LargeEvenLabel → Prop}
    (hQ : ∀ lab', LargeEvenInLambda2 lab' → GGLabelIso lab lab' → H lab' → Q lab') :
    GGMarkingAll (K := K) (fun lab' _ _ _ _ _ => H lab' → Q lab') := by
  intro P hP
  obtain ⟨hlab, hhas⟩ := orthLeaf_lab_of_eq_marking hmark
  obtain ⟨hcomm, lab', hlab', hraw'⟩ := hP
  have hhas' : GGHasLabel lab' (K ⧸ Subgroup.center K) :=
    CFSG.StandardType.largeEvenRawDatum_mono (fun R _ I F hQ' => by
      obtain ⟨-, -, hθ⟩ := hQ'
      obtain ⟨θ, -⟩ := hθ
      exact ⟨θ⟩) hraw'
  have hiso : GGLabelIso lab lab' :=
    CFSG.StandardType.ggLabelRigidInput_holds lab lab' (K ⧸ Subgroup.center K) hlab hlab' hhas hhas'
  refine ⟨hcomm, lab', hlab', CFSG.StandardType.largeEvenRawDatum_mono (fun R _ I F hQ' => ?_) hraw'⟩
  obtain ⟨hs, hna, hθ⟩ := hQ'
  obtain ⟨θ, hPθ⟩ := hθ
  exact ⟨hs, hna, θ, hPθ, fun hH => hQ lab' hlab' hiso hH⟩

private def orthLeaf_OrthShapeData (X : Type) [Group X] (A : Subgroup (MulAut X))
    (J : Subgroup X) (n r : ℕ) : Prop :=
  ∃ s : LargeEvenLabel, LargeEvenInLambda2 s ∧ GGHasLabel s (J ⧸ Subgroup.center J) ∧
    orthLeaf_SymLabelShape s ∧
    (s.tag = .A → (s.rank = 1 → Nat.card A ≤ 3 ^ 2) ∧
      (s.rank = 2 → Subgroup.center J ≠ ⊥)) ∧
    ((s.tag = .D ∨ s.tag = .twD) → s.n = n ∧
      (s.tag = .D → s.rank = 4 → n = 1 → r = 6))

private theorem orthLeaf_frame
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J) :
    ∃ (lab : LargeEvenLabel) (n r : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      lab = ⟨.D, r, n⟩ ∧ 1 ≤ n ∧ 3 ≤ r ∧ 3 ^ 3 ≤ Nat.card A ∧
      LargeEvenSplit 3 lab ∧
      LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) ∧
      ((r = 3 ∧ LinShapeConcl (2 ^ n) 4 A J) ∨
        (4 ≤ r ∧ orthLeaf_OrthShapeData X A J n r)) := by
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hKLocal, huniq, hA27, hmarkX⟩ := hd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmarkX
  have hmark : LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) :=
    ⟨hcomm, lab, hlab, CFSG.StandardType.largeEvenRawDatum_mono
      (fun R _ I F hQ => by
        obtain ⟨hs, hna, θ, -⟩ := hQ
        exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθP⟩ := hQ
  obtain ⟨θ, hP⟩ := hθP
  have htag : lab.tag = .D := hP.1
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  have hn1 : 1 ≤ n := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.1
  have hr3 : 3 ≤ rank := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.2
  have hsplitD : 3 ∣ 2 ^ n - 1 ∨ n = 1 := orthLeaf_split_D hP.2.1
  by_cases hr3eq : rank = 3
  · subst hr3eq
    dsimp only [LargeEvenRawDatumLegacy] at hraw
    rw [if_pos rfl] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hcardK, hQK⟩ := hraw
    obtain ⟨hsimpleK, hnaK, θK, hPK⟩ := hQK
    letI := hfieldK
    letI := hfiniteK
    have hcharK : CharP K 2 := orthLeaf_charP_two_of_card_pow hn1 hcardK
    have hsplitK : 3 ∣ Nat.card K - 1 ∨ Nat.card K = 2 := by
      rcases hsplitD with h | h
      · exact Or.inl (by rw [hcardK]; exact h)
      · exact Or.inr (by rw [hcardK, h]; norm_num)
    have hsimple : IsSimpleGroup (PSLg 4 K) ∧ ∃ a b : PSLg 4 K, a * b ≠ b * a :=
      ⟨hsimpleK, hnaK⟩
    have hLin : LinShapeConcl (2 ^ n) 4 A J := by
      have h := linShape_holds K hcharK 4 (by norm_num) hsimple hsplitK X hcomm θK A δ J hKLocal
        huniq hA27 hPK.2.2
      rwa [hcardK] at h
    exact ⟨⟨.D, 3, n⟩, n, 3, K, hfieldK, hfiniteK, rfl, hn1, by norm_num, hA27, hP.2.1, hmark,
      Or.inl ⟨rfl, hLin⟩⟩
  · have hr4 : 4 ≤ rank := by omega
    dsimp only [LargeEvenRawDatumLegacy] at hraw
    rw [if_neg hr3eq] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hcardK, hQK⟩ := hraw
    obtain ⟨hsimpleK, hnaK, θK, hPK⟩ := hQK
    letI := hfieldK
    letI := hfiniteK
    have hcharK : CharP K 2 := orthLeaf_charP_two_of_card_pow hn1 hcardK
    have hsimple : IsSimpleGroup (POmPlusG rank K) ∧
        ∃ a b : POmPlusG rank K, a * b ≠ b * a :=
      ⟨hsimpleK, hnaK⟩
    have hOrth : OrthShapeConcl n rank A J :=
      orthShape_holds K hcharK n rank hcardK hr4 hsplitD hsimple X hcomm θK A δ J hKLocal huniq
        hA27 hPK.2.2
    obtain ⟨s, hlabS, hhasS, hdisj⟩ := hOrth
    have hs : orthLeaf_SymLabelShape s := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htw, h3⟩ | hB | hC | ⟨hD, h4, -, -⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl ⟨htw, h3⟩)
      · exact Or.inr (Or.inr (Or.inl hB))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, h4⟩)))
    have hAimp : s.tag = .A → (s.rank = 1 → Nat.card A ≤ 3 ^ 2) ∧
        (s.rank = 2 → Subgroup.center J ≠ ⊥) := by
      intro hAt
      have hdisj' := hdisj
      rcases hdisj' with ⟨hA, h1, h2⟩ | ⟨htw, -⟩ | hB | hC | ⟨hD, -⟩
      · exact ⟨h1, h2⟩
      · rw [hAt] at htw
        exact absurd htw (by decide)
      · rw [hAt] at hB
        exact absurd hB (by decide)
      · rw [hAt] at hC
        exact absurd hC (by decide)
      · rcases hD with hD | hD <;> rw [hAt] at hD <;> exact absurd hD (by decide)
    have hDimp : (s.tag = .D ∨ s.tag = .twD) → s.n = n ∧
        (s.tag = .D → s.rank = 4 → n = 1 → rank = 6) := by
      intro hD
      have hdisj' := hdisj
      rcases hdisj' with ⟨hA, -⟩ | ⟨htw, -⟩ | hB | hC | ⟨hD', h4, hsn, hD6⟩
      · rw [hA] at hD
        rcases hD with hD | hD <;> exact absurd hD (by decide)
      · rw [htw] at hD
        rcases hD with hD | hD <;> exact absurd hD (by decide)
      · rw [hB] at hD
        rcases hD with hD | hD <;> exact absurd hD (by decide)
      · rw [hC] at hD
        rcases hD with hD | hD <;> exact absurd hD (by decide)
      · exact ⟨hsn, hD6⟩
    refine ⟨⟨.D, rank, n⟩, n, rank, K, hfieldK, hfiniteK, rfl, hn1, hr3, hA27, hP.2.1, hmark,
      Or.inr ⟨hr4, ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩⟩⟩

private theorem orthLeaf_cell1
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro hmarkJ
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hG2, hhasJ⟩ := orthLeaf_exists_label_of_marking hmarkJ
  rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
  · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
      hm3p, hm2p⟩ := hLin
    letI := hfieldE
    letI := hfiniteE
    have hcharE : CharP E 2 := by
      refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
      rw [hEcard, pow_mul]
    have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
    exact linJNoG2_holds J m E hcharE hLinJ hmarkJ
  · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
    exact (orthLeaf_no_g2 hs hG2
      (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ)).elim

private theorem orthLeaf_cell2
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab))
    (hZ : Subgroup.center J = ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  have hfalse : False := by
    rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
        hm3p, hm2p⟩ := hLin
      letI := hfieldE
      letI := hfiniteE
      have hcharE : CharP E 2 := by
        refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
        rw [hEcard, pow_mul]
      have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
      obtain ⟨hcommJ, labJ, hlabJ, hrawJ⟩ := hmarkJ
      obtain ⟨R', hR', I', F', hQ'⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawJ
      obtain ⟨-, -, θ', hA2J⟩ := hQ'
      obtain ⟨hrJ, hnJ, htagJ⟩ := hA2J
      rcases htagJ with ⟨htagA, -⟩ | ⟨htagTwA, -⟩
      · have hmarkJA : LargeEvenMarking J
            (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .A) :=
          ⟨hcommJ, labJ, hlabJ, CFSG.StandardType.largeEvenRawDatum_mono
            (fun R _ I F hQ => by
              obtain ⟨hs, hna, θ, hA2⟩ := hQ
              exact ⟨hs, hna, θ, hA2, htagA⟩) hrawJ⟩
        obtain ⟨hm3, hmE4⟩ := linJA2_holds J m E hcharE hLinJ hmarkJA
        have hjm : j = 1 := by
          have h3 : j * m ≤ 4 := hjmN
          rw [hm3, Nat.mul_comm j 3] at h3
          omega
        have hn2 : 2 ≤ n := by
          have h4 : 4 ≤ 2 ^ n := by
            rw [hEcard, hjm, pow_one] at hmE4
            exact hmE4
          by_contra hlt
          have h1 : n ≤ 1 := by omega
          have hle : 2 ^ n ≤ 2 := by
            calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
              _ = 2 := by norm_num
          omega
        have h3n : 3 ∣ 2 ^ n - 1 := by
          rcases orthLeaf_split_D hsplit with h | h
          · exact h
          · omega
        exact (hm3p hm3 (Or.inl ⟨hjm, h3n⟩)) hZ
      · have hmarkJTwA : LargeEvenMarking J
            (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) :=
          ⟨hcommJ, labJ, hlabJ, CFSG.StandardType.largeEvenRawDatum_mono
            (fun R _ I F hQ => by
              obtain ⟨hs, hna, θ, hA2⟩ := hQ
              exact ⟨hs, hna, θ, hA2, htagTwA⟩) hrawJ⟩
        exact absurd hmarkJTwA (linJNoTwA2_holds J m E hcharE hLinJ)
    · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
      obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hA2, hhasJ⟩ :=
        orthLeaf_exists_label_of_marking hmarkJ
      have hres : s.tag = .A ∧ s.rank = 2 :=
        orthLeaf_A2_shape hs hA2
          (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
            hhasS hhasJ)
      exact (hAimp hres.1).2 hres.2 hZ
  exact hfalse.elim

private theorem orthLeaf_cell3
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA))
    (hZ : Subgroup.center J ≠ ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  have hfalse : False := by
    rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
        hm3p, hm2p⟩ := hLin
      letI := hfieldE
      letI := hfiniteE
      have hcharE : CharP E 2 := by
        refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
        rw [hEcard, pow_mul]
      have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
      exact absurd hmarkJ (linJNoTwA2_holds J m E hcharE hLinJ)
    · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
      obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ :=
        orthLeaf_exists_label_of_marking hmarkJ
      have hA2 : GGLabelA2 labJ := hPJ.1
      have htw : labJ.tag = .twA := hPJ.2
      have hr2 : labJ.rank = 2 := hA2.1
      exact orthLeaf_no_twA_two hs htw hr2
        (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
          hhasS hhasJ)
  exact hfalse.elim

private theorem orthLeaf_cell4
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  have hfalse : False := by
    rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
        hm3p, hm2p⟩ := hLin
      letI := hfieldE
      letI := hfiniteE
      have hcharE : CharP E 2 := by
        refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
        rw [hEcard, pow_mul]
      have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
      exact absurd hmarkJ (linJNoTriD4_holds J m E hcharE hLinJ)
    · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
      obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, htagTri, hhasJ⟩ :=
        orthLeaf_exists_label_of_marking hmarkJ
      exact orthLeaf_no_triD4 hs htagTri
        (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
          hhasS hhasJ)
  exact hfalse.elim

private theorem orthLeaf_cell5
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
        (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
  · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
      hm3p, hm2p⟩ := hLin
    letI := hfieldE
    letI := hfiniteE
    have hcharE : CharP E 2 := by
      refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
      rw [hEcard, pow_mul]
    have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
    exact absurd hmarkJ (linJNoD4Odd_holds J m E hcharE hLinJ)
  · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, htP, hhasJ⟩ :=
      orthLeaf_exists_label_of_marking hmarkJ
    obtain ⟨htD, hrD, hodd⟩ := htP
    have hiso : GGLabelIso s labJ :=
      CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ hhasS hhasJ
    have hseq : s = ⟨.D, 4, labJ.n⟩ := orthLeaf_D4_of_iso hs htD hrD hiso
    have hstag : s.tag = .D := by rw [hseq]
    have hDinfo := hDimp (Or.inl hstag)
    obtain ⟨hsn, hD6⟩ := hDinfo
    have htn : labJ.n = n := by
      rw [hseq] at hsn
      exact hsn
    have hnodd : Odd n := by
      rw [← htn]
      exact hodd
    have hn1' : n = 1 := by
      rcases orthLeaf_split_D hsplit with h3 | h1
      · exact absurd h3 (orthLeaf_odd_not_three_dvd hnodd)
      · exact h1
    have hr6 : r = 6 := by
      rw [hseq] at hD6
      exact hD6 rfl rfl hn1'
    have hlab6 : (⟨.D, r, n⟩ : LargeEvenLabel) = ⟨.D, 6, 1⟩ := by
      rw [hr6, hn1']
    refine orthLeaf_ggMarkingAll_of_label_eq
      (H := fun l => LargeEvenSplit 3 l) (Q := fun l =>
        (l.tag = .twE6 ∧ 3 ∣ 2 ^ l.n + 1) ∨ (l.tag = .twD ∧ l.rank = 5) ∨
          (l.tag = .D ∧ l.rank = 6 ∧ l.n = 1) ∨ (l.tag = .twD ∧ l.rank = 7 ∧ l.n = 1))
      hmark ?_
    intro lab' hlab' hiso' hsplit'
    rw [hlab6] at hiso'
    have hlab' : lab' = ⟨.D, 6, 1⟩ := orthLeaf_D_left (by norm_num) hiso'
    subst hlab'
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))

private theorem orthLeaf_cell6
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 3) X A δ J)
    (hmarkA1 : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)) :
    Nat.card A = 3 ^ 3 ∧
      GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
        (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, n, r, K, hfieldK, hfiniteK, hlab, hn1, hr3, hA27, hsplit, hmark, hbranch⟩ :=
    orthLeaf_frame (δ := δ) hd
  subst hlab
  have hfalse : False := by
    rcases hbranch with ⟨hr3eq, hLin⟩ | ⟨hr4, hOrth⟩
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hmE, hj1, hj3, hEcard, hjmN, hJiso, hj3p, hj2p,
        hm3p, hm2p⟩ := hLin
      letI := hfieldE
      letI := hfiniteE
      have hcharE : CharP E 2 := by
        refine orthLeaf_charP_two_of_card_pow (Nat.mul_pos hn1 hj1) ?_
        rw [hEcard, pow_mul]
      have hLinJ : LinJ J m E := ⟨hm2, hmE, hJiso⟩
      have hm2eq : m = 2 := linJA1_holds J m E hcharE hLinJ hmarkA1
      have hjne : j ≠ 3 := by
        have := hjmN
        omega
      have hlt : Nat.card A < 3 ^ 3 := (hm2p hm2eq).2 hjne
      omega
    · obtain ⟨s, hlabS, hhasS, hs, hAimp, hDimp⟩ := hOrth
      obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ :=
        orthLeaf_exists_label_of_marking hmarkA1
      have htagA : labJ.tag = .A := hPJ.1
      have hrankA : labJ.rank = 1 := hPJ.2
      have hst : s = labJ := orthLeaf_eq_of_A1_shape hs htagA hrankA
        (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
          hhasS hhasJ)
      have hAeq : s.tag = .A := by rw [hst]; exact htagA
      have hrank1 : s.rank = 1 := by rw [hst]; exact hrankA
      have hle : Nat.card A ≤ 3 ^ 2 := (hAimp hAeq).1 hrank1
      omega
  exact hfalse.elim

theorem leafOrth_holds
    : KnownOverSix (DatumOn (fam 3)) := by
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    exact orthLeaf_cell1 hd
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact orthLeaf_cell2 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact orthLeaf_cell3 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ
    exact orthLeaf_cell4 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkJ
    exact orthLeaf_cell5 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkA1
    exact orthLeaf_cell6 hd hmarkA1

end CFSG.StandardType.TablePThreeKG

end
