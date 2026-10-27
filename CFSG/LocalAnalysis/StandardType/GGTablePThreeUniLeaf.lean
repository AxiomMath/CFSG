module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniShape

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem uniLeaf_uniCharP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k)
    (h : Nat.card F = 2 ^ k) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, h]
  apply Nat.mod_eq_zero_of_dvd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨2 ^ t, by rw [pow_succ]; ring⟩

private theorem uniLeaf_three_dvd_two_pow_add_one_of_split_twA {rank n : ℕ}
    (h : LargeEvenSplit 3 (⟨.twA, rank, n⟩ : LargeEvenLabel)) : 3 ∣ 2 ^ n + 1 := by
  unfold LargeEvenSplit at h
  rcases h with ⟨huntw, -⟩ | ⟨-, -, h3⟩ | ⟨hD, -⟩ | ⟨hn, -⟩
  · exact absurd huntw (by simp [LargeEvenUntwisted])
  · exact h3
  · exact absurd hD (by simp)
  · have hnn : n = 1 := hn
    rw [hnn]; norm_num

private theorem uniLeaf_label_eq_of_rank_twA {lab : LargeEvenLabel} {r : ℕ} (htag : lab.tag = .twA)
    (hrank : lab.rank = r) : lab = ⟨.twA, r, lab.n⟩ := by
  cases lab
  simp_all

private theorem uniLeaf_eq_of_ggLabelIso_twA_left {lab : LargeEvenLabel} {r n : ℕ} (hr : 4 ≤ r)
    (h : GGLabelIso (⟨.twA, r, n⟩ : LargeEvenLabel) lab) : lab = ⟨.twA, r, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all <;> omega

private theorem uniLeaf_eq_or_twD3_of_ggLabelIso_twA3_left {lab : LargeEvenLabel} {n : ℕ}
    (h : GGLabelIso (⟨.twA, 3, n⟩ : LargeEvenLabel) lab) :
    lab = ⟨.twA, 3, n⟩ ∨ lab = ⟨.twD, 3, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_ggLabelG2_of_ggLabelIso_A {lab : LargeEvenLabel} {r f : ℕ}
    (hg : GGLabelG2 lab) (h : GGLabelIso lab (⟨.A, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelG2] at hg
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_ggLabelG2_of_ggLabelIso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (hg : GGLabelG2 lab) (h : GGLabelIso lab (⟨.twA, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelG2] at hg
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_triD4_of_ggLabelIso_A {lab : LargeEvenLabel} {r f : ℕ}
    (ht : lab.tag = .triD4) (h : GGLabelIso lab (⟨.A, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_triD4_of_ggLabelIso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (ht : lab.tag = .triD4) (h : GGLabelIso lab (⟨.twA, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_D4_of_ggLabelIso_A {lab : LargeEvenLabel} {r f : ℕ}
    (ht : lab.tag = .D) (hr : lab.rank = 4)
    (h : GGLabelIso lab (⟨.A, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_D4_of_ggLabelIso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (ht : lab.tag = .D) (hr : lab.rank = 4)
    (h : GGLabelIso lab (⟨.twA, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_A1_of_ggLabelIso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (ht : lab.tag = .A) (hr : lab.rank = 1)
    (h : GGLabelIso lab (⟨.twA, r, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_not_A2_of_ggLabelIso_A_one {lab : LargeEvenLabel} {f : ℕ}
    (hA2 : GGLabelA2 lab) (h : GGLabelIso lab (⟨.A, 1, f⟩ : LargeEvenLabel)) : False := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelA2] at hA2
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_rank_eq_two_of_ggLabelA2_iso_twA {lab : LargeEvenLabel} {r f : ℕ}
    (hA2 : GGLabelA2 lab) (h : GGLabelIso lab (⟨.twA, r, f⟩ : LargeEvenLabel)) : r = 2 := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelA2] at hA2
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem uniLeaf_exists_label_of_marking {K : Type} [Group K] {P : LargeEvenMarkProp K}
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

private theorem uniLeaf_lab_of_eq_marking {K : Type} [Group K] {lab : LargeEvenLabel}
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

private theorem uniLeaf_ggMarkingAll_of_label_eq
    {K : Type} [Group K] {lab : LargeEvenLabel}
    (hmark : LargeEvenMarking K (fun l _ _ _ _ _ => l = lab))
    {H Q : LargeEvenLabel → Prop}
    (hQ : ∀ lab', LargeEvenInLambda2 lab' → GGLabelIso lab lab' → H lab' → Q lab') :
    GGMarkingAll (K := K) (fun lab' _ _ _ _ _ => H lab' → Q lab') := by
  intro P hP
  obtain ⟨hlab, hhas⟩ := uniLeaf_lab_of_eq_marking hmark
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

private theorem uniLeaf_ggHasLabel_linear_two {F : Type} [Field F] [Finite F] {k : ℕ}
    (hk : Nat.card F = 2 ^ k) :
    GGHasLabel (⟨.A, 1, k⟩ : LargeEvenLabel) (PSLg 2 F) := by
  dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeLinear]
  exact ⟨F, inferInstance, inferInstance, hk, ⟨MulEquiv.refl _⟩⟩

private theorem uniLeaf_ggHasLabel_unitary {Y : Type} [Group Y] {E : Type} [Field E] [Finite E]
    {m k : ℕ} (hm : 1 ≤ m) (hk : Nat.card E = (2 ^ k) ^ 2)
    (e : Y ≃* PSUg m E (2 ^ k)) :
    GGHasLabel (⟨.twA, m - 1, k⟩ : LargeEvenLabel) Y := by
  dsimp only [GGHasLabel, LargeEvenRawDatum, LargeEvenRecipeUnitary]
  refine ⟨E, inferInstance, inferInstance, hk, ?_⟩
  rw [Nat.sub_add_cancel hm]
  exact ⟨e⟩

private theorem uniLeaf_uniFrame {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 1) X A δ J) :
    ∃ (lab : LargeEvenLabel) (K : Type) (_ : Field K) (_ : Finite K) (N : ℕ),
      lab.tag = .twA ∧ 1 ≤ lab.n ∧ 3 ^ 3 ≤ Nat.card A ∧ N = lab.rank + 1 ∧ 3 ≤ N ∧
        Nat.card K = (2 ^ lab.n) ^ 2 ∧ 3 ∣ 2 ^ lab.n + 1 ∧
        LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) ∧
        Nonempty (X ⧸ Subgroup.center X ≃* PSUg N K (2 ^ lab.n)) ∧
        UniShapeConcl (2 ^ lab.n) N A J := by
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hKLocal, huniq, hA27, hmarkX⟩ := hd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmarkX
  have hmark : LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) :=
    ⟨hcomm, lab, hlab, CFSG.StandardType.largeEvenRawDatum_mono
      (fun R _ I F hQ => by
        obtain ⟨hs, hna, hθ⟩ := hQ
        obtain ⟨θ, -⟩ := hθ
        exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθP⟩ := hQ
  obtain ⟨θ, hP⟩ := hθP
  have htag : lab.tag = .twA := hP.1
  obtain ⟨tag, rank, n⟩ := lab
  subst htag
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
  obtain ⟨K, hfieldK, hfiniteK, hcardK, hQK⟩ := hraw
  obtain ⟨hsimpleK, hnaK, hθK⟩ := hQK
  obtain ⟨θK, hPK⟩ := hθK
  have hn1 : 1 ≤ n := hlab.1
  have hrank2 : 2 ≤ rank := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.2.1
  have hq3 : 3 ∣ 2 ^ n + 1 := uniLeaf_three_dvd_two_pow_add_one_of_split_twA hPK.2.1
  have hcharK : CharP K 2 := by
    refine uniLeaf_uniCharP_two_of_card_pow (k := n * 2) (by omega) ?_
    rw [hcardK, ← pow_mul]
  have hshape : UniShapeConcl (2 ^ n) (rank + 1) A J :=
    uniShape_holds K hcharK (2 ^ n) (rank + 1) hcardK hq3 (by omega)
      ⟨hsimpleK, hnaK⟩ X hcomm θK A δ J hKLocal huniq hA27 hPK.2.2
  exact ⟨⟨.twA, rank, n⟩, K, hfieldK, hfiniteK, rank + 1, rfl, hn1, hA27, rfl, by omega,
    hcardK, hq3, hmark, ⟨θK⟩, hshape⟩

private theorem uniLeaf_uniCell1
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  intro hmarkJ
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hG2, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  rcases hshape with hI | hII
  · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, -, -⟩ := hI
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkF : Nat.card F = 2 ^ (lab.n * j) := by rw [hcardF, hq]
    have hhasσ : GGHasLabel (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) :=
      CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨hJiso.trans e⟩)
        (uniLeaf_ggHasLabel_linear_two hkF)
    have hk2 : 2 ≤ lab.n * j := by
      by_contra h
      have h1 : lab.n * j ≤ 1 := by omega
      have hle : 2 ^ (lab.n * j) ≤ 2 := by
        calc 2 ^ (lab.n * j) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 := by norm_num
      rw [hkF] at h4F
      omega
    have hlabσ : LargeEvenInLambda2 (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) := by
      dsimp only [LargeEvenInLambda2]
      exact ⟨by omega, le_rfl, fun _ => hk2⟩
    exact (uniLeaf_not_ggLabelG2_of_ggLabelIso_A hG2
      (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ)).elim
  · obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
    have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
      rw [← hq]
      exact hJiso
    have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
        (J ⧸ Subgroup.center J) :=
      uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
    have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
    have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
    have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
      refine ⟨hnj1, ?_, ?_⟩
      · show 2 ≤ m - 1
        omega
      · intro h
        have hm12 : m - 1 = 2 := h
        have hm3' : m = 3 := by omega
        change 2 ≤ lab.n * j
        have hqj : 2 ^ (lab.n * j) ≠ 2 := by
          intro hq2
          apply hne
          rw [hm3']
          congr 1
          rw [hq]
          exact hq2
        by_contra hlt
        have h1 : lab.n * j = 1 := by omega
        exact hqj (by rw [h1]; norm_num)
    exact (uniLeaf_not_ggLabelG2_of_ggLabelIso_twA hG2
      (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ)).elim

private theorem uniLeaf_uniCell2
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab))
    (hZ : Subgroup.center J = ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hA2, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  rcases hshape with hI | hII
  · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, -, -⟩ := hI
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkF : Nat.card F = 2 ^ (lab.n * j) := by rw [hcardF, hq]
    have hhasσ : GGHasLabel (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) :=
      CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨hJiso.trans e⟩)
        (uniLeaf_ggHasLabel_linear_two hkF)
    have hk2 : 2 ≤ lab.n * j := by
      by_contra h
      have h1 : lab.n * j ≤ 1 := by omega
      have hle : 2 ^ (lab.n * j) ≤ 2 := by
        calc 2 ^ (lab.n * j) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 := by norm_num
      rw [hkF] at h4F
      omega
    have hlabσ : LargeEvenInLambda2 (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) := by
      dsimp only [LargeEvenInLambda2]
      exact ⟨by omega, le_rfl, fun _ => hk2⟩
    exact (uniLeaf_not_A2_of_ggLabelIso_A_one hA2
      (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ)).elim
  · obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
    have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
      rw [← hq]
      exact hJiso
    have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
        (J ⧸ Subgroup.center J) :=
      uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
    have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
    have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
    have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
      refine ⟨hnj1, ?_, ?_⟩
      · show 2 ≤ m - 1
        omega
      · intro h
        have hm12 : m - 1 = 2 := h
        have hm3' : m = 3 := by omega
        change 2 ≤ lab.n * j
        have hqj : 2 ^ (lab.n * j) ≠ 2 := by
          intro hq2
          apply hne
          rw [hm3']
          congr 1
          rw [hq]
          exact hq2
        by_contra hlt
        have h1 : lab.n * j = 1 := by omega
        exact hqj (by rw [h1]; norm_num)
    have hisoJ : GGLabelIso labJ (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) :=
      CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ
    have hm_eq : m = 3 := by
      have h := uniLeaf_rank_eq_two_of_ggLabelA2_iso_twA hA2 hisoJ
      omega
    rcases hj with hj1 | hj3
    · exfalso
      exact (hm3imp hm_eq hj1).1 hZ
    · have hN9 : N = 9 := by rw [himp3 hj3, hm_eq]
      have hrank8 : lab.rank = 8 := by omega
      have hlab_eq : lab = ⟨.twA, 8, lab.n⟩ := uniLeaf_label_eq_of_rank_twA htag hrank8
      refine uniLeaf_ggMarkingAll_of_label_eq hmark ?_
      intro lab' hlab' hiso hsplit
      rw [hlab_eq] at hiso
      have hlab' : lab' = ⟨.twA, 8, lab.n⟩ := uniLeaf_eq_of_ggLabelIso_twA_left (by omega) hiso
      subst hlab'
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hq3⟩))

private theorem uniLeaf_uniCell3
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA))
    (hZ : Subgroup.center J ≠ ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  have hA2 : GGLabelA2 labJ := hPJ.1
  rcases hshape with hI | hII
  · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, -, -⟩ := hI
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkF : Nat.card F = 2 ^ (lab.n * j) := by rw [hcardF, hq]
    have hhasσ : GGHasLabel (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) :=
      CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨hJiso.trans e⟩)
        (uniLeaf_ggHasLabel_linear_two hkF)
    have hk2 : 2 ≤ lab.n * j := by
      by_contra h
      have h1 : lab.n * j ≤ 1 := by omega
      have hle : 2 ^ (lab.n * j) ≤ 2 := by
        calc 2 ^ (lab.n * j) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
          _ = 2 := by norm_num
      rw [hkF] at h4F
      omega
    have hlabσ : LargeEvenInLambda2 (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) := by
      dsimp only [LargeEvenInLambda2]
      exact ⟨by omega, le_rfl, fun _ => hk2⟩
    exact (uniLeaf_not_A2_of_ggLabelIso_A_one hA2
      (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ)).elim
  · obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
    have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
      rw [← hq]
      exact hJiso
    have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
        (J ⧸ Subgroup.center J) :=
      uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
    have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
    have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
    have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
      refine ⟨hnj1, ?_, ?_⟩
      · show 2 ≤ m - 1
        omega
      · intro h
        have hm12 : m - 1 = 2 := h
        have hm3' : m = 3 := by omega
        change 2 ≤ lab.n * j
        have hqj : 2 ^ (lab.n * j) ≠ 2 := by
          intro hq2
          apply hne
          rw [hm3']
          congr 1
          rw [hq]
          exact hq2
        by_contra hlt
        have h1 : lab.n * j = 1 := by omega
        exact hqj (by rw [h1]; norm_num)
    have hisoJ : GGLabelIso labJ (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) :=
      CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ
    have hm_eq : m = 3 := by
      have h := uniLeaf_rank_eq_two_of_ggLabelA2_iso_twA hA2 hisoJ
      omega
    rcases hj with hj1 | hj3
    · have hNle : N ≤ 5 := (hm3imp hm_eq hj1).2.2
      have hAle : Nat.card A ≤ 3 ^ 3 := (hm3imp hm_eq hj1).2.1
      have hAcard : Nat.card A = 3 ^ 3 := le_antisymm hAle hA27
      have hNlt : m < N := himp1 hj1
      have hN45 : N = 4 ∨ N = 5 := by omega
      refine uniLeaf_ggMarkingAll_of_label_eq hmark ?_
      intro lab' hlab' hiso hsplit
      rcases hN45 with hN4 | hN5
      · have hrank3 : lab.rank = 3 := by omega
        have hlab3 : lab = ⟨.twA, 3, lab.n⟩ := uniLeaf_label_eq_of_rank_twA htag hrank3
        rw [hlab3] at hiso
        rcases uniLeaf_eq_or_twD3_of_ggLabelIso_twA3_left hiso with h | h
        · subst h; exact Or.inl ⟨rfl, rfl⟩
        · subst h; exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
      · have hrank4 : lab.rank = 4 := by omega
        have hlab4 : lab = ⟨.twA, 4, lab.n⟩ := uniLeaf_label_eq_of_rank_twA htag hrank4
        rw [hlab4] at hiso
        have hlab' : lab' = ⟨.twA, 4, lab.n⟩ := uniLeaf_eq_of_ggLabelIso_twA_left (by omega) hiso
        subst hlab'
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hq3, hAcard⟩))
    · have hN9 : N = 9 := by rw [himp3 hj3, hm_eq]
      have hrank8 : lab.rank = 8 := by omega
      have hlab8 : lab = ⟨.twA, 8, lab.n⟩ := uniLeaf_label_eq_of_rank_twA htag hrank8
      refine uniLeaf_ggMarkingAll_of_label_eq hmark ?_
      intro lab' hlab' hiso hsplit
      rw [hlab8] at hiso
      have hlab' : lab' = ⟨.twA, 8, lab.n⟩ := uniLeaf_eq_of_ggLabelIso_twA_left (by omega) hiso
      subst hlab'
      exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, hq3⟩))

private theorem uniLeaf_uniCell4
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, htJ, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  have hfalse : False := by
    rcases hshape with hI | hII
    · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, -, -⟩ := hI
      obtain ⟨hJiso⟩ := hJiso
      have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
      have hkF : Nat.card F = 2 ^ (lab.n * j) := by rw [hcardF, hq]
      have hhasσ : GGHasLabel (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) :=
        CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨hJiso.trans e⟩)
          (uniLeaf_ggHasLabel_linear_two hkF)
      have hk2 : 2 ≤ lab.n * j := by
        by_contra h
        have h1 : lab.n * j ≤ 1 := by omega
        have hle : 2 ^ (lab.n * j) ≤ 2 := by
          calc 2 ^ (lab.n * j) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
            _ = 2 := by norm_num
        rw [hkF] at h4F
        omega
      have hlabσ : LargeEvenInLambda2 (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) := by
        dsimp only [LargeEvenInLambda2]
        exact ⟨by omega, le_rfl, fun _ => hk2⟩
      exact uniLeaf_not_triD4_of_ggLabelIso_A htJ
        (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
          hhasJ hhasσ)
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
      obtain ⟨hJiso⟩ := hJiso
      have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
      have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
      have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
        rw [← hq]
        exact hJiso
      have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
          (J ⧸ Subgroup.center J) :=
        uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
      have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
      have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
      have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
        refine ⟨hnj1, ?_, ?_⟩
        · show 2 ≤ m - 1
          omega
        · intro h
          have hm12 : m - 1 = 2 := h
          have hm3' : m = 3 := by omega
          change 2 ≤ lab.n * j
          have hqj : 2 ^ (lab.n * j) ≠ 2 := by
            intro hq2
            apply hne
            rw [hm3']
            congr 1
            rw [hq]
            exact hq2
          by_contra hlt
          have h1 : lab.n * j = 1 := by omega
          exact hqj (by rw [h1]; norm_num)
      exact uniLeaf_not_triD4_of_ggLabelIso_twA htJ
        (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
          hhasJ hhasσ)
  exact hfalse.elim

private theorem uniLeaf_uniCell5
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
        (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  have htJ : labJ.tag = .D := hPJ.1
  have hrJ : labJ.rank = 4 := hPJ.2.1
  have hfalse : False := by
    rcases hshape with hI | hII
    · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, -, -⟩ := hI
      obtain ⟨hJiso⟩ := hJiso
      have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
      have hkF : Nat.card F = 2 ^ (lab.n * j) := by rw [hcardF, hq]
      have hhasσ : GGHasLabel (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) :=
        CFSG.StandardType.largeEvenRawDatum_mono (fun R' _ _ _ ⟨e⟩ => ⟨hJiso.trans e⟩)
          (uniLeaf_ggHasLabel_linear_two hkF)
      have hk2 : 2 ≤ lab.n * j := by
        by_contra h
        have h1 : lab.n * j ≤ 1 := by omega
        have hle : 2 ^ (lab.n * j) ≤ 2 := by
          calc 2 ^ (lab.n * j) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
            _ = 2 := by norm_num
        rw [hkF] at h4F
        omega
      have hlabσ : LargeEvenInLambda2 (⟨.A, 1, lab.n * j⟩ : LargeEvenLabel) := by
        dsimp only [LargeEvenInLambda2]
        exact ⟨by omega, le_rfl, fun _ => hk2⟩
      exact uniLeaf_not_D4_of_ggLabelIso_A htJ hrJ
        (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
          hhasJ hhasσ)
    · obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
      obtain ⟨hJiso⟩ := hJiso
      have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
      have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
      have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
        rw [← hq]
        exact hJiso
      have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
          (J ⧸ Subgroup.center J) :=
        uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
      have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
      have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
      have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
        refine ⟨hnj1, ?_, ?_⟩
        · show 2 ≤ m - 1
          omega
        · intro h
          have hm12 : m - 1 = 2 := h
          have hm3' : m = 3 := by omega
          change 2 ≤ lab.n * j
          have hqj : 2 ^ (lab.n * j) ≠ 2 := by
            intro hq2
            apply hne
            rw [hm3']
            congr 1
            rw [hq]
            exact hq2
          by_contra hlt
          have h1 : lab.n * j = 1 := by omega
          exact hqj (by rw [h1]; norm_num)
      exact uniLeaf_not_D4_of_ggLabelIso_twA htJ hrJ
        (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
          hhasJ hhasσ)
  exact hfalse.elim

private theorem uniLeaf_uniCell6
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 1) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)) :
    Nat.card A = 3 ^ 3 ∧
      GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
        (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, K, hfieldK, hfiniteK, N, htag, hn1, hA27, hN, hN3, hcardK, hq3, hmark, hθ,
    hshape⟩ := uniLeaf_uniFrame hd
  obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ := uniLeaf_exists_label_of_marking hmarkJ
  have htJ : labJ.tag = .A := hPJ.1
  have hrJ : labJ.rank = 1 := hPJ.2
  rcases hshape with hI | hII
  · obtain ⟨F, hfieldF, hfiniteF, j, hj, hcardF, h4F, hJiso, himp1, himp3⟩ := hI
    rcases hj with hj1 | hj3
    · exfalso
      have := himp1 hj1
      omega
    · obtain ⟨hN6, hAle⟩ := himp3 hj3
      have hAcard : Nat.card A = 3 ^ 3 := le_antisymm hAle hA27
      have hrank5 : lab.rank = 5 := by omega
      have hlab5 : lab = ⟨.twA, 5, lab.n⟩ := uniLeaf_label_eq_of_rank_twA htag hrank5
      refine ⟨hAcard, ?_⟩
      refine uniLeaf_ggMarkingAll_of_label_eq hmark ?_
      intro lab' hlab' hiso hsplit
      rw [hlab5] at hiso
      have hlab' : lab' = ⟨.twA, 5, lab.n⟩ := uniLeaf_eq_of_ggLabelIso_twA_left (by omega) hiso
      subst hlab'
      exact Or.inr ⟨rfl, rfl, hq3⟩
  · exfalso
    obtain ⟨E, hfieldE, hfiniteE, m, j, hj, hcardE, hm3, hne, hJiso, himp1, himp3, hm3imp⟩ := hII
    obtain ⟨hJiso⟩ := hJiso
    have hq : (2 ^ lab.n) ^ j = 2 ^ (lab.n * j) := (pow_mul 2 lab.n j).symm
    have hkE : Nat.card E = (2 ^ (lab.n * j)) ^ 2 := by rw [hcardE, hq]
    have hJiso' : J ⧸ Subgroup.center J ≃* PSUg m E (2 ^ (lab.n * j)) := by
      rw [← hq]
      exact hJiso
    have hhasσ : GGHasLabel (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel)
        (J ⧸ Subgroup.center J) :=
      uniLeaf_ggHasLabel_unitary (by omega) hkE hJiso'
    have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> omega
    have hnj1 : 1 ≤ lab.n * j := Nat.mul_pos hn1 hj1
    have hlabσ : LargeEvenInLambda2 (⟨.twA, m - 1, lab.n * j⟩ : LargeEvenLabel) := by
      refine ⟨hnj1, ?_, ?_⟩
      · show 2 ≤ m - 1
        omega
      · intro h
        have hm12 : m - 1 = 2 := h
        have hm3' : m = 3 := by omega
        change 2 ≤ lab.n * j
        have hqj : 2 ^ (lab.n * j) ≠ 2 := by
          intro hq2
          apply hne
          rw [hm3']
          congr 1
          rw [hq]
          exact hq2
        by_contra hlt
        have h1 : lab.n * j = 1 := by omega
        exact hqj (by rw [h1]; norm_num)
    exact uniLeaf_not_A1_of_ggLabelIso_twA htJ hrJ
      (CFSG.StandardType.ggLabelRigidInput_holds labJ _ (J ⧸ Subgroup.center J) hlabJ hlabσ
        hhasJ hhasσ)

theorem leafUni_holds
    : KnownOverSix (DatumOn (fam 1)) := by
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    exact uniLeaf_uniCell1 hd
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact uniLeaf_uniCell2 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact uniLeaf_uniCell3 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ
    exact uniLeaf_uniCell4 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkJ
    exact uniLeaf_uniCell5 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkJ
    exact uniLeaf_uniCell6 hd hmarkJ

end CFSG.StandardType.TablePThreeKG

end
