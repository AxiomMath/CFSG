module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeKnownSix
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthMinusShapeDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthMinusShape
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniFourRank
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniLeaf
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShape
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJA1
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.Classical2



private theorem orthMinusLeaf_charP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ}
    (hk : 1 ≤ k) (h : Nat.card F = 2 ^ k) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, h]
  apply Nat.mod_eq_zero_of_dvd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨2 ^ t, by rw [pow_succ]; ring⟩

private theorem orthMinusLeaf_three_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) :
    3 ∣ 2 ^ n + 1 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hz : ((2 ^ n + 1 : ℕ) : ZMod 3) = 0 := by
    push_cast
    rw [h2]
    have hpow : ((-1 : ZMod 3) ^ n) = -1 := hn.neg_one_pow
    rw [hpow]
    decide
  exact (ZMod.natCast_eq_zero_iff (2 ^ n + 1) 3).mp hz

private theorem orthMinusLeaf_three_dvd_two_pow_sub_one {n : ℕ} (hn : Even n) :
    3 ∣ 2 ^ n - 1 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hz : ((2 ^ n - 1 : ℕ) : ZMod 3) = 0 := by
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    push_cast
    rw [h2]
    have hpow : ((-1 : ZMod 3) ^ n) = 1 := hn.neg_one_pow
    rw [hpow]
    decide
  exact (ZMod.natCast_eq_zero_iff (2 ^ n - 1) 3).mp hz

private theorem orthMinusLeaf_three_dvd_sq_two_pow_sub_one (n : ℕ) :
    3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h2 : (2 : ZMod 3) = -1 := by decide
  have hz : (((2 ^ n) ^ 2 - 1 : ℕ) : ZMod 3) = 0 := by
    have hpos : 1 ≤ (2 ^ n) ^ 2 := by
      have : 0 < (2 ^ n) ^ 2 := by positivity
      omega
    rw [Nat.cast_sub hpos]
    push_cast
    rw [h2]
    have hsquare : ((-1 : ZMod 3) ^ n) ^ 2 = 1 := by
      rw [← pow_mul]
      exact (show Even (n * 2) from ⟨n, by ring⟩).neg_one_pow
    rw [hsquare]
    decide
  exact (ZMod.natCast_eq_zero_iff ((2 ^ n) ^ 2 - 1) 3).mp hz

private def orthMinusLeaf_SymLabelShape (s : LargeEvenLabel) : Prop :=
  s.tag = .A ∨ s.tag = .twA ∨ s.tag = .B ∨ s.tag = .C ∨
    ((s.tag = .D ∨ s.tag = .twD) ∧ 4 ≤ s.rank)

private theorem orthMinusLeaf_no_g2 {s t : LargeEvenLabel} (hs : orthMinusLeaf_SymLabelShape s)
    (ht : GGLabelG2 t) (h : GGLabelIso s t) : False := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthMinusLeaf_SymLabelShape, GGLabelG2, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all

private theorem orthMinusLeaf_no_triD4 {s t : LargeEvenLabel} (hs : orthMinusLeaf_SymLabelShape s)
    (ht : t.tag = .triD4) (h : GGLabelIso s t) : False := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthMinusLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all

private theorem orthMinusLeaf_A2_shape {s t : LargeEvenLabel} (ht : GGLabelA2 t)
    (h : GGLabelIso s t) : s.rank = 2 ∧ (s.tag = .A ∨ s.tag = .twA) := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [GGLabelA2, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthMinusLeaf_twA2_shape {s t : LargeEvenLabel} (ht : GGLabelA2 t)
    (htw : t.tag = .twA) (h : GGLabelIso s t) : s.tag = .twA ∧ s.rank = 2 := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [GGLabelA2, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthMinusLeaf_eq_of_A1_shape {s t : LargeEvenLabel}
    (hs : orthMinusLeaf_SymLabelShape s) (ht : t.tag = .A) (hr : t.rank = 1)
    (h : GGLabelIso s t) : s = t := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthMinusLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthMinusLeaf_D4_of_iso {s t : LargeEvenLabel}
    (hs : orthMinusLeaf_SymLabelShape s) (ht : t.tag = .D) (hr : t.rank = 4)
    (h : GGLabelIso s t) : s = ⟨.D, 4, t.n⟩ := by
  obtain ⟨st, sr, sn⟩ := s
  obtain ⟨tt, tr, tn⟩ := t
  simp only [orthMinusLeaf_SymLabelShape, GGLabelIso] at *
  cases st <;> cases tt <;> simp_all <;> omega

private theorem orthMinusLeaf_twD_left {lab : LargeEvenLabel} {r n : ℕ} (hr : 4 ≤ r)
    (h : GGLabelIso (⟨.twD, r, n⟩ : LargeEvenLabel) lab) : lab = ⟨.twD, r, n⟩ := by
  obtain ⟨t, l, m⟩ := lab
  simp only [GGLabelIso] at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all <;> omega

private theorem orthMinusLeaf_exists_label_of_marking {K : Type} [Group K] {P : LargeEvenMarkProp K}
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

private theorem orthMinusLeaf_lab_of_eq_marking {K : Type} [Group K] {lab : LargeEvenLabel}
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

private theorem orthMinusLeaf_ggMarkingAll_of_label_eq
    {K : Type} [Group K] {lab : LargeEvenLabel}
    (hmark : LargeEvenMarking K (fun l _ _ _ _ _ => l = lab))
    {H Q : LargeEvenLabel → Prop}
    (hQ : ∀ lab', LargeEvenInLambda2 lab' → GGLabelIso lab lab' → H lab' → Q lab') :
    GGMarkingAll (K := K) (fun lab' _ _ _ _ _ => H lab' → Q lab') := by
  intro P hP
  obtain ⟨hlab, hhas⟩ := orthMinusLeaf_lab_of_eq_marking hmark
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

private theorem orthMinusLeaf_reduce
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J) :
    DatumOn (fam 1) X A δ J ∨
      (∃ (n r : ℕ), 4 ≤ r ∧ OrthMinusShapeConcl n r A J ∧
        LargeEvenMarking X (fun l _ _ _ _ _ => l = (⟨.twD, r, n⟩ : LargeEvenLabel))) := by
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hKLocal, huniq, hA27, hmarkX⟩ := hd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmarkX
  have htag : lab.tag = .twD := by
    obtain ⟨R, hR, I, F, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, hθP⟩ := hQ
    obtain ⟨θ, hP⟩ := hθP
    exact hP.1
  obtain ⟨tag, r, n⟩ := lab
  subst htag
  have hn1 : 1 ≤ n := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.1
  have hr2 : 2 ≤ r := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.2
  rcases eq_or_ne r 2 with hr2eq | hr2ne
  · subst hr2eq
    dsimp only [LargeEvenRawDatumLegacy] at hraw
    obtain ⟨K, hfieldK, hfiniteK, hcardK, hQ0⟩ := hraw
    letI := hfieldK
    letI := hfiniteK
    obtain ⟨hsimple0, hna0, hθ0⟩ := hQ0
    obtain ⟨θ0, -, hsplit0, hin0⟩ := hθ0
    have hcharK : CharP K 2 := by
      refine orthMinusLeaf_charP_two_of_card_pow (k := 2 * n) (by omega) ?_
      rw [hcardK, ← pow_mul, Nat.mul_comm]
    have hsplitK : 3 ∣ Nat.card K - 1 ∨ Nat.card K = 2 := by
      left
      rw [hcardK]
      exact orthMinusLeaf_three_dvd_sq_two_pow_sub_one n
    have hLin := linShape_holds K hcharK 2 (by norm_num) ⟨hsimple0, hna0⟩ hsplitK X hcomm θ0
      A δ J hKLocal huniq hA27 hin0
    rw [hcardK] at hLin
    obtain ⟨E, hfieldE, hfiniteE, m, j, h2m, -, hj1, -, -, hjmN, -, -, -, -, hm2p⟩ := hLin
    have hm2 : m = 2 := by nlinarith [h2m, hj1, hjmN]
    have hjne : j ≠ 3 := by
      intro hj
      subst hj
      nlinarith [h2m, hjmN]
    have hlt : Nat.card A < 3 ^ 3 := (hm2p hm2).2 hjne
    exact False.elim (absurd hA27 (by omega))
  · dsimp only [LargeEvenRawDatumLegacy] at hraw
    rw [if_neg hr2ne] at hraw
    rcases eq_or_ne r 3 with hr3eq | hr3ne
    · subst hr3eq
      rw [if_pos rfl] at hraw
      obtain ⟨K, hfieldK, hfiniteK, hcardK, hQ0⟩ := hraw
      letI := hfieldK
      letI := hfiniteK
      obtain ⟨hsimple0, hna0, hθ0⟩ := hQ0
      obtain ⟨θ0, -, -, hin0⟩ := hθ0
      by_cases hodd : Odd n
      · refine Or.inl ⟨hKLocal, huniq, hA27, hcomm, ⟨.twA, 3, n⟩, ?_, ?_⟩
        · simp only [LargeEvenInLambda2]
          exact ⟨hn1, by norm_num, by simp⟩
        · dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary]
          refine ⟨K, hfieldK, hfiniteK, hcardK, ?_⟩
          refine ⟨hsimple0, hna0, θ0, rfl, ?_, hin0⟩
          simp only [LargeEvenSplit, LargeEvenUntwisted]
          exact Or.inr (Or.inl ⟨by simp, by decide, orthMinusLeaf_three_dvd_two_pow_add_one hodd⟩)
      · have heven : Even n := by
          rcases Nat.even_or_odd n with h | h
          · exact h
          · exact absurd h hodd
        have hq3 : 3 ∣ 2 ^ n - 1 := orthMinusLeaf_three_dvd_two_pow_sub_one heven
        have hcharK : CharP K 2 := by
          refine orthMinusLeaf_charP_two_of_card_pow (k := 2 * n) (by omega) ?_
          rw [hcardK, ← pow_mul, Nat.mul_comm]
        have hinj : Function.Injective (ggInducedAut θ0) :=
          CFSG.StandardType.ggInducedAut_injective_of_perfect hcomm θ0
        let Ā : Subgroup (MulAut (PSUg 4 K (2 ^ n))) := A.map (ggInducedAut θ0)
        have hĀe : IsElemAbelian 3 Ā := CFSG.Open.IsElemAbelian.map hKLocal.1.1 (ggInducedAut θ0)
        have hĀI : ∀ a ∈ Ā, a ∈ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (LargeEvenGUSet (Fin 4) K (2 ^ n)) := by
          intro a ha
          obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
          exact hin0 a₀ ha₀
        have hle : Nat.card Ā ≤ 3 ^ 2 :=
          uni_four_rank_of_dvd_sub_one (K := K) (q := 2 ^ n) hcardK hq3 hĀe hĀI
        have hcardĀ : Nat.card Ā = Nat.card A := Subgroup.card_map_of_injective hinj
        have hleA : Nat.card A ≤ 3 ^ 2 := by rwa [hcardĀ] at hle
        exact False.elim (absurd hA27 (by omega))
    · rw [if_neg hr3ne] at hraw
      obtain ⟨K, hfieldK, hfiniteK, hcardK, b, c, hbc, hQ0⟩ := hraw
      letI := hfieldK
      letI := hfiniteK
      obtain ⟨hsimple0, hna0, hθ0⟩ := hQ0
      obtain ⟨θ0, -, -, hin0⟩ := hθ0
      have hr4 : 4 ≤ r := by omega
      have hcharK : CharP K 2 := orthMinusLeaf_charP_two_of_card_pow hn1 hcardK
      have hOrth : OrthMinusShapeConcl n r A J :=
        orthMinusShape_holds K hcharK n r hcardK hr4 b c hbc ⟨hsimple0, hna0⟩ X hcomm θ0
          A δ J hKLocal huniq hA27 hin0
      have hmark : LargeEvenMarking X (fun l _ _ _ _ _ => l = (⟨.twD, r, n⟩ : LargeEvenLabel)) := by
        refine ⟨hcomm, ⟨.twD, r, n⟩, hlab, ?_⟩
        dsimp only [LargeEvenRawDatumLegacy]
        rw [if_neg hr2ne, if_neg hr3ne]
        exact ⟨K, hfieldK, hfiniteK, hcardK, b, c, hbc, hsimple0, hna0, θ0, rfl⟩
      exact Or.inr ⟨n, r, hr4, hOrth, hmark⟩

private theorem orthMinusLeaf_cell1
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro hmarkJ
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.1 X hcomm A δ J hfam1 hmarkJ
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    have hs : orthMinusLeaf_SymLabelShape s := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl htwA)
      · exact Or.inr (Or.inr (Or.inl hB))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, hr⟩)))
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hG2, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkJ
    exact orthMinusLeaf_no_g2 hs hG2
      (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ)


private theorem orthMinusLeaf_cell2
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab))
    (hZ : Subgroup.center J = ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.2.1 X hcomm A δ J hfam1 hmarkJ hZ
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hA2, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkJ
    have hiso : GGLabelIso s labJ :=
      CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ
    rcases orthMinusLeaf_A2_shape hA2 hiso with ⟨hrank2, hAtag | htwtag⟩
    · rcases hdisj with ⟨hA, hintA⟩ | ⟨htwA, himp⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · exact False.elim (hintA.2 hrank2 hZ)
      · rw [hAtag] at htwA; exact False.elim (absurd htwA (by decide))
      · rw [hAtag] at hB; exact False.elim (absurd hB (by decide))
      · rw [hAtag] at hC; exact False.elim (absurd hC (by decide))
      · rcases hD with hD | hD <;> rw [hAtag] at hD <;> exact False.elim (absurd hD (by decide))
    · rcases hdisj with ⟨hA, hintA⟩ | ⟨htwA, himp⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · rw [htwtag] at hA; exact False.elim (absurd hA (by decide))
      · exact False.elim ((himp hrank2).1 hZ)
      · rw [htwtag] at hB; exact False.elim (absurd hB (by decide))
      · rw [htwtag] at hC; exact False.elim (absurd hC (by decide))
      · rcases hD with hD | hD <;> rw [htwtag] at hD <;> exact False.elim (absurd hD (by decide))


private theorem orthMinusLeaf_cell3
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA))
    (hZ : Subgroup.center J ≠ ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.2.2.1 X hcomm A δ J hfam1 hmarkJ hZ
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkJ
    have hA2 : GGLabelA2 labJ := hPJ.1
    have htw : labJ.tag = .twA := hPJ.2
    have hiso : GGLabelIso s labJ :=
      CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ
    obtain ⟨hst, hrank2⟩ := orthMinusLeaf_twA2_shape hA2 htw hiso
    have hrle4 : r ≤ 4 := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htwA, himp⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · rw [hst] at hA; exact absurd hA (by decide)
      · exact (himp hrank2).2
      · rw [hst] at hB; exact absurd hB (by decide)
      · rw [hst] at hC; exact absurd hC (by decide)
      · rcases hD with hD | hD <;> rw [hst] at hD <;> exact absurd hD (by decide)
    have hr4eq : r = 4 := le_antisymm hrle4 hr4
    subst hr4eq
    refine orthMinusLeaf_ggMarkingAll_of_label_eq
      (lab := (⟨.twD, 4, n⟩ : LargeEvenLabel)) hmark ?_
    intro lab' hlab' hiso' hsplit'
    have heq : lab' = (⟨.twD, 4, n⟩ : LargeEvenLabel) :=
      orthMinusLeaf_twD_left (by norm_num) hiso'
    subst heq
    exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)


private theorem orthMinusLeaf_cell4
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.2.2.2.1 X hcomm A δ J hfam1 hmarkJ
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    have hs : orthMinusLeaf_SymLabelShape s := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl htwA)
      · exact Or.inr (Or.inr (Or.inl hB))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, hr⟩)))
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, htagTri, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkJ
    exact (orthMinusLeaf_no_triD4 hs htagTri
      (CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ)).elim


private theorem orthMinusLeaf_cell5
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
        (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.2.2.2.2.1 X hcomm A δ J hfam1 hmarkJ
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    have hs : orthMinusLeaf_SymLabelShape s := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl htwA)
      · exact Or.inr (Or.inr (Or.inl hB))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, hr⟩)))
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkJ
    obtain ⟨htD, hrD, hoddJ⟩ := hPJ
    have hiso : GGLabelIso s labJ :=
      CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ
    have hseq : s = (⟨.D, 4, labJ.n⟩ : LargeEvenLabel) := orthMinusLeaf_D4_of_iso hs htD hrD hiso
    have hstag : s.tag = .D := by rw [hseq]
    rcases hdisj with ⟨hA, -⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, hr4s, hsn, hD6⟩
    · rw [hstag] at hA; exact absurd hA (by decide)
    · rw [hstag] at htwA; exact absurd htwA (by decide)
    · rw [hstag] at hB; exact absurd hB (by decide)
    · rw [hstag] at hC; exact absurd hC (by decide)
    · have htn : labJ.n = n := by rw [hseq] at hsn; exact hsn
      have hnodd : Odd n := by rw [← htn]; exact hoddJ
      have hsr4 : s.rank = 4 := by rw [hseq]
      have hres := hD6 hstag hsr4 hnodd
      rcases hres with hr5 | ⟨hr7, hn1⟩
      · subst hr5
        refine orthMinusLeaf_ggMarkingAll_of_label_eq
          (lab := (⟨.twD, 5, n⟩ : LargeEvenLabel)) hmark ?_
        intro lab' hlab' hiso' hsplit'
        have heq : lab' = (⟨.twD, 5, n⟩ : LargeEvenLabel) :=
          orthMinusLeaf_twD_left (by norm_num) hiso'
        subst heq
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · subst hr7
        subst hn1
        refine orthMinusLeaf_ggMarkingAll_of_label_eq
          (lab := (⟨.twD, 7, 1⟩ : LargeEvenLabel)) hmark ?_
        intro lab' hlab' hiso' hsplit'
        have heq : lab' = (⟨.twD, 7, 1⟩ : LargeEvenLabel) :=
          orthMinusLeaf_twD_left (by norm_num) hiso'
        subst heq
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))


private theorem orthMinusLeaf_cell6
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hd : DatumOn (fam 4) X A δ J)
    (hmarkA1 : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)) :
    Nat.card A = 3 ^ 3 ∧
      GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
        (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  have hA27 : 3 ^ 3 ≤ Nat.card A := by
    rcases hd with ⟨-, -, hA27, -⟩
    exact hA27
  have hcomm : commutator X = ⊤ := by
    rcases hd with ⟨-, -, -, hmarkX⟩
    exact hmarkX.1
  rcases orthMinusLeaf_reduce (δ := δ) hd with hfam1 | ⟨n, r, hr4, hshape, hmark⟩
  · exact leafUni_holds.2.2.2.2.2 X hcomm A δ J hfam1 hmarkA1
  · obtain ⟨s, hlabS, hhasS, hdisj⟩ := hshape
    have hs : orthMinusLeaf_SymLabelShape s := by
      rcases hdisj with ⟨hA, -⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, hr, -, -⟩
      · exact Or.inl hA
      · exact Or.inr (Or.inl htwA)
      · exact Or.inr (Or.inr (Or.inl hB))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hC)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hD, hr⟩)))
    obtain ⟨labJ, R, hR, I, F, θJ, hlabJ, hPJ, hhasJ⟩ :=
      orthMinusLeaf_exists_label_of_marking hmarkA1
    have htagA : labJ.tag = .A := hPJ.1
    have hrankA : labJ.rank = 1 := hPJ.2
    have hiso : GGLabelIso s labJ :=
      CFSG.StandardType.ggLabelRigidInput_holds s labJ (J ⧸ Subgroup.center J) hlabS hlabJ
        hhasS hhasJ
    have hst : s = labJ := orthMinusLeaf_eq_of_A1_shape hs htagA hrankA hiso
    exfalso
    rcases hdisj with ⟨hA, hintA⟩ | ⟨htwA, -⟩ | hB | hC | ⟨hD, -, -, -⟩
    · have hle : Nat.card A ≤ 3 ^ 2 := hintA.1 (by rw [hst]; exact hrankA)
      omega
    · rw [hst] at htwA; rw [htagA] at htwA; exact absurd htwA (by decide)
    · rw [hst] at hB; rw [htagA] at hB; exact absurd hB (by decide)
    · rw [hst] at hC; rw [htagA] at hC; exact absurd hC (by decide)
    · rcases hD with hD | hD <;> rw [hst] at hD <;> rw [htagA] at hD <;>
        exact absurd hD (by decide)


theorem leafOrthMinus_holds
    : KnownOverSix (DatumOn (fam 4)) := by
  unfold KnownOverSix
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    exact orthMinusLeaf_cell1 hd
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact orthMinusLeaf_cell2 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact orthMinusLeaf_cell3 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ
    exact orthMinusLeaf_cell4 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkJ
    exact orthMinusLeaf_cell5 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkA1
    exact orthMinusLeaf_cell6 hd hmarkA1

end CFSG.StandardType.TablePThreeKG

end
