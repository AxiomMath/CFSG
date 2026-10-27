module

import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinShape
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoG2
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoTwA2
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJA2
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoTriD4
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJNoD4Odd
import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinJA1
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinMark

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem charP_two_of_card_pow {F : Type} [Field F] [Finite F] {k : ℕ} (hk : 1 ≤ k)
    (h : Nat.card F = 2 ^ k) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, h]
  apply Nat.mod_eq_zero_of_dvd
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨2 ^ t, by rw [pow_succ]; ring⟩

private theorem two_le_of_three_dvd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) (h : 3 ∣ 2 ^ n - 1) :
    2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  norm_num at h

private theorem label_eq_of_rank {lab : LargeEvenLabel} {r : ℕ} (htag : lab.tag = .A)
    (hrank : lab.rank = r) : lab = ⟨.A, r, lab.n⟩ := by
  cases lab
  simp_all

private def LinFrame (X : Type) [Group X] (A : Subgroup (MulAut X)) (δ : MulAut X)
    (J : Subgroup X) : Prop :=
  ∃ (lab : LargeEvenLabel) (E : Type) (_ : Field E) (_ : Finite E) (m j : ℕ),
    lab.tag = .A ∧ 1 ≤ lab.n ∧ 3 ^ 3 ≤ Nat.card A ∧
      LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) ∧
      LinJ J m E ∧ CharP E 2 ∧ 1 ≤ j ∧ j ≤ 3 ∧ Nat.card E = (2 ^ lab.n) ^ j ∧
      (j = 3 → 3 ∣ 2 ^ lab.n - 1 ∧ lab.rank + 1 = 3 * m) ∧
      (¬ 3 ∣ 2 ^ lab.n - 1 → 2 ^ lab.n = 2) ∧
      (m = 3 → (j = 1 ∧ 3 ∣ 2 ^ lab.n - 1 ∨ j = 2) → Subgroup.center J ≠ ⊥) ∧
      (m = 2 → (j = 3 → Nat.card A ≤ 3 ^ 3) ∧ (j ≠ 3 → Nat.card A < 3 ^ 3))

private theorem linFrame {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J) : LinFrame X A δ J := by
  unfold DatumOn at hd
  dsimp only [fam] at hd
  obtain ⟨hK, huniq, h27, hmarkX⟩ := hd
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmarkX
  have hmark : LargeEvenMarking X (fun l _ _ _ _ _ => l = lab) :=
    ⟨hcomm, lab, hlab, largeEvenRawDatum_mono
      (fun R _ I F hQ => by
        obtain ⟨hs, hna, hθ⟩ := hQ
        obtain ⟨θ, -⟩ := hθ
        exact ⟨hs, hna, θ, rfl⟩) hraw⟩
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, hθP⟩ := hQ
  obtain ⟨θ, hP⟩ := hθP
  have htag : lab.tag = .A := hP.1
  obtain ⟨tag, rank, n⟩ := lab
  have htagA : tag = .A := htag
  subst htagA
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨K, hfieldK, hfiniteK, hcardK, hQK⟩ := hraw
  obtain ⟨hsimpleK, hnaK, θK, hPK⟩ := hQK
  have hn1 : 1 ≤ n := hlab.1
  have hrank1 : 1 ≤ rank := by
    have h := hlab
    simp only [LargeEvenInLambda2] at h
    exact h.2.1
  have hcharK : CharP K 2 := charP_two_of_card_pow hn1 hcardK
  have hsplitK : 3 ∣ Nat.card K - 1 ∨ Nat.card K = 2 := by
    have hsplit := hPK.2.1
    rw [hcardK]
    unfold LargeEvenSplit at hsplit
    rcases hsplit with ⟨-, h3⟩ | ⟨hnt, -⟩ | ⟨ht, -⟩ | ⟨hn, -⟩
    · exact Or.inl h3
    · exact absurd trivial hnt
    · exact absurd ht (by simp)
    · exact Or.inr (by rw [hn]; norm_num)
  have hshape := linShape_holds K hcharK (rank + 1) (Nat.succ_le_succ hrank1)
    ⟨hsimpleK, hnaK⟩ hsplitK X hcomm θK A δ J hK huniq h27 hPK.2.2
  obtain ⟨E, hfieldE, hfiniteE, m, j, hm2, hm2E, hj1, hj3, hEcard, hjmN, hJiso, hj3p',
    hj2p', hm3p', hm2p'⟩ := hshape
  have hcardE : Nat.card E = (2 ^ n) ^ j := by rw [hEcard, hcardK]
  have hcharE : CharP E 2 :=
    charP_two_of_card_pow (Nat.mul_pos hn1 hj1) (by rw [hcardE, pow_mul])
  have hLinJ : LinJ J m E := ⟨hm2, hm2E, hJiso⟩
  have hj3p : j = 3 → 3 ∣ 2 ^ n - 1 ∧ rank + 1 = 3 * m := by
    intro hj
    obtain ⟨h1, h2⟩ := hj3p' hj
    exact ⟨by rw [hcardK] at h1; exact h1, h2⟩
  have hq2 : ¬ 3 ∣ 2 ^ n - 1 → 2 ^ n = 2 := by
    intro hnot
    rcases hsplitK with h | h
    · exact absurd (by rw [hcardK] at h; exact h) hnot
    · rw [← hcardK]; exact h
  have hm3p : m = 3 → (j = 1 ∧ 3 ∣ 2 ^ n - 1 ∨ j = 2) → Subgroup.center J ≠ ⊥ := by
    intro hm hh
    exact hm3p' hm (by
      rcases hh with ⟨hj, h3⟩ | h2
      · exact Or.inl ⟨hj, by rw [hcardK]; exact h3⟩
      · exact Or.inr h2)
  exact ⟨⟨.A, rank, n⟩, E, hfieldE, hfiniteE, m, j, rfl, hn1, h27, hmark, hLinJ, hcharE,
    hj1, hj3, hcardE, hj3p, hq2, hm3p, hm2p'⟩

section LinLeafCerts

private theorem linCell1
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J) :
    ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro hmarkG2
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  exact linJNoG2_holds J m E hcharE hLinJ hmarkG2

private theorem linCell2
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab))
    (hZ : Subgroup.center J = ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .A ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  obtain ⟨hcommJ, lab', hlab', hraw'⟩ := hmarkJ
  obtain ⟨R', hR', I', F', hQ'⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨hsimple', hna', hθA2⟩ := hQ'
  obtain ⟨θ', hA2⟩ := hθA2
  have hm3 : m = 3 ∧ 4 ≤ Nat.card E := by
    rcases hA2.2.2 with ⟨htagA, -⟩ | ⟨htagTwA, -⟩
    · have hmarkJA : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .A) :=
        ⟨hcommJ, lab', hlab', largeEvenRawDatum_mono
          (fun R _ I F hQ => by
            obtain ⟨hs, hna, hθ⟩ := hQ
            obtain ⟨θ, hA2'⟩ := hθ
            exact ⟨hs, hna, θ, hA2', htagA⟩) hraw'⟩
      exact linJA2_holds J m E hcharE hLinJ hmarkJA
    · have hmarkJTwA : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) :=
        ⟨hcommJ, lab', hlab', largeEvenRawDatum_mono
          (fun R _ I F hQ => by
            obtain ⟨hs, hna, hθ⟩ := hQ
            obtain ⟨θ, hA2'⟩ := hθ
            exact ⟨hs, hna, θ, hA2', htagTwA⟩) hraw'⟩
      exact absurd hmarkJTwA (linJNoTwA2_holds J m E hcharE hLinJ)
  have hj3 : j = 3 := by
    rcases Nat.lt_or_ge j 3 with hlt | hge
    · have hnot : ¬ (j = 1 ∧ 3 ∣ 2 ^ lab.n - 1 ∨ j = 2) :=
        fun hh => hm3p hm3.1 hh hZ
      have hcases : j = 1 ∨ j = 2 := by omega
      rcases hcases with h1 | h2
      · by_cases h3 : 3 ∣ 2 ^ lab.n - 1
        · exact absurd (Or.inl ⟨h1, h3⟩) hnot
        · have hq2' := hq2 h3
          have hE2 : Nat.card E = 2 := by rw [hcardE, h1, hq2']; norm_num
          omega
      · exact absurd (Or.inr h2) hnot
    · omega
  have hrank : lab.rank = 8 := by
    have h := (hj3p hj3).2
    omega
  have h3n : 3 ∣ 2 ^ lab.n - 1 := (hj3p hj3).1
  have hn2 : 2 ≤ lab.n := two_le_of_three_dvd_two_pow_sub_one hn1 h3n
  have hlab_eq : lab = ⟨.A, 8, lab.n⟩ := label_eq_of_rank htag hrank
  have hmarkX8 : LargeEvenMarking X (fun l _ _ _ _ _ => l = ⟨.A, 8, lab.n⟩) :=
    largeEvenMarking_mono (fun l R _ I F' θ h => h.trans hlab_eq) hmark
  have hAll := linMark_holds X 8 lab.n (by norm_num) hn2 hmarkX8
  exact ggMarkingAll_mono (fun lab R _ I F' θ hEq hsp => by
    rw [hEq]
    exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, h3n⟩))) hAll

private theorem linCell3
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA))
    (hZ : Subgroup.center J ≠ ⊥) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twA ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ (lab.rank = 3 ∨ lab.rank = 4)) ∨
        (lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ Nat.card A = 3 ^ 3) ∨
        (lab.tag = .twA ∧ lab.rank = 8 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  exact absurd hmarkJ (linJNoTwA2_holds J m E hcharE hLinJ)

private theorem linCell4
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  exact absurd hmarkJ (linJNoTriD4_holds J m E hcharE hLinJ)

private theorem linCell5
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n)) :
    GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
      (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twD ∧ lab.rank = 5) ∨
        (lab.tag = .D ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twD ∧ lab.rank = 7 ∧ lab.n = 1) := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  exact absurd hmarkJ (linJNoD4Odd_holds J m E hcharE hLinJ)

private theorem linCell6
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hmarkA1 : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)) :
    Nat.card A = 3 ^ 3 ∧
      GGMarkingAll (K := X) fun lab _ _ _ _ _ => LargeEvenSplit 3 lab →
        (lab.tag = .A ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
          (lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1) := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  have hm2 : m = 2 := linJA1_holds J m E hcharE hLinJ hmarkA1
  have hj3 : j = 3 := by
    by_contra hjne
    have hlt := (hm2p hm2).2 hjne
    omega
  have hcardA : Nat.card A = 3 ^ 3 := by
    have hle := (hm2p hm2).1 hj3
    omega
  refine ⟨hcardA, ?_⟩
  have hrank : lab.rank = 5 := by
    have h := (hj3p hj3).2
    omega
  have h3n : 3 ∣ 2 ^ lab.n - 1 := (hj3p hj3).1
  have hn2 : 2 ≤ lab.n := two_le_of_three_dvd_two_pow_sub_one hn1 h3n
  have hlab_eq : lab = ⟨.A, 5, lab.n⟩ := label_eq_of_rank htag hrank
  have hmarkX5 : LargeEvenMarking X (fun l _ _ _ _ _ => l = ⟨.A, 5, lab.n⟩) :=
    largeEvenMarking_mono (fun l R _ I F' θ h => h.trans hlab_eq) hmark
  have hAll := linMark_holds X 5 lab.n (by norm_num) hn2 hmarkX5
  exact ggMarkingAll_mono (fun lab R _ I F' θ hEq hsp => by
    rw [hEq]
    exact Or.inl ⟨rfl, rfl, h3n⟩) hAll

private theorem linCell7
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hcardA : Nat.card A = 3 ^ 3)
    (hmarkX : LargeEvenMarking X (fun lab _ _ _ _ _ =>
      lab.tag = .twA ∧ lab.rank = 5 ∧ 3 ∣ 2 ^ lab.n + 1))
    (hmarkA1 : LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1)) :
    ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  have hm2 : m = 2 := linJA1_holds J m E hcharE hLinJ hmarkA1
  have hj3 : j = 3 := by
    by_contra hjne
    have hlt := (hm2p hm2).2 hjne
    omega
  have hrank : lab.rank = 5 := by
    have h := (hj3p hj3).2
    omega
  have h3n : 3 ∣ 2 ^ lab.n - 1 := (hj3p hj3).1
  have hn2 : 2 ≤ lab.n := two_le_of_three_dvd_two_pow_sub_one hn1 h3n
  have hlab_eq : lab = ⟨.A, 5, lab.n⟩ := label_eq_of_rank htag hrank
  have hmarkX5 : LargeEvenMarking X (fun l _ _ _ _ _ => l = ⟨.A, 5, lab.n⟩) :=
    largeEvenMarking_mono (fun l R _ I F' θ h => h.trans hlab_eq) hmark
  have hAll := linMark_holds X 5 lab.n (by norm_num) hn2 hmarkX5
  have hfalse : False := by
    have hboth := hAll _ hmarkX
    obtain ⟨-, lab'', hlab'', hraw''⟩ := hboth
    obtain ⟨R'', hR'', I'', F'', hQ''⟩ := largeEvenRawDatum_exists hraw''
    obtain ⟨hs'', hna'', hθ''⟩ := hQ''
    obtain ⟨θ'', hP'', hEq''⟩ := hθ''
    rw [hEq''] at hP''
    exact absurd hP''.1 (by intro h; cases h)
  exact hfalse.elim

private theorem linCell8
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X} (hd : DatumOn (fam 0) X A δ J)
    (hcardA : Nat.card A = 3 ^ 3)
    (hmarkX : LargeEvenMarking X (fun lab _ _ _ _ _ =>
      lab.tag = .twA ∧ lab.rank = 4 ∧ 3 ∣ 2 ^ lab.n + 1))
    (hmarkJ : LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA))
    (hZ : Subgroup.center J ≠ ⊥) :
    ¬ ∃ U : Subgroup (MulAut X), U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U := by
  obtain ⟨lab, E, hfieldE, hfiniteE, m, j, htag, hn1, h27, hmark, hLinJ, hcharE, hj1, hj3,
    hcardE, hj3p, hq2, hm3p, hm2p⟩ := linFrame hd
  letI := hfieldE
  letI := hfiniteE
  exact absurd hmarkJ (linJNoTwA2_holds J m E hcharE hLinJ)

theorem leafLin_holds :
    LeafLin := by
  change KnownOver (DatumOn (fam 0))
  unfold KnownOver
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ hX A δ J hd
    exact linCell1 hd
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact linCell2 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ hZ
    exact linCell3 hd hmarkJ hZ
  · intro X _ _ hX A δ J hd hmarkJ
    exact linCell4 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkJ
    exact linCell5 hd hmarkJ
  · intro X _ _ hX A δ J hd hmarkA1
    exact linCell6 hd hmarkA1
  · intro X _ _ hX A δ J hd hcardA hmarkX hmarkA1
    exact linCell7 hd hcardA hmarkX hmarkA1
  · intro X _ _ hX A δ J hd hcardA hmarkX hmarkJ hZ
    exact linCell8 hd hcardA hmarkX hmarkJ hZ

end LinLeafCerts

end CFSG.StandardType.TablePThreeKG

end
