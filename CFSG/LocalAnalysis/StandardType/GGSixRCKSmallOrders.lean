module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallDefs
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MILabel
public import CFSG.LocalAnalysis.StandardType.GGReverseMarkingRaw

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open CFSG.Assembly
open CFSG.SeitzReduction.F4Pilot (statedLieAdmissible_of_lieModel card_eq_evenLieOrder
  evenLieOrder not_lieModel_twistedG2_two two_le_of_admissible_G2)
open CFSG.ComponentClassification.CatLeafProof (IsChar2LieShape lieModel_eq_of_isChar2LieShape)
open CFSG.LocalAnalysis.GLTheoremA.MI (evenLieOrder_ne_ordTits)
open CFSG.StandardType.NbrInnerMore (eq_of_markedModel_twF4)

private theorem rckOR_exists_label_of_lieModel {X : Type} [Group X] {t : StatedLieTag} {r e : ℕ}
    (h : CFSG.Blueprint.LieModel X t r 2 e) (ht : ¬ RCKSmallLieTag t) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ markTag lab = t ∧ markRank lab = r ∧
      markChar lab = 2 ∧ markDeg lab = e := by
  have hadm := CFSG.Blueprint.LieModel.admissible h
  rcases h with ⟨htc, hcl⟩ | ⟨hr0, htc, hce⟩ | ⟨hr0, htr, hrt⟩ | ⟨hr0, rfl, hsz⟩
  · obtain ⟨lab, hlab, h1, h2, h3, h4, -⟩ := exists_label_rawDatum_of_statedClassicalModel hcl
    exact ⟨lab, hlab, h1, h2, h3, h4⟩
  · obtain ⟨lab, hlab, h1, h2, h3, h4, -⟩ := exists_label_rawDatum_of_chevalleyExceptionalModel hce
    exact ⟨lab, hlab, h1, by rw [hr0]; exact h2, h3, h4⟩
  · rcases (by simpa [CFSG.Blueprint.reeTitsTags] using htr :
      t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits) with rfl | rfl | rfl
    · exact absurd hadm.2.2.2.1 (by norm_num)
    · exact absurd (Or.inr (Or.inr (Or.inl rfl))) ht
    · exact absurd (Or.inr (Or.inr (Or.inr rfl))) ht
  · exact absurd (Or.inr (Or.inl rfl)) ht

theorem false_of_lieModel_small
    {X : Type} [Group X] {t t' : StatedLieTag} {r r' e e' : ℕ}
    (h : CFSG.Blueprint.LieModel X t r 2 e) (ht : ¬ RCKSmallLieTag t)
    (h' : CFSG.Blueprint.LieModel X t' r' 2 e') (ht' : RCKSmallLieTag t') : False := by
  rcases ht' with rfl | rfl | rfl | rfl
  ·
    obtain ⟨hr', -⟩ := (statedLieAdmissible_of_lieModel h').2.2
    have hshape : IsChar2LieShape .G2 r' :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hr'⟩))))
    obtain ⟨h1, -, -⟩ := lieModel_eq_of_isChar2LieShape h' hshape h
    exact ht (Or.inl h1)
  ·
    obtain ⟨hr', -⟩ := (statedLieAdmissible_of_lieModel h').2.2
    have hshape : IsChar2LieShape .twistedB2 r' := Or.inr (Or.inr (Or.inl ⟨rfl, hr'⟩))
    obtain ⟨h1, -, -⟩ := lieModel_eq_of_isChar2LieShape h' hshape h
    exact ht (Or.inr (Or.inl h1))
  ·
    obtain ⟨hr', -, -, he3⟩ := (statedLieAdmissible_of_lieModel h').2.2
    have h'0 : CFSG.Blueprint.LieModel X .twistedF4 0 2 e' := hr' ▸ h'
    obtain ⟨⟨t0, r0, n0⟩, hlab, htag, hrank, hchar, hdeg⟩ := rckOR_exists_label_of_lieModel h ht
    have hM : MarkedModel ⟨t0, r0, n0⟩ X := by
      unfold MarkedModel
      rw [htag, hrank, hchar, hdeg]
      exact h
    obtain ⟨htag', -⟩ := eq_of_markedModel_twF4 he3 h'0 hlab hchar hM
    have ht0 : t0 = .twF4 := by simpa using htag'
    subst ht0
    have ht_eq : t = .twistedF4 := by
      rw [← htag]
      rfl
    exact ht (Or.inr (Or.inr (Or.inl ht_eq)))
  ·
    have htne : t ≠ .Tits := fun hh => ht (Or.inr (Or.inr (Or.inr hh)))
    have hcard := card_eq_evenLieOrder h
    have hcard' := card_eq_evenLieOrder h'
    refine evenLieOrder_ne_ordTits (statedLieAdmissible_of_lieModel h) htne ?_
    rw [← hcard, hcard']
    rfl

theorem false_of_card_360_small
    {X : Type} [Group X] {t' : StatedLieTag} {r' e' : ℕ}
    (h' : CFSG.Blueprint.LieModel X t' r' 2 e') (ht' : RCKSmallLieTag t')
    (h360 : Nat.card X ≤ 360) : False := by
  rcases ht' with rfl | rfl | rfl | rfl
  ·
    have he2 : 2 ≤ e' := two_le_of_admissible_G2 (statedLieAdmissible_of_lieModel h')
    have hcard : Nat.card X = ordG2 (2 ^ e') := card_eq_evenLieOrder h'
    have hq : 4 ≤ 2 ^ e' := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) he2
    have hq6 : 4096 ≤ (2 ^ e') ^ 6 := by
      calc 4096 = 4 ^ 6 := by norm_num
        _ ≤ (2 ^ e') ^ 6 := Nat.pow_le_pow_left hq 6
    have h1 : 1 ≤ (2 ^ e') ^ 6 - 1 := by omega
    have h2 : 1 ≤ (2 ^ e') ^ 2 - 1 := by
      have h16 : 16 ≤ (2 ^ e') ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ e') ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have hgt : 360 < ordG2 (2 ^ e') := by
      calc 360 < (2 ^ e') ^ 6 := lt_of_lt_of_le (by norm_num) hq6
        _ = (2 ^ e') ^ 6 * 1 * 1 := by ring
        _ ≤ (2 ^ e') ^ 6 * ((2 ^ e') ^ 6 - 1) * ((2 ^ e') ^ 2 - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
        _ = ordG2 (2 ^ e') := by rw [ordG2]
    omega
  ·
    obtain ⟨-, -, hodd, he3⟩ := (statedLieAdmissible_of_lieModel h').2.2
    have hcard : Nat.card X = ordSuzuki (2 ^ e') := card_eq_evenLieOrder h'
    have hq : 8 ≤ 2 ^ e' := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) he3
    have hq2 : 64 ≤ (2 ^ e') ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ e') ^ 2 := Nat.pow_le_pow_left hq 2
    have h1 : 65 ≤ (2 ^ e') ^ 2 + 1 := by omega
    have h2 : 7 ≤ 2 ^ e' - 1 := by omega
    have hgt : 360 < ordSuzuki (2 ^ e') := by
      calc 360 < 64 * 65 * 7 := by norm_num
        _ ≤ (2 ^ e') ^ 2 * ((2 ^ e') ^ 2 + 1) * (2 ^ e' - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul hq2 h1) h2
        _ = ordSuzuki (2 ^ e') := by rw [ordSuzuki]
    omega
  ·
    obtain ⟨-, -, hodd, he3⟩ := (statedLieAdmissible_of_lieModel h').2.2
    have hcard : Nat.card X = ordTwistedF4 (2 ^ e') := card_eq_evenLieOrder h'
    have hq : 8 ≤ 2 ^ e' := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e' := Nat.pow_le_pow_right (by norm_num) he3
    have hq12 : 2 ^ 36 ≤ (2 ^ e') ^ 12 := by
      calc 2 ^ 36 = 8 ^ 12 := by norm_num
        _ ≤ (2 ^ e') ^ 12 := Nat.pow_le_pow_left hq 12
    have h1 : 1 ≤ (2 ^ e') ^ 6 + 1 := by omega
    have h2 : 1 ≤ (2 ^ e') ^ 4 - 1 := by
      have h4096 : 4096 ≤ (2 ^ e') ^ 4 := by
        calc 4096 = 8 ^ 4 := by norm_num
          _ ≤ (2 ^ e') ^ 4 := Nat.pow_le_pow_left hq 4
      omega
    have h3 : 1 ≤ (2 ^ e') ^ 3 + 1 := by omega
    have h4 : 1 ≤ 2 ^ e' - 1 := by omega
    have hgt : 360 < ordTwistedF4 (2 ^ e') := by
      calc 360 < 2 ^ 36 := by norm_num
        _ ≤ (2 ^ e') ^ 12 := hq12
        _ = (2 ^ e') ^ 12 * 1 * 1 * 1 * 1 := by ring
        _ ≤ (2 ^ e') ^ 12 * ((2 ^ e') ^ 6 + 1) * ((2 ^ e') ^ 4 - 1) *
              ((2 ^ e') ^ 3 + 1) * (2 ^ e' - 1) :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2) h3) h4
        _ = ordTwistedF4 (2 ^ e') := by rw [ordTwistedF4]
    omega
  ·
    have hcard : Nat.card X = ordTits := card_eq_evenLieOrder h'
    have hgt : 360 < ordTits := by rw [ordTits]; norm_num
    omega

end CFSG.StandardType.RCKSmall
