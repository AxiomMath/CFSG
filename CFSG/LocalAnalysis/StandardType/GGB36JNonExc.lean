module

public import CFSG.LocalAnalysis.StandardType.GGB36Final
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ltqNc_three_dvd_two_pow (n : ℕ) :
    3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hne : 2 ^ n % 3 ≠ 0 := by
    intro h0
    have hd : 3 ∣ 2 ^ n := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hd2 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hd
    have := Nat.le_of_dvd (by norm_num) hd2
    omega
  have hlt : 2 ^ n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hcase : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by omega
  rcases hcase with hc | hc
  · left
    refine ⟨2 ^ n / 3, ?_⟩
    have h := Nat.div_add_mod (2 ^ n) 3
    omega
  · right
    refine ⟨2 ^ n / 3 + 1, ?_⟩
    have h := Nat.div_add_mod (2 ^ n) 3
    omega

private theorem ltqNc_labelIso_tag_eq {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (ht : lab.tag = .triD4 ∨ lab.tag = .G2 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) : lab'.tag = lab.tag := by
  rcases h with h | h | h | h | h | h | h | h
  · rw [h]
  · exfalso
    rcases h.1 with hb | hc
    · rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [hb] at h1 <;>
        exact absurd h1 (by decide)
    · rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [hc] at h1 <;>
        exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.1] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)
  · exfalso
    rcases ht with h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h.2] at h1 <;>
      dsimp only at h1 <;> exact absurd h1 (by decide)

private theorem ltqNc_twF4der_eq {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (ht : lab.tag = .twF4der) : lab = ⟨.twF4der, 0, 1⟩ := by
  obtain ⟨t, l, n⟩ := lab
  obtain rfl : t = .twF4der := ht
  obtain ⟨-, hl, hn⟩ := hlab
  subst hl
  subst hn
  rfl

private theorem ltqNc_twF4der_labelAll :
    LargeEvenLabelAll ⟨.twF4der, 0, 1⟩ fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → ∀ X : Subgroup (MulAut R),
        (X : Set (MulAut R)) ⊆ I → IsElemAbelian 3 X → Nat.card X < 3 ^ 4 := by
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro _ _ X hXI hX
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hm : CFSG.Blueprint.ReeTitsModel (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) .Tits 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩, 0, rfl, reeTitsRelationModel_largeEven 0 hK⟩
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have : Finite (LargeEvenCenterQuot (LargeEvenTwF4H 0 K)) := Finite.of_equiv _ e.symm.toEquiv
  have : Finite CFSG.Sporadic.Schreier.Tits.titsD :=
    Nat.finite_of_card_ne_zero fun h => by
      have hd := NbrInnerNine.card_titsD_dvd
      rw [h] at hd
      norm_num at hd
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK2
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanF4)
    (LargeEvenTwF4H 0 K)
  refine TableBExcSmallRest.card_lt_of_subset_inn
    (TableBExcSmallRest.center_eq_bot_of_mulEquiv e
      CFSG.Sporadic.Schreier.Tits.titsD_center)
    (fun A hA => TableBExcSmallRest.card_lt_of_mulEquiv e (fun E hE =>
      NbrInnerNine.card_lt_of_not_pow_dvd (p := 3) (k := 4) Nat.prime_three (fun h => ?_) hE)
      hA)
    (fun φ hφ => hI (hXI hφ)) hX
  · have h' : 3 ^ 4 ∣ 35942400 := h.trans NbrInnerNine.card_titsD_dvd
    norm_num at h'

private theorem ltqNc_not_marking_of_labelAll_card_lt {X : Type} [Group X] {p k : ℕ}
    {S : LargeEvenLabel → Prop}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab fun R _ I _ =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ E : Subgroup (MulAut R),
        (E : Set (MulAut R)) ⊆ I → IsElemAbelian p E → Nat.card E < p ^ k) :
    ¬ LargeEvenMarking X (fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ k ≤ Nat.card E) := by
  intro h
  obtain ⟨-, lab, -, hraw⟩ := largeEvenMarking_and_labelAll hall
    (fun _ _ _ _ _ _ hP => hP.1) h
  obtain ⟨R, _, I, _, hs, hna, _, ⟨-, E, hEI, hE, hk⟩, hlt⟩ := largeEvenRawDatum_exists hraw
  exact (hlt hs hna E hEI hE).not_ge hk

private theorem ltqNc_false_of_bound
    {X : Type} [Group X] [Finite X] {p n k : ℕ} {A Ab : Subgroup (MulAut X)} {σ : MulAut X}
    {J : Subgroup X} {S : LargeEvenLabel → Prop} {labX : LargeEvenLabel}
    (hbound : ¬ LargeEvenMarking X fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ k ≤ Nat.card E)
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) (hBig : p ^ k ≤ Nat.card A)
    (hΛX : LargeEvenInLambda2 labX) (hhX : GGHasLabel labX (X ⧸ Subgroup.center X))
    (hS_of_iso : ∀ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' →
      GGLabelIso labX lab' → S lab') : False := by
  obtain ⟨hlocCore, -, -, -, -, -, -, hmarked⟩ := hd.1
  obtain ⟨hcomm, lab', hlab', hraw⟩ := hmarked
  have hHasLabel_lab' : GGHasLabel lab' (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso : GGLabelIso labX lab' :=
    ggLabelRigidInput_holds labX lab' (X ⧸ Subgroup.center X) hΛX hlab' hhX hHasLabel_lab'
  have hS : S lab' := hS_of_iso lab' hlab' hiso
  have hrawE : LargeEvenRawDatum lab' fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : X ⧸ Subgroup.center X ≃* R,
        (True ∧ LargeEvenHalfSplit p lab' (Subgroup.center X = ⊥) ∧ GGInducedInn A θ I) ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
          p ^ k ≤ Nat.card E := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    refine ⟨hs, hna, θ, hP, ?_⟩
    refine ⟨A.map (ggInducedAut θ), ?_, ?_, ?_⟩
    · rintro x hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hP.2.2 a ha
    · exact CFSG.Open.IsElemAbelian.map hlocCore.1 (ggInducedAut θ)
    · rw [Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hcomm θ)]
      exact hBig
  have key : LargeEvenMarking X fun lab R _ I _ _ => S lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
        p ^ k ≤ Nat.card E :=
    ⟨hcomm, lab', hlab', largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hP, hE⟩ =>
      ⟨hs, hna, θ, hS, hE⟩) hrawE⟩
  exact hbound key

@[expose] def GGB36JClassicalRK : Prop :=
  GGTablePKnownRK fun p n labJ labX => GGRegimeB36J p n labJ labX ∧
    (labX.tag = .A ∨ labX.tag = .twA ∨ labX.tag = .B ∨ labX.tag = .C ∨ labX.tag = .D ∨ labX.tag = .twD)

private theorem ltqNc_big_three {X : Type} [Group X] [Finite X] {p n : ℕ}
    {A Ab : Subgroup (MulAut X)} {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB p n (fun _ _ => True) A Ab σ J) : p ^ 3 ≤ Nat.card A := by
  obtain ⟨-, hflat, hAb3, -, -, -, -, -⟩ := hd.1
  exact hAb3.trans (Nat.card_le_card_of_injective (Subgroup.inclusion hflat.1)
    (Subgroup.inclusion_injective hflat.1))

private theorem ltqNc_big_four {X : Type} [Group X] [Finite X] {A Ab : Subgroup (MulAut X)}
    {σ : MulAut X} {J : Subgroup X}
    (hd : GGTPNDatumB 3 (3 ^ 6) (fun _ _ => True) A Ab σ J) : 3 ^ 4 ≤ Nat.card A := by
  obtain ⟨-, hflat, -, -, hnum, -, -, -⟩ := hd.1
  have hAb4 : 3 ^ 4 ≤ Nat.card Ab := by
    have h : 3 ^ 2 * 3 ^ 4 ≤ 3 ^ 2 * Nat.card Ab := by
      calc 3 ^ 2 * 3 ^ 4 = 3 ^ 6 := by norm_num
        _ ≤ 3 ^ 2 * Nat.card Ab := hnum.2
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  exact hAb4.trans (Nat.card_le_card_of_injective (Subgroup.inclusion hflat.1)
    (Subgroup.inclusion_injective hflat.1))

theorem ggTablePKnownRK_b36J_nonClassical :
    GGTablePKnownRK fun p n labJ labX => GGRegimeB36J p n labJ labX ∧
      (labX.tag = .triD4 ∨ labX.tag = .G2 ∨ labX.tag = .twB2 ∨ labX.tag = .twF4 ∨ labX.tag = .B2der ∨
        labX.tag = .G2der ∨ labX.tag = .twF4der) := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨hp3, hn, -, -, -⟩ := hr.1
  subst hp3
  subst hn
  have htagX := hr.2
  exfalso
  rcases hr.2 with h | h | h | h | h | h | h
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab =>
        lab.tag = .triD4 ∧ (3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1))
      (ggInndiag_pRank_le_two_triD4 (X := X) Nat.prime_three) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => ⟨by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h],
        ltqNc_three_dvd_two_pow lab'.n⟩)
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab => lab.tag = .G2)
      (ggInndiag_pRank_le_two_G2 (X := X) Nat.prime_three (by norm_num)) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h])
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab => lab.tag = .twB2)
      (ggInndiag_pRank_le_two_twB2 (X := X) Nat.prime_three (by norm_num)) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h])
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab =>
        lab.tag = .twF4 ∧ (3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1))
      (ggInndiag_pRank_le_two_twF4 (X := X) Nat.prime_three (by norm_num)) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => ⟨by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h],
        ltqNc_three_dvd_two_pow lab'.n⟩)
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab => lab.tag = .B2der)
      (ggInndiag_pRank_le_two_B2der (X := X) Nat.prime_three (by norm_num)) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h])
  · exact ltqNc_false_of_bound (p := 3) (k := 3) (S := fun lab => lab.tag = .G2der)
      (ggInndiag_pRank_le_two_G2der (X := X) Nat.prime_three (by norm_num)) hd
      (ltqNc_big_three hd) hΛX hhX
      (fun lab' _ hiso => by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h])
  · exact ltqNc_false_of_bound (p := 3) (k := 4) (S := fun lab => lab.tag = .twF4der)
      (ltqNc_not_marking_of_labelAll_card_lt (p := 3) (k := 4)
        (S := fun lab => lab.tag = .twF4der)
        (fun lab hlab htlab => by
          rw [ltqNc_twF4der_eq hlab htlab]
          exact ltqNc_twF4der_labelAll))
      hd (ltqNc_big_four hd) hΛX hhX
      (fun lab' _ hiso => by
        rw [ltqNc_labelIso_tag_eq hiso htagX, h])

theorem ggB36JNonExcRK_of_classical
    (h : GGB36JClassicalRK) : GGB36JNonExcRK := by
  refine GGTablePKnownRK.mono
    (GGTablePKnownRK.union h ggTablePKnownRK_b36J_nonClassical) ?_
  intro p n labJ labX hR
  obtain ⟨hreg, hnot⟩ := hR
  obtain ⟨t, r, e⟩ := labX
  have htag : (t = .A ∨ t = .twA ∨ t = .B ∨ t = .C ∨ t = .D ∨ t = .twD) ∨
      (t = .triD4 ∨ t = .G2 ∨ t = .twB2 ∨ t = .twF4 ∨ t = .B2der ∨ t = .G2der ∨
        t = .twF4der) := by
    revert hnot
    cases t <;> simp_all
  rcases htag with hc | hn
  · exact Or.inl ⟨hreg, hc⟩
  · exact Or.inr ⟨hreg, hn⟩

end CFSG.StandardType

end
