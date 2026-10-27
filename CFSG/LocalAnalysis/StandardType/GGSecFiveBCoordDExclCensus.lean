module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSmallLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma coxeterMatrixA_apply {N : ℕ} (i j : Fin N) :
    CoxeterMatrix.A N i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 := rfl

theorem coxeterMatrixA_noFour {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    ∃ j, ¬ CoxeterMatrix.A N i j ∣ 4 := by
  by_cases h : (i : ℕ) + 1 < N
  · refine ⟨⟨i.val + 1, h⟩, ?_⟩
    have hne : i ≠ ⟨i.val + 1, h⟩ := by
      intro he
      have hv : (i : ℕ) = i.val + 1 := by
        simpa using congrArg Fin.val he
      omega
    have hji : (i : ℕ) + 1 = ((⟨i.val + 1, h⟩ : Fin N) : ℕ) := rfl
    rw [coxeterMatrixA_apply, if_neg hne, if_pos (Or.inr hji)]
    norm_num
  · refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
    have hne : i ≠ ⟨i.val - 1, by omega⟩ := by
      intro he
      have hv : (i : ℕ) = i.val - 1 := by
        simpa using congrArg Fin.val he
      omega
    have hji : ((⟨i.val - 1, by omega⟩ : Fin N) : ℕ) + 1 = i := by
      show i.val - 1 + 1 = i.val
      omega
    rw [coxeterMatrixA_apply, if_neg hne, if_pos (Or.inl hji)]
    norm_num

private lemma cartanD_apply_chain {N : ℕ} (i j : Fin N) (hne : i ≠ j)
    (h1 : (j : ℕ) = (i : ℕ) + 1) (h2 : (j : ℕ) + 2 < N) :
    CartanMatrix.D N i j = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  rw [if_neg hne, if_neg (by omega), if_pos ⟨h1.symm, h2⟩]

private lemma cartanD_apply_fork_left {N : ℕ} (i j : Fin N) (hne : i ≠ j)
    (h1 : (i : ℕ) + 3 = N) (h2 : (j : ℕ) + 2 = N) :
    CartanMatrix.D N i j = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  have hnot3 : ¬ ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < N) := by
    rintro ⟨hij, hj2⟩
    omega
  have hnot4 : ¬ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < N) := by
    rintro ⟨hji, hi2⟩
    omega
  rw [if_neg hne, if_neg (by omega), if_neg hnot3, if_neg hnot4,
    if_pos ⟨h1, Or.inl h2⟩]

private lemma cartanD_apply_fork_right {N : ℕ} (i j : Fin N) (hne : i ≠ j)
    (hlt : N < (i : ℕ) + 3) (h1 : (j : ℕ) + 3 = N)
    (h2 : (i : ℕ) + 2 = N ∨ (i : ℕ) + 1 = N) :
    CartanMatrix.D N i j = -1 := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  have hnot3 : ¬ ((i : ℕ) + 1 = (j : ℕ) ∧ (j : ℕ) + 2 < N) := by
    rintro ⟨hij, -⟩
    omega
  have hnot4 : ¬ ((j : ℕ) + 1 = (i : ℕ) ∧ (i : ℕ) + 2 < N) := by
    rintro ⟨hji, hi2⟩
    omega
  have hnot5 : ¬ ((i : ℕ) + 3 = N ∧ ((j : ℕ) + 2 = N ∨ (j : ℕ) + 1 = N)) := by
    rintro ⟨h, -⟩
    omega
  rw [if_neg hne, if_neg (by omega), if_neg hnot3, if_neg hnot4, if_neg hnot5,
    if_pos ⟨h1, h2⟩]

theorem ggCoxeterMatrixD_noFour {N : ℕ} (hN : 3 ≤ N) (i : Fin N) :
    ∃ j, ¬ ggCoxeterMatrixD N i j ∣ 4 := by
  by_cases h1 : (i : ℕ) + 3 < N
  · have hne : i ≠ ⟨i.val + 1, by omega⟩ := by
      intro he
      have hv : (i : ℕ) = i.val + 1 := by
        simpa using congrArg Fin.val he
      omega
    refine ⟨⟨i.val + 1, by omega⟩, ?_⟩
    have hD : CartanMatrix.D N i ⟨i.val + 1, by omega⟩ = -1 :=
      cartanD_apply_chain i ⟨i.val + 1, by omega⟩ hne rfl (by omega)
    rw [ggCoxeterMatrixD_apply, if_neg hne, if_neg (by rw [hD]; norm_num)]
    norm_num
  · by_cases h2 : (i : ℕ) + 3 = N
    · have hne : i ≠ ⟨N - 2, by omega⟩ := by
        intro he
        have hv : (i : ℕ) = N - 2 := by
          simpa using congrArg Fin.val he
        omega
      refine ⟨⟨N - 2, by omega⟩, ?_⟩
      have hD : CartanMatrix.D N i ⟨N - 2, by omega⟩ = -1 :=
        cartanD_apply_fork_left i ⟨N - 2, by omega⟩ hne (by omega)
          (by show N - 2 + 2 = N; omega)
      rw [ggCoxeterMatrixD_apply, if_neg hne, if_neg (by rw [hD]; norm_num)]
      norm_num
    · have hlt : N < (i : ℕ) + 3 := by omega
      have hne : i ≠ ⟨N - 3, by omega⟩ := by
        intro he
        have hv : (i : ℕ) = N - 3 := by
          simpa using congrArg Fin.val he
        omega
      have h2' : (i : ℕ) + 2 = N ∨ (i : ℕ) + 1 = N := by
        by_cases hi : (i : ℕ) + 2 = N
        · exact Or.inl hi
        · exact Or.inr (by omega)
      refine ⟨⟨N - 3, by omega⟩, ?_⟩
      have hD : CartanMatrix.D N i ⟨N - 3, by omega⟩ = -1 :=
        cartanD_apply_fork_right i ⟨N - 3, by omega⟩ hne hlt
          (by show N - 3 + 3 = N; omega) h2'
      rw [ggCoxeterMatrixD_apply, if_neg hne, if_neg (by rw [hD]; norm_num)]
      norm_num

theorem coxeterMatrixE₆_noFour : ∀ i : Fin 6, ∃ j, ¬ CoxeterMatrix.E₆ i j ∣ 4 := by
  intro i
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩

theorem coxeterMatrixE₇_noFour : ∀ i : Fin 7, ∃ j, ¬ CoxeterMatrix.E₇ i j ∣ 4 := by
  intro i
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩

theorem coxeterMatrixE₈_noFour : ∀ i : Fin 8, ∃ j, ¬ CoxeterMatrix.E₈ i j ∣ 4 := by
  intro i
  fin_cases i
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨6, by decide⟩

theorem coxeterMatrixF₄_noFour : ∀ i : Fin 4, ∃ j, ¬ CoxeterMatrix.F₄ i j ∣ 4 := by
  intro i
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩

theorem ggTBTorRowNoFour_of_twA {lab : LargeEvenLabel} (hn : lab.n = 1)
    (ht : lab.tag = .twA) (hr3 : 3 ≤ lab.rank) (hr5 : lab.rank ≠ 5) :
    GGTBTorRowNoFour 3 lab := by
  have hM : ggTorM lab = 3 := by norm_num [ggTorM, ht, hn]
  have h3 : 3 ∣ ggTorM lab := by rw [hM]
  by_cases hdiv : 3 ∣ lab.rank + 1
  · have hr4 : 4 ≤ lab.rank := by
      obtain ⟨k, hk⟩ := hdiv
      omega
    refine ⟨lab.rank - 1 - ggTorEnn 3 lab, ggTorM lab, lab.rank, CartanMatrix.A lab.rank,
      CoxeterMatrix.A lab.rank,
      GGTBTorRowAt.aDep (p := 3) (lab := lab) (Or.inr ht) hr4 hdiv h3 ?_, ?_⟩
    · rintro ⟨-, h5, -⟩
      exact hr5 h5
    · intro i
      exact coxeterMatrixA_noFour (by omega) i
  · refine ⟨lab.rank - ggTorEnn 3 lab, ggTorM lab, lab.rank, CartanMatrix.A lab.rank,
      CoxeterMatrix.A lab.rank,
      GGTBTorRowAt.aInd (p := 3) (lab := lab) (Or.inr ht) hdiv h3, ?_⟩
    intro i
    exact coxeterMatrixA_noFour (by omega) i

theorem ggTBTorRowNoFour_of_D_even {lab : LargeEvenLabel} (hn : lab.n = 1)
    (ht : lab.tag = .D) (he : Even lab.rank) (hr4 : 4 ≤ lab.rank) :
    GGTBTorRowNoFour 3 lab := by
  have hdvd : 3 ∣ 2 ^ lab.n + 1 := by rw [hn]; norm_num
  refine ⟨lab.rank - ggTorEnn 3 lab, ggTorMpm 3 lab, lab.rank, CartanMatrix.D lab.rank,
    ggCoxeterMatrixD lab.rank,
    GGTBTorRowAt.d (p := 3) (lab := lab) (Or.inl ⟨ht, Or.inr ⟨hdvd, he⟩⟩), ?_⟩
  intro i
  exact ggCoxeterMatrixD_noFour (by omega) i

theorem ggTBTorRowNoFour_of_twD_odd {lab : LargeEvenLabel} (hn : lab.n = 1)
    (ht : lab.tag = .twD) (ho : Odd lab.rank) (hr3 : 3 ≤ lab.rank) :
    GGTBTorRowNoFour 3 lab := by
  have hdvd : 3 ∣ 2 ^ lab.n + 1 := by rw [hn]; norm_num
  refine ⟨lab.rank - ggTorEnn 3 lab, ggTorMpm 3 lab, lab.rank, CartanMatrix.D lab.rank,
    ggCoxeterMatrixD lab.rank,
    GGTBTorRowAt.d (p := 3) (lab := lab) (Or.inr ⟨ht, hdvd, ho⟩), ?_⟩
  intro i
  exact ggCoxeterMatrixD_noFour (by omega) i

theorem ggTBTorRowNoFour_of_E7 {lab : LargeEvenLabel} (hn : lab.n = 1)
    (ht : lab.tag = .E7) : GGTBTorRowNoFour 3 lab := by
  have hdvd : 3 ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by rw [hn]; norm_num
  refine ⟨7 - ggTorEnn 3 lab, ggTorMpm 3 lab, 7, CartanMatrix.E 7, CoxeterMatrix.E₇,
    GGTBTorRowAt.e7 (p := 3) (lab := lab) ht hdvd, ?_⟩
  exact coxeterMatrixE₇_noFour

theorem ggTBTorRowNoFour_of_E8 {lab : LargeEvenLabel} (_hn : lab.n = 1)
    (ht : lab.tag = .E8) : GGTBTorRowNoFour 3 lab := by
  refine ⟨8 - ggTorEnn 3 lab, ggTorME8 lab, 8, CartanMatrix.E 8, CoxeterMatrix.E₈,
    GGTBTorRowAt.e8Three (p := 3) (lab := lab) ht rfl, ?_⟩
  exact coxeterMatrixE₈_noFour

private lemma ggTableBNbrInnerNineClassicalLabel_D_three :
    GGTableBNbrInnerNineClassicalLabel 3 (⟨.D, 3, 1⟩ : LargeEvenLabel) := by
  refine Or.inl ⟨Or.inr ⟨rfl, rfl⟩, ?_⟩
  intro j hj h3j
  have h3j' : 3 * j ≤ 4 := by simpa using h3j
  have hj1 : j = 1 := by omega
  subst j
  norm_num

private theorem odd_five_of_D {l : ℕ} (h3 : 3 ≤ l)
    (hCl : ¬ GGTableBNbrInnerNineClassicalLabel 3 (⟨.D, l, 1⟩ : LargeEvenLabel))
    (hNF : ¬ GGTBTorRowNoFour 3 (⟨.D, l, 1⟩ : LargeEvenLabel)) :
    Odd l ∧ 5 ≤ l := by
  have hlne3 : l ≠ 3 := by
    rintro rfl
    exact hCl ggTableBNbrInnerNineClassicalLabel_D_three
  have hodd : Odd l := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact hNF (ggTBTorRowNoFour_of_D_even (lab := ⟨.D, l, 1⟩) rfl rfl he
      (by simpa using (by omega : 4 ≤ l)))
  refine ⟨hodd, ?_⟩
  obtain ⟨k, hk⟩ := hodd
  omega

private theorem even_four_of_twD {l : ℕ} (h2 : 2 ≤ l) (hne2 : l ≠ 2)
    (hNF : ¬ GGTBTorRowNoFour 3 (⟨.twD, l, 1⟩ : LargeEvenLabel)) :
    Even l ∧ 4 ≤ l := by
  have h3 : 3 ≤ l := by omega
  have hodd : ¬ Odd l := by
    intro ho
    exact hNF (ggTBTorRowNoFour_of_twD_odd (lab := ⟨.twD, l, 1⟩) rfl rfl ho h3)
  have heven : Even l := Nat.not_odd_iff_even.mp hodd
  refine ⟨heven, ?_⟩
  obtain ⟨k, hk⟩ := heven
  omega

private theorem false_of_twA {l : ℕ} (h2 : 2 ≤ l) (hne2 : l ≠ 2) (hne5 : l ≠ 5)
    (hNF : ¬ GGTBTorRowNoFour 3 (⟨.twA, l, 1⟩ : LargeEvenLabel)) : False := by
  have h3 : 3 ≤ l := by omega
  exact hNF (ggTBTorRowNoFour_of_twA (lab := ⟨.twA, l, 1⟩) rfl rfl h3 hne5)

private lemma twA_rank_ne_two {l : ℕ}
    (hSm : ¬ (GGTableBNbrInnerNineSmallLabel 3 (⟨.twA, l, 1⟩ : LargeEvenLabel) ∨
      (⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .triD4 ∨
      (⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .twF4)) : l ≠ 2 := by
  rintro rfl
  exact hSm (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inr ⟨rfl, rfl⟩)))))))))

private lemma twA_rank_ne_five {l : ℕ}
    (hres : ¬ ((⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .F4 ∨
      (⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .E6 ∨
      (⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .twE6 ∨
      ((⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .twA ∧ l = 5) ∨
      ((⟨.twA, l, 1⟩ : LargeEvenLabel).tag = .twD ∧ l = 2))) : l ≠ 5 := by
  rintro rfl
  exact hres (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))

private lemma twD_rank_ne_two {l : ℕ}
    (hres : ¬ ((⟨.twD, l, 1⟩ : LargeEvenLabel).tag = .F4 ∨
      (⟨.twD, l, 1⟩ : LargeEvenLabel).tag = .E6 ∨
      (⟨.twD, l, 1⟩ : LargeEvenLabel).tag = .twE6 ∨
      ((⟨.twD, l, 1⟩ : LargeEvenLabel).tag = .twA ∧ l = 5) ∨
      ((⟨.twD, l, 1⟩ : LargeEvenLabel).tag = .twD ∧ l = 2))) : l ≠ 2 := by
  rintro rfl
  exact hres (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))

theorem ggSecFiveBCoordDExcl_census {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hQ : ¬ GGLabQFour 3 lab) (hNF : ¬ GGTBTorRowNoFour 3 lab)
    (hCl : ¬ GGTableBNbrInnerNineClassicalLabel 3 lab)
    (hSm : ¬ (GGTableBNbrInnerNineSmallLabel 3 lab ∨ lab.tag = .triD4 ∨ lab.tag = .twF4))
    (hRes : ¬ (lab.n = 1 ∧ (lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨
      (lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .twD ∧ lab.rank = 2)))) :
    lab.n = 1 ∧ ((lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C) ∨
      (lab.tag = .D ∧ Odd lab.rank ∧ 5 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ Even lab.rank ∧ 4 ≤ lab.rank)) := by
  obtain ⟨t, l, n⟩ := lab
  have hn : n = 1 := by
    have h1 : 1 ≤ n := hΛ.1
    have hq : ¬ 2 ≤ n := hQ
    omega
  subst n
  have hres : ¬ (t = .F4 ∨ t = .E6 ∨ t = .twE6 ∨ (t = .twA ∧ l = 5) ∨
      (t = .twD ∧ l = 2)) := by
    intro h
    exact hRes ⟨rfl, h⟩
  refine ⟨rfl, ?_⟩
  cases t
  · exact Or.inl (Or.inl rfl)
  · exact False.elim (false_of_twA hΛ.2.1 (twA_rank_ne_two hSm)
      (twA_rank_ne_five hres) hNF)
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inr (Or.inr rfl))
  · obtain ⟨hodd, h5⟩ := odd_five_of_D hΛ.2 hCl hNF
    exact Or.inr (Or.inl ⟨rfl, hodd, h5⟩)
  · obtain ⟨heven, h4⟩ := even_four_of_twD hΛ.2 (twD_rank_ne_two hres) hNF
    exact Or.inr (Or.inr ⟨rfl, heven, h4⟩)
  · exact False.elim (hres (Or.inr (Or.inl rfl)))
  · exact False.elim (hNF (ggTBTorRowNoFour_of_E7 (lab := ⟨.E7, l, 1⟩) rfl rfl))
  · exact False.elim (hNF (ggTBTorRowNoFour_of_E8 (lab := ⟨.E8, l, 1⟩) rfl rfl))
  · exact False.elim (hres (Or.inl rfl))
  · exact False.elim (hres (Or.inr (Or.inr (Or.inl rfl))))
  · exact False.elim (hSm (Or.inr (Or.inl rfl)))
  · exact False.elim (hSm (Or.inl (Or.inl rfl)))
  · exact False.elim (hSm (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  · exact False.elim (hSm (Or.inr (Or.inr rfl)))
  · exact False.elim (hSm (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact False.elim (hSm (Or.inl (Or.inr (Or.inl rfl))))
  · exact False.elim (hSm (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))

theorem ggSecFiveBCoordDExclRestOn_not_lambda2 :
    GGSecFiveBCoordDExclRestOn fun _ lab => ¬ LargeEvenInLambda2 lab := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  exact hP.1 hlab

theorem ggSecFiveBCoordDExclRestOn_ne_three :
    GGSecFiveBCoordDExclRestOn fun p _ => p ≠ 3 := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn4 hK y K hK𝒦 hnb r hr hrefl hsgn hM hLD
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hM
  exact hP.1 hp3

end CFSG.StandardType

end
