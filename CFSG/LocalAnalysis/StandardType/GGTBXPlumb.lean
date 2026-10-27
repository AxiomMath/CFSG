module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGLabel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySplitRefl
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTBTorAll : Prop :=
  GGTBTorA ∧ GGTBTorE6 ∧ GGTBTorE8 ∧ GGTBTorAInd ∧ GGTBTorC ∧ GGTBTorD ∧ GGTBTorE6Ind ∧
    GGTBTorE7 ∧ GGTBTorE8Ind ∧ GGTBTorF4 ∧ GGTBTorG2 ∧ GGTBTorRelD ∧ GGTBTorRelE6 ∧
    GGTBTorRelA5

@[expose] def GGTBTorRemaining : Prop :=
  True

theorem GGTBTorAll.remaining (_h : GGTBTorAll) : GGTBTorRemaining :=
  trivial

inductive GGTBTorRowAt (p : ℕ) (lab : LargeEvenLabel) :
    (r m N : ℕ) → Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop
  | aDep : (lab.tag = .A ∨ lab.tag = .twA) → 4 ≤ lab.rank → p ∣ lab.rank + 1 →
      p ∣ ggTorM lab → ¬ (p = 3 ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n + 1) →
      GGTBTorRowAt p lab (lab.rank - 1 - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank)
  | e6Three : lab.tag = .E6 → p = 3 → 3 ∣ ggTorM lab →
      GGTBTorRowAt p lab 5 (ggTorM lab) 6 CartanMatrix.E₆ CoxeterMatrix.E₆
  | e8Three : lab.tag = .E8 → p = 3 →
      GGTBTorRowAt p lab (8 - ggTorEnn 3 lab) (ggTorME8 lab) 8 CartanMatrix.E₈ CoxeterMatrix.E₈
  | aInd : (lab.tag = .A ∨ lab.tag = .twA) → ¬ p ∣ lab.rank + 1 → p ∣ ggTorM lab →
      GGTBTorRowAt p lab (lab.rank - ggTorEnn p lab) (ggTorM lab) lab.rank
        (CartanMatrix.A lab.rank) (CoxeterMatrix.A lab.rank)
  | c : (lab.tag = .B ∨ lab.tag = .C) → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      GGTBTorRowAt p lab (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
        (CartanMatrix.C lab.rank) (CoxeterMatrix.B lab.rank)
  | d : ((lab.tag = .D ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank))) ∨
        (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank)) →
      GGTBTorRowAt p lab (lab.rank - ggTorEnn p lab) (ggTorMpm p lab) lab.rank
        (CartanMatrix.D lab.rank) (ggCoxeterMatrixD lab.rank)
  | e6Ind : p ≠ 3 → (lab.tag = .E6 ∨ lab.tag = .twE6) → p ∣ ggTorM lab →
      GGTBTorRowAt p lab (6 - ggTorEnn p lab) (ggTorM lab) 6 (CartanMatrix.E 6) CoxeterMatrix.E₆
  | e7 : lab.tag = .E7 → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      GGTBTorRowAt p lab (7 - ggTorEnn p lab) (ggTorMpm p lab) 7 (CartanMatrix.E 7)
        CoxeterMatrix.E₇
  | e8Ind : p ≠ 3 → lab.tag = .E8 → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) →
      GGTBTorRowAt p lab (8 - ggTorEnn p lab) (ggTorMpm p lab) 8 (CartanMatrix.E 8)
        CoxeterMatrix.E₈
  | f4 : lab.tag = .F4 → p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) → ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1) →
      GGTBTorRowAt p lab (4 - ggTorEnn p lab) (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
  | g2 : lab.tag = .G2 → p ∣ 2 ^ lab.n - 1 →
      GGTBTorRowAt p lab 2 (2 ^ lab.n - 1) 2 CartanMatrix.G₂ CoxeterMatrix.G₂
  | relD : ((lab.tag = .D ∧ p ∣ 2 ^ lab.n + 1 ∧ Odd lab.rank) ∨
        (lab.tag = .twD ∧ (p ∣ 2 ^ lab.n - 1 ∨ (p ∣ 2 ^ lab.n + 1 ∧ Even lab.rank)))) →
      GGTBTorRowAt p lab (lab.rank - 1) (ggTorMpm p lab) (lab.rank - 1)
        (CartanMatrix.B (lab.rank - 1)) (CoxeterMatrix.B (lab.rank - 1))
  | relE6 : p ≠ 3 → ((lab.tag = .E6 ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n - 1)) →
      GGTBTorRowAt p lab 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄
  | relA5 : lab.rank = 5 →
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1)) →
      GGTBTorRowAt p lab 3 (ggTorMpm p lab) 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3)

@[expose] def GGTBTorCov (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
    GGTBTorRowAt p lab r m N C M

@[expose]
def GGTBTorWRows : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
    (M : CoxeterMatrix (Fin N)), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGTBTorRowAt p lab r m N C M →
        LargeEvenLabelAll lab fun R _ I _ => GGTorusTorW p r m N C M R I

@[expose]
def GGTBTorLiftRows : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
    (M : CoxeterMatrix (Fin N)), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
      GGTBTorRowAt p lab r m N C M → LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift p r R

theorem ggTBTorWRows_of_all (h : GGTBTorAll) : GGTBTorWRows := by
  obtain ⟨hA, hE6, hE8, hAI, hC, hD, hE6I, hE7, hE8I, hF4, hG2, hRD, hRE6, hRA5⟩ := h
  intro p lab r m N C M hp hp2 hlab hrow
  cases hrow with
  | aDep h1 h2 h3 h4 h5 => exact hA p hp hp2 lab hlab h1 h2 h3 h4 h5
  | e6Three h1 h2 h3 => subst h2; exact hE6 lab hlab h1 h3
  | e8Three h1 h2 => subst h2; exact hE8 lab hlab h1
  | aInd h1 h2 h3 => exact hAI p hp hp2 lab hlab h1 h2 h3
  | c h1 h2 => exact hC p hp hp2 lab hlab h1 h2
  | d h1 => exact hD p hp hp2 lab hlab h1
  | e6Ind h1 h2 h3 => exact hE6I p hp hp2 h1 lab hlab h2 h3
  | e7 h1 h2 => exact hE7 p hp hp2 lab hlab h1 h2
  | e8Ind h1 h2 h3 => exact hE8I p hp hp2 h1 lab hlab h2 h3
  | f4 h1 h2 h3 => exact hF4 p hp hp2 lab hlab h1 h2 h3
  | g2 h1 h2 => exact hG2 p hp hp2 lab hlab h1 h2
  | relD h1 => exact hRD p hp hp2 lab hlab h1
  | relE6 h1 h2 => exact hRE6 p hp hp2 h1 lab hlab h2
  | relA5 h1 h2 => exact hRA5 p hp hp2 lab hlab h1 h2

private lemma l05nPlB1_coxeter_reindex_refl {ι : Type} (M : CoxeterMatrix ι) :
    M = M.reindex (Equiv.refl ι) := by
  apply CoxeterMatrix.ext
  ext i j
  rw [CoxeterMatrix.reindex_apply]
  simp

private lemma l05nPlB1_odd_two_pow_sub_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  exact ⟨2 ^ k - 1, by omega⟩

private lemma l05nPlB1_odd_two_pow_add_one {n : ℕ} (hn : 1 ≤ n) : Odd (2 ^ n + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact ⟨2 ^ k, by omega⟩

private lemma l05nPlB1_odd_ggTorM {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorM lab) := by
  unfold ggTorM
  split_ifs with h
  · exact l05nPlB1_odd_two_pow_add_one hlab.1
  · exact l05nPlB1_odd_two_pow_sub_one hlab.1

private lemma l05nPlB1_odd_ggTorME8 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    Odd (ggTorME8 lab) := by
  unfold ggTorME8
  split_ifs with h
  · exact l05nPlB1_odd_two_pow_sub_one hlab.1
  · exact l05nPlB1_odd_two_pow_add_one hlab.1

private lemma l05nPlB1_odd_ggTorMpm {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : Odd (ggTorMpm p lab) := by
  unfold ggTorMpm
  split_ifs with h
  · exact l05nPlB1_odd_two_pow_sub_one hlab.1
  · exact l05nPlB1_odd_two_pow_add_one hlab.1

private lemma l05nPlB1_three_dvd_two_pow_sub_or_add (n : ℕ) :
    3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k + 1, ?_⟩
      rw [pow_succ]; omega
    · left
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k - 1, ?_⟩
      rw [pow_succ]; omega

private lemma l05nPlB1_three_dvd_ggTorME8 {lab : LargeEvenLabel} :
    3 ∣ ggTorME8 lab := by
  unfold ggTorME8
  split_ifs with h
  · exact h
  · rcases l05nPlB1_three_dvd_two_pow_sub_or_add lab.n with h1 | h1
    · exact absurd h1 h
    · exact h1

private lemma l05nPlB1_dvd_ggTorMpm {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1)) : p ∣ ggTorMpm p lab := by
  unfold ggTorMpm
  split_ifs with h1
  · exact h1
  · exact (hp.dvd_mul.mp h).resolve_left h1

private lemma l05nPlB1_rank_A {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∨ lab.tag = .twA) : 1 ≤ lab.rank := by
  rcases h with h | h
  · have h2 := hlab.2; rw [h] at h2; exact h2.1
  · have h2 := hlab.2; rw [h] at h2; omega

private lemma l05nPlB1_rank_BC {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .B ∨ lab.tag = .C) : 2 ≤ lab.rank := by
  rcases h with h | h
  · have h2 := hlab.2; rw [h] at h2; exact h2.1
  · have h2 := hlab.2; rw [h] at h2; exact h2.1

private lemma l05nPlB1_rank_D {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .D) : 3 ≤ lab.rank := by
  have h2 := hlab.2; rw [h] at h2; exact h2

private lemma l05nPlB1_rank_twD {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twD) : 2 ≤ lab.rank := by
  have h2 := hlab.2; rw [h] at h2; exact h2

private lemma l05nPlB1_weyl_A {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.A n) :=
  Or.inl ⟨n, Equiv.refl _, hn, Or.inl (l05nPlB1_coxeter_reindex_refl _)⟩

private lemma l05nPlB1_weyl_B {n : ℕ} (hn : 1 ≤ n) : GGIsWeylMatrix (CoxeterMatrix.B n) := by
  by_cases h1 : n = 1
  · subst h1
    have hBA : CoxeterMatrix.B 1 = CoxeterMatrix.A 1 := by
      apply CoxeterMatrix.ext
      ext i j
      fin_cases i <;> fin_cases j <;> decide
    exact Or.inl ⟨1, Equiv.refl _, le_rfl,
      Or.inl (hBA.trans (l05nPlB1_coxeter_reindex_refl _))⟩
  · have hn2 : 2 ≤ n := by omega
    exact Or.inl ⟨n, Equiv.refl _, by omega,
      Or.inr (Or.inl ⟨hn2, l05nPlB1_coxeter_reindex_refl _⟩)⟩

private lemma l05nPlB1_weyl_D {n : ℕ} (hn : 3 ≤ n) : GGIsWeylMatrix (ggCoxeterMatrixD n) := by
  by_cases h3 : n = 3
  · subst h3
    have hDA : ggCoxeterMatrixD 3 = (CoxeterMatrix.A 3).reindex (Equiv.swap 0 1) := by
      apply CoxeterMatrix.ext
      ext i j
      fin_cases i <;> fin_cases j <;> (rw [CoxeterMatrix.reindex_apply]; decide)
    exact Or.inl ⟨3, Equiv.swap 0 1, by norm_num, Or.inl hDA⟩
  · have hn4 : 4 ≤ n := by omega
    exact Or.inl ⟨n, Equiv.refl _, by omega,
      Or.inr (Or.inr ⟨hn4, l05nPlB1_coxeter_reindex_refl _⟩)⟩

private lemma l05nPlB1_weyl_E6 : GGIsWeylMatrix CoxeterMatrix.E₆ :=
  Or.inr (Or.inl ⟨Equiv.refl _, l05nPlB1_coxeter_reindex_refl _⟩)

private lemma l05nPlB1_weyl_E7 : GGIsWeylMatrix CoxeterMatrix.E₇ :=
  Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, l05nPlB1_coxeter_reindex_refl _⟩))

private lemma l05nPlB1_weyl_E8 : GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, l05nPlB1_coxeter_reindex_refl _⟩)))

private lemma l05nPlB1_weyl_F4 : GGIsWeylMatrix CoxeterMatrix.F₄ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, l05nPlB1_coxeter_reindex_refl _⟩))))

private lemma l05nPlB1_weyl_G2 : GGIsWeylMatrix CoxeterMatrix.G₂ :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Equiv.refl _, l05nPlB1_coxeter_reindex_refl _⟩))))

theorem l05nPlP1_row_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ}
    {M : CoxeterMatrix (Fin N)} (hrow : GGTBTorRowAt p lab r m N C M) :
    Odd m ∧ p ∣ m ∧ GGIsWeylMatrix M ∧ GGIntCartan M C := by
  cases hrow with
  | aDep h1 h2 h3 h4 h5 =>
      exact ⟨l05nPlB1_odd_ggTorM hlab, h4,
        l05nPlB1_weyl_A (by omega), ggIntCartan_A lab.rank⟩
  | e6Three h1 h2 h3 =>
      subst h2
      exact ⟨l05nPlB1_odd_ggTorM hlab, h3, l05nPlB1_weyl_E6, ggIntCartan_E₆⟩
  | e8Three h1 h2 =>
      subst h2
      exact ⟨l05nPlB1_odd_ggTorME8 hlab, l05nPlB1_three_dvd_ggTorME8,
        l05nPlB1_weyl_E8, ggIntCartan_E₈⟩
  | aInd h1 h2 h3 =>
      exact ⟨l05nPlB1_odd_ggTorM hlab, h3,
        l05nPlB1_weyl_A (l05nPlB1_rank_A hlab h1), ggIntCartan_A lab.rank⟩
  | c h1 h2 =>
      exact ⟨l05nPlB1_odd_ggTorMpm hlab, l05nPlB1_dvd_ggTorMpm hp h2,
        l05nPlB1_weyl_B (by have := l05nPlB1_rank_BC hlab h1; omega),
        ggIntCartan_C lab.rank⟩
  | d h1 =>
      rcases h1 with ⟨htD, h | ⟨h, _⟩⟩ | ⟨htwD, h, hodd⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_left h _),
          l05nPlB1_weyl_D (l05nPlB1_rank_D hlab htD), ggIntCartan_D lab.rank⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _),
          l05nPlB1_weyl_D (l05nPlB1_rank_D hlab htD), ggIntCartan_D lab.rank⟩
      · refine ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _), ?_,
          ggIntCartan_D lab.rank⟩
        have hr := l05nPlB1_rank_twD hlab htwD
        rcases hodd with ⟨k, hk⟩
        exact l05nPlB1_weyl_D (by omega)
  | e6Ind h1 h2 h3 =>
      exact ⟨l05nPlB1_odd_ggTorM hlab, h3, l05nPlB1_weyl_E6, ggIntCartan_E₆⟩
  | e7 h1 h2 =>
      exact ⟨l05nPlB1_odd_ggTorMpm hlab, l05nPlB1_dvd_ggTorMpm hp h2,
        l05nPlB1_weyl_E7, ggIntCartan_E₇⟩
  | e8Ind h1 h2 h3 =>
      exact ⟨l05nPlB1_odd_ggTorMpm hlab, l05nPlB1_dvd_ggTorMpm hp h3,
        l05nPlB1_weyl_E8, ggIntCartan_E₈⟩
  | f4 h1 h2 h3 =>
      exact ⟨l05nPlB1_odd_ggTorMpm hlab, l05nPlB1_dvd_ggTorMpm hp h2,
        l05nPlB1_weyl_F4, ggIntCartan_F₄⟩
  | g2 h1 h2 =>
      exact ⟨l05nPlB1_odd_two_pow_sub_one hlab.1, h2, l05nPlB1_weyl_G2, ggIntCartan_G₂⟩
  | relD h1 =>
      rcases h1 with ⟨htD, h, hodd⟩ | ⟨htwD, h | ⟨h, _⟩⟩
      · refine ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _), ?_,
          ggIntCartan_B (lab.rank - 1)⟩
        have hr := l05nPlB1_rank_D hlab htD
        exact l05nPlB1_weyl_B (by omega)
      · refine ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_left h _), ?_,
          ggIntCartan_B (lab.rank - 1)⟩
        have hr := l05nPlB1_rank_twD hlab htwD
        exact l05nPlB1_weyl_B (by omega)
      · refine ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _), ?_,
          ggIntCartan_B (lab.rank - 1)⟩
        have hr := l05nPlB1_rank_twD hlab htwD
        exact l05nPlB1_weyl_B (by omega)
  | relE6 h1 h2 =>
      rcases h2 with ⟨ht, h⟩ | ⟨ht, h⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _),
          l05nPlB1_weyl_F4, ggIntCartan_F₄⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_left h _),
          l05nPlB1_weyl_F4, ggIntCartan_F₄⟩
  | relA5 h1 h2 =>
      rcases h2 with ⟨ht, h⟩ | ⟨ht, h⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_right h _),
          l05nPlB1_weyl_B (by norm_num), ggIntCartan_C 3⟩
      · exact ⟨l05nPlB1_odd_ggTorMpm hlab,
          l05nPlB1_dvd_ggTorMpm hp (dvd_mul_of_dvd_left h _),
          l05nPlB1_weyl_B (by norm_num), ggIntCartan_C 3⟩

theorem l05nPlQ_marking_with (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (P : ∀ (_r _m N : ℕ), Matrix (Fin N) (Fin N) ℤ → CoxeterMatrix (Fin N) → Prop)
    (h : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ)
      (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m N C M ∧ P r m N C M) p Bs X) :
    ∃ (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)) (R : Type) (_ : Group R) (θ : X ⧸ Subgroup.center X ≃* R)
      (I : Set (MulAut R)) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      commutator X = ⊤ ∧ LargeEvenInLambda2 lab ∧ GGTBTorRowAt p lab r m N C M ∧ P r m N C M ∧
        (∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I) ∧ GGTorusLift p r R ∧
        GGTorusTorW p r m N C M R I ∧ GGHasLabel lab (X ⧸ Subgroup.center X) := by
  have hp : p.Prime := Fact.out
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hcov, _hnorm, _hind⟩ := hP₀
  obtain ⟨r, m, N, C, M, hrow, hP⟩ := hcov
  let P' : LargeEvenLabel → LargeEvenRawCont := fun lab' R _ I _ =>
    GGTBTorRowAt p lab' r m N C M → GGTorusTorW p r m N C M R I ∧ GGTorusLift p r R
  have hall : ∀ lab', LargeEvenInLambda2 lab' → LargeEvenLabelAll lab' (P' lab') := by
    intro lab' hlab'
    by_cases hrow' : GGTBTorRowAt p lab' r m N C M
    · have hW' := hW p lab' r m N C M hp hp2 hlab' hrow'
      have hLift' := hLift p lab' r m N C M hp hp2 hlab' hrow'
      refine ggL45_labelAll_mono (lab := lab') (largeEvenLabelAll_and hW' hLift') ?_
      intro R _ I _ h
      exact fun _ => h
    · refine ggL45_labelAll_mono (lab := lab') (P := fun _ _ _ _ => True)
        (P' := P' lab') ?_ ?_
      · exact fun Q hQ => largeEvenRawDatum_mono (fun _ _ _ _ h => ⟨h, trivial⟩) hQ
      · intro R _ I _ _ hrow''
        exact absurd hrow'' hrow'
  have hraw' := hall lab hlab _ hraw
  obtain ⟨R, _instR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw'
  obtain ⟨⟨-, -, θ, hPθ⟩, hrow_to_W⟩ := hQ
  obtain ⟨_hcov', hnorm', hind'⟩ := hPθ
  refine ⟨lab, r, m, N, C, M, R, ‹Group R›, θ, I, hnorm', hperf, hlab, hrow, hP, ?_, ?_,
    (hrow_to_W hrow).1, hHas⟩
  · intro b hb
    obtain ⟨φ, hφI, hindφ⟩ := hind' b⁻¹ (Bs.inv_mem hb)
    have hφeq : φ = ggLAut X θ ⟨b⁻¹⁻¹,
        (Subgroup.normalizer (X : Set G)).inv_mem (hnorm' (Bs.inv_mem hb))⟩ :=
      eq_ggLAut_of_induces X θ (hnorm' (Bs.inv_mem hb)) hindφ
    have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (X : Set G)).inv_mem
        (hnorm' (Bs.inv_mem hb))⟩ : Subgroup.normalizer (X : Set G)) = ⟨b, hnorm' hb⟩ :=
      Subtype.ext (inv_inv b)
    rw [hφeq, hb_eq] at hφI
    exact hφI
  · exact (hrow_to_W hrow).2

theorem l05nPlQ_marking (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (h : GGInnerDiagOnLabel GGTBTorCov p Bs X) :
    ∃ (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)) (R : Type) (_ : Group R) (θ : X ⧸ Subgroup.center X ≃* R)
      (I : Set (MulAut R)) (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      commutator X = ⊤ ∧ LargeEvenInLambda2 lab ∧ GGTBTorRowAt p lab r m N C M ∧
        (∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I) ∧ GGTorusLift p r R ∧
        GGTorusTorW p r m N C M R I := by
  obtain ⟨lab,r,m,N,C,M,R,hR,θ,I,hN,hperf,hlab,hrow,-,hBsI,hLift,hT,-⟩ :=
    l05nPlQ_marking_with hW hLift hp2 (fun _ _ _ _ _ => True) (by
      obtain ⟨hperf,lab,hlab,hraw⟩ := h
      refine ⟨hperf,lab,hlab,?_⟩
      refine largeEvenRawDatum_mono ?_ hraw
      intro R _ I _ hR
      obtain ⟨hperf,hθ,θ,⟨hcov,hnorm,hind⟩⟩ := hR
      obtain ⟨r,m,N,C,M,hrow⟩ := hcov
      exact ⟨hperf,hθ,θ,⟨⟨r,m,N,C,M,hrow,trivial⟩,hnorm,hind⟩⟩)
  exact ⟨lab,r,m,N,C,M,R,hR,θ,I,hN,hperf,hlab,hrow,hBsI,hLift,hT⟩

theorem l05nPlP3_core_L (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel GGTBTorCov p Bs L) :
    ∃ (m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N))
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      Odd m ∧ p ∣ m ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        GGTorusTorData m N C M ↥L (ggGamma L hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨_lab, _r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hBsI, hlift, hT⟩ :=
    l05nPlQ_marking hW hLift hp2 h
  have hTB := ggTorusTBGroup_of_L hH.1 hperf θ hN hBsI hlift
  have hTor := hT ↥L (ggQuotHom θ) (ggGamma L hN).range hTB
  obtain ⟨hom, hpm, hM, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩

theorem l05nPlP4_core_K (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (h : GGInnerDiagOnLabel GGTBTorCov p Bs K) :
    ∃ (m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N))
      (hN : Bs ≤ Subgroup.normalizer (K : Set G)),
      Odd m ∧ p ∣ m ∧ GGIsWeylMatrix M ∧ GGIntCartan M C ∧
        GGTorusTorData m N C M ↥K (ggGamma K hN).range := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨_lab, _r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hBsI, hlift, hT⟩ :=
    l05nPlQ_marking hW hLift hp2 h
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hTB := ggTorusTBGroup_of_nbr hH.1 hnb hperf θ hN hBsI hlift
  have hTor := hT ↥K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨hom, hpm, hM, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  exact ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩

theorem ggResXDatum_of_tbTor (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGInnerDiagOnLabel GGTBTorCov p Bs L → GGResXDatum p Bs L) ∧
        (GGInnerDiagOnLabel GGTBTorCov p Bs K → GGResXDatum p Bs K) := by
  intro G _ _ p B Bs x L D J y K hH _
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hW : GGTBTorWRows := ggTBTorWRows_of_all hT
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hH.1.2.1.2.2.2
  constructor
  · intro h
    obtain ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩ := l05nPlP3_core_L hW hLift hH h
    exact ggResXDatum_of_torData hp2 hom hpm hM hMC hBs hS hN hTor
  · intro h
    obtain ⟨m, N, C, M, hN, hom, hpm, hM, hMC, hTor⟩ := l05nPlP4_core_K hW hLift hH h
    exact ggResXDatum_of_torData hp2 hom hpm hM hMC hBs hS hN hTor

@[expose] def GGTBWeylRowRes (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTBTorCov p lab ∧ LargeEvenHalfSplit p lab True ∧ ¬ ggRowSeven p lab lab ∧
    lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der

@[expose] def GGTBXDatumResInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGInnerDiagOnLabel GGTBWeylRowRes p Bs L → GGResXDatum p Bs L) ∧
      (GGInnerDiagOnLabel GGTBWeylRowRes p Bs K → GGResXDatum p Bs K)

theorem ggResXDatum_of_cov_or_res (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hR : GGTBXDatumResInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs L →
        GGResXDatum p Bs L) ∧
      (GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∨ GGTBWeylRowRes p lab) p Bs K →
        GGResXDatum p Bs K) := by
  intro G _ _ p B Bs x L D J y K hH _
  have h1 := ggResXDatum_of_tbTor hT hLift G p B Bs x L D J y K hH
  have h2 := hR G p B Bs x L D J y K hH
  exact ⟨fun h => h.elim_or.elim h1.1 h2.1, fun h => h.elim_or.elim h1.2 h2.2⟩

theorem ggTBXDatumInput_of_res (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    (hR : GGTBXDatumResInput) :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
      (GGInnerDiagOnLabel GGTBWeylRow p Bs L → GGResXDatum p Bs L) ∧
        (GGInnerDiagOnLabel GGTBWeylRow p Bs K → GGResXDatum p Bs K) := by
  intro G _ _ p B Bs x L D J y K hH _
  have h := ggResXDatum_of_cov_or_res hT hLift hR G p B Bs x L D J y K hH
  have hmono : ∀ lab, GGTBWeylRow p lab → GGTBTorCov p lab ∨ GGTBWeylRowRes p lab := by
    intro lab hw
    by_cases hc : GGTBTorCov p lab
    · exact Or.inl hc
    · exact Or.inr ⟨hc, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩
  exact ⟨fun h' => h.1 (largeEvenMarking_mono
      (fun lab _ _ _ _ _ hP => ⟨hmono lab hP.1, hP.2⟩) h'),
    fun h' => h.2 (largeEvenMarking_mono
      (fun lab _ _ _ _ _ hP => ⟨hmono lab hP.1, hP.2⟩) h')⟩

end CFSG.StandardType
