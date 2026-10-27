module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoRestTwo

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace IOneRest

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open TypeA TwoThree TableBSymp

theorem recipeLinear_iRank {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m)
    (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont} (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  have hle : ∀ X : Subgroup (MulAut (projectiveSL d K)),
      (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) → IsElemAbelian p X →
        Nat.card X ≤ p ^ (d - 1) :=
    fun X hXI hX => card_le_of_subset_conjAut hp hpK (by omega) hpd' hX hXI
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · refine ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggIRankLe_of_mulEquiv (recipeEquiv d K) hI (ggIRankLe_zero_of_card_lt fun X hXI hX => ?_)⟩
    calc Nat.card X ≤ p ^ (d - 1) := hle X hXI hX
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by omega)
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggIRankLe_of_mulEquiv (recipeEquiv d K) hI (ggIRankLe_of_card_le hle)⟩

theorem largeEvenLabelAll_iRank_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_iRank hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_iRank hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_iRank hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

variable {K : Type} [Field K] {m : ℕ}

theorem ggIRankLe_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGIRankLe p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  refine ggIRankLe_of_card_le fun X hXI hX => ?_
  have : NeZero m := ⟨by omega⟩
  obtain ⟨A, hA, hAc⟩ := exists_of_subset_inn (center_spProj_eq_bot (K := K) (m := m))
    (fun φ hφ => sp_I_subset_inn (hXI hφ)) hX
  exact hAc ▸ card_le_of_isElemAbelian_spProj hp hp2 hpq hA

theorem recipeSymplectic_iRank {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    (hl : 1 ≤ l) {Q : LargeEvenRawCont} (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l, ggTorusLift_symplectic hp hp2 hpq hl,
    ggIRankLe_symplectic hp hp2 hpq hl⟩

theorem largeEvenLabelAll_iRank_symplectic {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  have hp2 := ne_two_of_dvd_two_pow_sub_one hn hpn
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_iRank hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

theorem recipeLinear_iRank_two {d N : ℕ} (hd : 3 ≤ d) (hN : N = 2) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift 3 r R ∧ GGIRankLe 3 r R I := by
  subst hN
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  have hle : ∀ X : Subgroup (MulAut (projectiveSL d K)),
      (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) → IsElemAbelian 3 X →
        Nat.card X ≤ 3 ^ (d / 2) :=
    fun X hXI hX => card_le_pow_half hX (card_sq_le_of_subset_conjAut hK (by omega) hX hXI)
  rcases (show d ≤ 5 ∨ 6 ≤ d by omega) with hd5 | hd6
  · refine ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL (by omega))),
      ggIRankLe_of_mulEquiv (recipeEquiv d K) hI (ggIRankLe_zero_of_card_lt fun X hXI hX => ?_)⟩
    calc Nat.card X ≤ 3 ^ (d / 2) := hle X hXI hX
      _ < 3 ^ 4 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact ⟨d / 2, ggTorusLift_of_mulEquiv (recipeEquiv d K) (ggTorusLift_two hK (by omega)),
      ggIRankLe_of_mulEquiv (recipeEquiv d K) hI (ggIRankLe_of_card_le hle)⟩

theorem largeEvenLabelAll_iRank_twoThree {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGIRankLe p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hn, ht⟩ := h
  dsimp only at hn ht
  subst hn
  intro Q hQ
  rcases ht with rfl | ⟨rfl, rfl⟩
  · have hl : 2 ≤ l := by
      have h1 := hlab.2
      dsimp only at h1
      omega
    exact recipeLinear_iRank_two (d := l + 1) (by omega) (by norm_num) hQ
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    exact recipeLinear_iRank_two (d := 4) (by norm_num) (by norm_num) hQ

end IOneRest

open IOneRest

theorem largeEvenLabelAll_and_iOne {lab : LargeEvenLabel} {P P' : LargeEvenRawCont}
    (h : LargeEvenLabelAll lab P) (h' : LargeEvenLabelAll lab P') :
    LargeEvenLabelAll lab fun R _ I F => P R I F ∧ P' R I F :=
  CFSG.StandardType.largeEvenLabelAll_and h h'

theorem ggStdSubIOneProperInputOn_typeA (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGTypeALabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_and_iOne ((TypeA.largeEvenLabelAll_corFourTwo_typeA hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩) (largeEvenLabelAll_iRank_typeA hp hlab h)

theorem ggStdSubIOneProperInputOn_reflSp (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGReflSpLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ hp hlab h _ =>
    largeEvenLabelAll_and_iOne ((largeEvenLabelAll_corFourTwo_symplectic hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩) (largeEvenLabelAll_iRank_symplectic hp hlab h)

theorem ggStdSubIOneProperInputOn_twoThree (ha₀ : GGLNoncyclicInput) :
    GGStdSubIOneProperInputOn GGTwoThreeLabel :=
  ggStdSubIOneProperInputOn_of_bstarEq ha₀ fun _ _ _ hlab h _ =>
    largeEvenLabelAll_and_iOne (largeEvenLabelAll_innerDiag_twoThree hlab h)
      (largeEvenLabelAll_iRank_twoThree hlab h)

end CFSG.StandardType
