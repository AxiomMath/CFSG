module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsH
public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.OddTranspositions.PartTwoSec6
import CFSG.LocalAnalysis.WeakClosure81.W16Gt2KFactsJ

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

private theorem unitaryClass_indep_of_herm_ne_zero {m : ℕ} {c a : Fin m → F}
    (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (hca : herm (unitaryInvolution F 2 n) c a ≠ 0) :
    ∀ α β : F, α • c + β • a = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hca (herm_zero_left _ a)
  have hβ : β = 0 := by
    by_contra hβ
    apply hca
    have ha : a = (-(β⁻¹ * α)) • c := by
      have h2 : a = β⁻¹ • (β • a) := (inv_smul_smul₀ hβ a).symm
      have h3 : β • a = -(α • c) := eq_neg_of_add_eq_zero_right h
      rw [h2, h3, smul_neg, smul_smul]
      module
    rw [ha, herm_smul_right, hc, mul_zero]
  subst hβ
  have hα : α • c = 0 := by simpa using h
  rcases smul_eq_zero.mp hα with h | h
  · exact ⟨h, rfl⟩
  · exact absurd h hc0

private theorem unitaryClass_suTv_mul_smul_apply (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c a : Fin m → F} (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (ha : herm (unitaryInvolution F 2 n) a a = 0) {s t : F}
    (hs : s + unitaryInvolution F 2 n s = 0) (ht : t + unitaryInvolution F 2 n t = 0) :
    (suTv (isUnitaryInvolution_unitaryInvolution hF) a t *
        suTv (isUnitaryInvolution_unitaryInvolution hF) c s) • c =
      c + (t * herm (unitaryInvolution F 2 n) a c) • a ∧
    (suTv (isUnitaryInvolution_unitaryInvolution hF) c s *
        suTv (isUnitaryInvolution_unitaryInvolution hF) a t) • c =
      (1 + s * t * herm (unitaryInvolution F 2 n) a c *
        herm (unitaryInvolution F 2 n) c a) • c +
      (t * herm (unitaryInvolution F 2 n) a c) • a := by
  constructor
  · rw [mul_smul, suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hc hs,
      suTv_smul (isUnitaryInvolution_unitaryInvolution hF) ha ht]
    simp only [herm_add_right, herm_smul_right, hc, mul_zero, zero_smul, add_zero]
  · rw [mul_smul, suTv_smul (isUnitaryInvolution_unitaryInvolution hF) ha ht,
      suTv_smul (isUnitaryInvolution_unitaryInvolution hF) hc hs]
    simp only [herm_add_right, herm_smul_right, hc, mul_zero, zero_smul, add_zero]
    module

private theorem unitaryClass_coeff_contradiction (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c a : Fin m → F} (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (hca : herm (unitaryInvolution F 2 n) c a ≠ 0) {s t : F} (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (u : Fˣ)
    (heqc : c + (t * herm (unitaryInvolution F 2 n) a c) • a =
      (u : F) • ((1 + s * t * herm (unitaryInvolution F 2 n) a c *
        herm (unitaryInvolution F 2 n) c a) • c +
        (t * herm (unitaryInvolution F 2 n) a c) • a)) : False := by
  rw [smul_add, smul_smul, smul_smul] at heqc
  have hzero : (1 - (u : F) * (1 + s * t * herm (unitaryInvolution F 2 n) a c *
        herm (unitaryInvolution F 2 n) c a)) • c +
      (t * herm (unitaryInvolution F 2 n) a c -
        (u : F) * (t * herm (unitaryInvolution F 2 n) a c)) • a = 0 := by
    linear_combination (norm := module) heqc
  obtain ⟨hα, hβ⟩ := unitaryClass_indep_of_herm_ne_zero hc hca _ _ hzero
  have hac : herm (unitaryInvolution F 2 n) a c ≠ 0 := by
    rw [herm_conj (unitaryInvolution F 2 n) (unitaryInvolution_involutive hF)]
    exact (map_ne_zero_iff (unitaryInvolution F 2 n)
      (unitaryInvolution F 2 n).injective).mpr hca
  have hu1 : (u : F) = 1 := by
    have hK : t * herm (unitaryInvolution F 2 n) a c ≠ 0 := mul_ne_zero ht0 hac
    have h2 : (1 - (u : F)) * (t * herm (unitaryInvolution F 2 n) a c) = 0 := by
      linear_combination hβ
    rcases mul_eq_zero.mp h2 with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hK
  have hprod : s * t * herm (unitaryInvolution F 2 n) a c *
      herm (unitaryInvolution F 2 n) c a = 0 := by
    rw [hu1, one_mul, sub_eq_zero] at hα
    exact add_left_cancel (show (1 : F) + s * t * herm (unitaryInvolution F 2 n) a c *
      herm (unitaryInvolution F 2 n) c a = 1 + 0 by simpa using hα.symm)
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 ht0) hac) hca) hprod

private theorem unitaryClass_mul_ne_mul (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c a : Fin m → F} (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (ha : herm (unitaryInvolution F 2 n) a a = 0) {s t : F} (hs0 : s ≠ 0)
    (hs : s + unitaryInvolution F 2 n s = 0) (ht0 : t ≠ 0)
    (ht : t + unitaryInvolution F 2 n t = 0)
    (hca : herm (unitaryInvolution F 2 n) c a ≠ 0) :
    kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) c s *
        suTv (isUnitaryInvolution_unitaryInvolution hF) a t) ≠
      kFactsSuProj hF m (suTv (isUnitaryInvolution_unitaryInvolution hF) a t *
        suTv (isUnitaryInvolution_unitaryInvolution hF) c s) := by
  intro heq
  obtain ⟨u, hu⟩ := (kFacts_suProj_eq_iff hF
    (suTv (isUnitaryInvolution_unitaryInvolution hF) c s *
      suTv (isUnitaryInvolution_unitaryInvolution hF) a t)
    (suTv (isUnitaryInvolution_unitaryInvolution hF) a t *
      suTv (isUnitaryInvolution_unitaryInvolution hF) c s)).mp heq
  have hact : ∀ v : Fin m → F,
      (suTv (isUnitaryInvolution_unitaryInvolution hF) a t *
        suTv (isUnitaryInvolution_unitaryInvolution hF) c s) • v =
      (u : F) • ((suTv (isUnitaryInvolution_unitaryInvolution hF) c s *
        suTv (isUnitaryInvolution_unitaryInvolution hF) a t) • v) := by
    intro v
    rw [smul_def, smul_def, hu, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    exact Matrix.mulVec_smul _ _ _
  obtain ⟨hQc, hPc⟩ := unitaryClass_suTv_mul_smul_apply hF hc ha hs ht
  refine unitaryClass_coeff_contradiction hF hc hca hs0 ht0 u ?_
  rw [← hQc, ← hPc]
  exact hact c

theorem setOf_isConj_kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} (hm : 3 ≤ m)
    {e₀ : Fin m → F} (he₀ : e₀ ≠ 0) (he₀i : herm (unitaryInvolution F 2 n) e₀ e₀ = 0) :
    {y | IsConj (kFactsSuProjTv hF m e₀ 1) y} =
      {y | ∃ c : Fin m → F, c ≠ 0 ∧ herm (unitaryInvolution F 2 n) c c = 0 ∧
        y = kFactsSuProjTv hF m c 1} := by
  have hσ := isUnitaryInvolution_unitaryInvolution hF
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  ext y
  constructor
  · intro hy
    change IsConj (kFactsSuProjTv hF m e₀ 1) y at hy
    rw [isConj_iff] at hy
    obtain ⟨g, hg⟩ := hy
    obtain ⟨t, ht⟩ := kFacts_suProj_surjective hF m g
    refine ⟨t • e₀, ?_, ?_, ?_⟩
    · intro h
      apply he₀
      have := congrArg (fun v => t⁻¹ • v) h
      simpa using this
    · rw [herm_smul_smul (unitaryInvolution F 2 n) t e₀ e₀, he₀i]
    · rw [← hg, ← ht, kFacts_suProj_conj_suProjTv hF t he₀i h1]
  · rintro ⟨c, hc0, hc, rfl⟩
    obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_iso hσ hm he₀ he₀i hc0 hc
    refine isConj_iff.mpr ⟨kFactsSuProj hF m t, ?_⟩
    rw [kFacts_suProj_conj_suProjTv hF t he₀i h1, ht]

theorem commute_kFactsSuProjTv_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c a : Fin m → F} (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (ha0 : a ≠ 0) (ha : herm (unitaryInvolution F 2 n) a a = 0) {s t : F} (hs0 : s ≠ 0)
    (hs : s + unitaryInvolution F 2 n s = 0) (ht0 : t ≠ 0)
    (ht : t + unitaryInvolution F 2 n t = 0) :
    Commute (kFactsSuProjTv hF m c s) (kFactsSuProjTv hF m a t) ↔
      herm (unitaryInvolution F 2 n) c a = 0 := by
  constructor
  · intro hcomm
    by_contra hca
    exact unitaryClass_mul_ne_mul hF hc ha hs0 hs ht0 ht hca (by
      rw [map_mul, map_mul]
      exact hcomm)
  · intro h
    exact kFacts_suProjTv_comm_of_herm_eq_zero hF hc ha h hs ht

private theorem unitaryClass_comm_tv_smul_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {d c : Fin m → F} (hd0 : d ≠ 0) (hd : herm (unitaryInvolution F 2 n) d d = 0)
    (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0) {μ : F} (hμ0 : μ ≠ 0) :
    Commute (kFactsSuProjTv hF m d 1) (kFactsSuProjTv hF m c 1) ↔
      Commute (kFactsSuProjTv hF m d 1) (kFactsSuProjTv hF m (μ • c) 1) := by
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h1t : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hμc0 : μ • c ≠ 0 := smul_ne_zero hμ0 hc0
  have hμc : herm (unitaryInvolution F 2 n) (μ • c) (μ • c) = 0 := by
    rw [herm_smul_left, herm_smul_right, hc, mul_zero, mul_zero]
  rw [commute_kFactsSuProjTv_iff hF hd0 hd hc0 hc h1 h1t h1 h1t,
    commute_kFactsSuProjTv_iff hF hd0 hd hμc0 hμc h1 h1t h1 h1t,
    herm_smul_right]
  constructor
  · intro h
    rw [h, mul_zero]
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hμ0

private theorem unitaryClass_perpMem_smul (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c : Fin m → F} (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0)
    {μ : F} (hμ0 : μ ≠ 0) :
    perpMem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c' c' = 0 ∧
        y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m c 1) =
      perpMem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c' c' = 0 ∧
        y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m (μ • c) 1) := by
  ext y
  simp only [mem_perpMem]
  constructor
  · rintro ⟨hyS, hcomm⟩
    obtain ⟨d, hd0, hd, rfl⟩ := hyS
    exact ⟨⟨d, hd0, hd, rfl⟩,
      (unitaryClass_comm_tv_smul_iff hF hd0 hd hc0 hc hμ0).mp hcomm⟩
  · rintro ⟨hyS, hcomm⟩
    obtain ⟨d, hd0, hd, rfl⟩ := hyS
    exact ⟨⟨d, hd0, hd, rfl⟩,
      (unitaryClass_comm_tv_smul_iff hF hd0 hd hc0 hc hμ0).mpr hcomm⟩

private theorem unitaryClass_exists_smul_of_perpMem_eq (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c c' : Fin m → F} (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (hc'0 : c' ≠ 0) (hc' : herm (unitaryInvolution F 2 n) c' c' = 0)
    (heq : perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧
        herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧ y = kFactsSuProjTv hF m c'' 1}
        (kFactsSuProjTv hF m c 1) =
      perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧
        herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧ y = kFactsSuProjTv hF m c'' 1}
        (kFactsSuProjTv hF m c' 1)) :
    ∃ μ : F, c' = μ • c := by
  by_contra hne
  have hne' : ∀ μ : F, c' ≠ μ • c := fun μ h => hne ⟨μ, h⟩
  have h1 : (1 : F) ≠ 0 := one_ne_zero
  have h1t : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  by_cases hcc' : herm (unitaryInvolution F 2 n) c c' = 0
  · obtain ⟨d, hd, hcd, hc'd⟩ := exists_iso_perp
      (isUnitaryInvolution_unitaryInvolution hF) hc0 hc hc' hcc' hne'
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hc'd (herm_zero_right _ c')
    have hmem : kFactsSuProjTv hF m d 1 ∈
        perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧
          herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧ y = kFactsSuProjTv hF m c'' 1}
          (kFactsSuProjTv hF m c 1) := by
      refine ⟨⟨d, hd0, hd, rfl⟩, ?_⟩
      exact ((commute_kFactsSuProjTv_iff hF hc0 hc hd0 hd h1 h1t h1 h1t).mpr hcd).symm
    rw [heq] at hmem
    have hdc' : herm (unitaryInvolution F 2 n) d c' = 0 :=
      (commute_kFactsSuProjTv_iff hF hd0 hd hc'0 hc' h1 h1t h1 h1t).mp
        (mem_perpMem.mp hmem).2
    exact hc'd (herm_eq_zero_comm _ (unitaryInvolution_involutive hF) hdc')
  · have hmem : kFactsSuProjTv hF m c' 1 ∈
        perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧
          herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧ y = kFactsSuProjTv hF m c'' 1}
          (kFactsSuProjTv hF m c' 1) :=
      mem_perpMem_self ⟨c', hc'0, hc', rfl⟩
    rw [← heq] at hmem
    have hc'c : herm (unitaryInvolution F 2 n) c' c = 0 :=
      (commute_kFactsSuProjTv_iff hF hc'0 hc' hc0 hc h1 h1t h1 h1t).mp
        (mem_perpMem.mp hmem).2
    exact hcc' (herm_eq_zero_comm _ (unitaryInvolution_involutive hF) hc'c)

theorem perpMem_setOf_kFactsSuProjTv_eq_iff (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c c' : Fin m → F} (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0)
    (hc'0 : c' ≠ 0) (hc' : herm (unitaryInvolution F 2 n) c' c' = 0) :
    perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧
        y = kFactsSuProjTv hF m c'' 1} (kFactsSuProjTv hF m c 1) =
      perpMem {y | ∃ c'' : Fin m → F, c'' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c'' c'' = 0 ∧
        y = kFactsSuProjTv hF m c'' 1} (kFactsSuProjTv hF m c' 1) ↔
      ∃ μ : F, c' = μ • c := by
  constructor
  · intro heq
    exact unitaryClass_exists_smul_of_perpMem_eq hF hc0 hc hc'0 hc' heq
  · rintro ⟨μ, hμ⟩
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hc'0 hμ
    rw [hμ]
    exact unitaryClass_perpMem_smul hF hc0 hc hμ0

private theorem unitaryClass_mem_Vmem_of_traceZero (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ}
    {c : Fin m → F} (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0) {s : F}
    (hs0 : s ≠ 0) (hs : s + unitaryInvolution F 2 n s = 0) :
    kFactsSuProjTv hF m c s ∈
      Vmem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c' c' = 0 ∧
        y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m c 1) := by
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  have hsneg : unitaryInvolution F 2 n s = -s := by linear_combination hs
  have hfix : unitaryInvolution F 2 n s = s := by
    rw [hsneg, CharTwo.neg_eq]
  obtain ⟨l, hl⟩ := (isUnitaryInvolution_unitaryInvolution hF).exists_norm hfix
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hl
    exact hs0 hl.symm
  have hlc0 : l • c ≠ 0 := smul_ne_zero hl0 hc0
  have hlc : herm (unitaryInvolution F 2 n) (l • c) (l • c) = 0 := by
    rw [herm_smul_left, herm_smul_right, hc, mul_zero, mul_zero]
  have hTs : kFactsSuProjTv hF m c s = kFactsSuProjTv hF m (l • c) 1 := by
    rw [kFacts_suProjTv_smul_vec hF hc h1 l, hl, mul_one]
  rw [mem_Vmem]
  refine ⟨⟨l • c, hlc0, hlc, hTs⟩, ?_⟩
  rw [hTs]
  exact (unitaryClass_perpMem_smul hF hc0 hc hl0).symm

theorem Vmem_setOf_kFactsSuProjTv (hF : Nat.card F = (2 ^ n) ^ 2) {m : ℕ} {c : Fin m → F}
    (hc0 : c ≠ 0) (hc : herm (unitaryInvolution F 2 n) c c = 0) :
    Vmem {y | ∃ c' : Fin m → F, c' ≠ 0 ∧ herm (unitaryInvolution F 2 n) c' c' = 0 ∧
        y = kFactsSuProjTv hF m c' 1} (kFactsSuProjTv hF m c 1) =
      {y | ∃ s : F, s ≠ 0 ∧ s + unitaryInvolution F 2 n s = 0 ∧ y = kFactsSuProjTv hF m c s} := by
  have h1 : (1 : F) + unitaryInvolution F 2 n 1 = 0 := by
    rw [map_one]
    exact CharTwo.add_self_eq_zero 1
  ext y
  constructor
  · intro hy
    rw [mem_Vmem] at hy
    obtain ⟨hyS, hperp⟩ := hy
    obtain ⟨c', hc'0, hc', rfl⟩ := hyS
    obtain ⟨μ, hμ⟩ :=
      (perpMem_setOf_kFactsSuProjTv_eq_iff hF hc0 hc hc'0 hc').mp hperp.symm
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hμ
      exact hc'0 hμ
    refine ⟨unitaryInvolution F 2 n μ * μ, ?_, ?_, ?_⟩
    · exact mul_ne_zero ((map_ne_zero_iff (unitaryInvolution F 2 n)
        (unitaryInvolution F 2 n).injective).mpr hμ0) hμ0
    · rw [(isUnitaryInvolution_unitaryInvolution hF).norm_fixed]
      exact CharTwo.add_self_eq_zero _
    · rw [hμ, kFacts_suProjTv_smul_vec hF hc h1 μ, mul_one]
  · rintro ⟨s, hs0, hs, rfl⟩
    exact unitaryClass_mem_Vmem_of_traceZero hF hc0 hc hs0 hs

theorem exists_mulEquiv_of_isUnitaryTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m n : ℕ} (hs : IsUnitaryTransvection X m n s) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (hK : Nat.card K = (2 ^ n) ^ 2)
      (φ : X ≃* StatedProj (StatedSU m (2 ^ n) K)) (e₀ : Fin m → K),
      e₀ ≠ 0 ∧ herm (unitaryInvolution K 2 n) e₀ e₀ = 0 ∧ φ s = kFactsSuProjTv hK m e₀ 1 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, e, hvt⟩ := hs
  let : Field K := hKfield
  let : Finite K := hKfinite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : CharP K 2 := charP_of_card_sq (p := 2) (f := n) hKcard
  obtain ⟨e₀, he₀0, he₀, he₀eq⟩ := kFacts_su_exists_centre hKcard hvt
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : X, ψ x = QuotientGroup.mk x := by
    intro x
    simp [ψ]
  let φ : X ≃* StatedProj (StatedSU m (2 ^ n) K) := ψ.trans e
  refine ⟨K, hKfield, hKfinite, inferInstance, hKcard, φ, e₀, he₀0, he₀, ?_⟩
  have hφs : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ]
  rw [hφs]
  exact he₀eq

end CFSG.OddTranspositions.PartFour
