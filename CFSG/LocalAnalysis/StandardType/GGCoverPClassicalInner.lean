module

public import CFSG.LocalAnalysis.StandardType.GGCoverSLPSL
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpRestInner
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace CoverPInner

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem ggCoverPTableB_of_forall_inner {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ a : MulAut R, (∃ k : ℕ, a ^ p ^ k = 1) → a ∈ (MulAut.conj : R →* MulAut R).range) :
    GGCoverPTableB p R I := by
  intro M _ _ L' E θ hE hpos a ha
  obtain ⟨ρ, hρ⟩ := h a ha
  refine ⟨ρ, fun e => ?_⟩
  rw [← hρ, inv_mul_cancel]
  exact Commute.one_left _

theorem mem_range_conj_of_eq_mul {R : Type} [Group R] {φ u f : MulAut R} {a N : ℕ}
    (hφ : φ ^ a = 1) (hu : u ∈ (MulAut.conj : R →* MulAut R).range) (hf : f ^ N = 1)
    (hcop : Nat.Coprime N a) (h : φ = u * f) : φ ∈ (MulAut.conj : R →* MulAut R).range := by
  have hpow : φ ^ N ∈ (MulAut.conj : R →* MulAut R).range := by
    rw [h]
    obtain ⟨d, hd, hd'⟩ :=
      RecipeFieldOmega.exists_mul_pow_eq (MulAut.conj : R →* MulAut R).range hu N
    rw [hd', hf, mul_one]
    exact hd
  exact RecipeFieldOmega.mem_of_pow_mem_of_coprime _ hpow hφ hcop

private lemma fieldAut_pow_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (hcard : Nat.card (RingAut K) = n) (σ : K ≃+* K) : σ ^ n = 1 := by
  rw [← hcard]
  exact pow_card_eq_one'

theorem forall_inner_symplectic {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 2 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (a : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    a ∈ (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _).range := by
  obtain ⟨k, hk⟩ := ha
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hcard : Nat.card (RingAut K) = n :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hcop : Nat.Coprime n (p ^ k) := hp.coprime_pow_of_not_dvd hpn
  have hcl : Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) ≤
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.fieldAut m K).range := by
    rw [Subgroup.closure_le]
    rintro φ hφ
    obtain ⟨σ, rfl⟩ := RecipeFieldSp.exists_fieldAut_of_mem hφ
    exact ⟨σ, rfl⟩
  obtain ⟨u, hu, f, hf, haeq⟩ :=
    NbrGraphSymplectic.ggOddAutInnField_symplectic hm hodd a hk
  obtain ⟨σ, hσ⟩ := hcl hf
  refine mem_range_conj_of_eq_mul hk (RecipeFieldSp.mem_conjImage_iff_inn.mp hu) ?_ hcop haeq
  rw [← hσ, ← map_pow]
  rw [fieldAut_pow_of_card hcard σ, map_one]

theorem forall_inner_omegaPlus {m n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hm : 4 ≤ m) (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : m = 4 → p ≠ 3)
    (hpn : ¬ p ∣ n) (a : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))))
    (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    a ∈ (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m)) →* MulAut _).range := by
  obtain ⟨k, hk⟩ := ha
  have hm1 : 1 ≤ m := by omega
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hcard : Nat.card (RingAut K) = n :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1
  have hcop : Nat.Coprime n (p ^ k) := hp.coprime_pow_of_not_dvd hpn
  have hfn : ∀ f ∈ Subgroup.closure
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K m)))),
      f ^ n = 1 := by
    intro f hf
    obtain ⟨σ, hσ⟩ := RecipeFieldOmega.congr_plusEquiv_of_mem_closure hm1 hf
    apply (MulAut.congr (RecipeFieldOmega.plusEquiv hm1)).injective
    rw [map_pow, map_one, hσ, ← map_pow]
    rw [fieldAut_pow_of_card hcard σ, map_one]
  by_cases hm5 : 5 ≤ m
  · obtain ⟨u, hu, f, hf, haeq⟩ :=
      RawAutOmega.ggOddAutInnField_omegaPlus hm5 hodd a hk
    exact mem_range_conj_of_eq_mul hk hu (hfn f hf) hcop haeq
  · have hm4 : m = 4 := by omega
    subst hm4
    have hp3' : p ≠ 3 := hp3 rfl
    have h6 : Nat.Coprime 6 p := by
      rw [show 6 = 2 * 3 by norm_num, Nat.coprime_mul_iff_left]
      exact ⟨(Nat.coprime_primes Nat.prime_two hp).2 hp2.symm,
        (Nat.coprime_primes Nat.prime_three hp).2 hp3'.symm⟩
    have hcop6 : Nat.Coprime 6 (p ^ k) := h6.pow_right k
    obtain ⟨u, hu, f, hf, haeq⟩ :=
      (RawAutOmega.ggOddAutInnField_omegaPlus_of (by norm_num : 1 ≤ 4) (M := 6) hcop6
        (RawAutOmega.exists_eq_mul_mul_fieldAutP_four (K := K))) a hk
    exact mem_range_conj_of_eq_mul hk hu (hfn f hf) hcop haeq

theorem pow_two_mul_eq_one_of_mem_closure_omegaMinus {r n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hr : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hK : Nat.card K = 2 ^ n)
    {g : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)))}
    (hg : g ∈ Subgroup.closure (LargeEvenPhiQ (r - 1) b c
      (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))) :
    g ^ (2 * n) = 1 := by
  apply (MulAut.congr (RecipeFieldOmega.minusEquiv hr b c)).injective
  rw [map_pow, map_one]
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp
    (RecipeFieldOmega.congr_minusEquiv_of_mem_closure hr hirr hg)
  rw [← hz, ← orderOf_dvd_iff_pow_eq_one, orderOf_zpow]
  exact dvd_trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    (orderOf_dvd_of_pow_eq_one (AutOm.frobAut_pow_two_mul hr hirr hK))

theorem forall_inner_omegaMinus {r n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (hr : 4 ≤ r) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (a : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c))))
    (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    a ∈ (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (r - 1) b c)) →*
      MulAut _).range := by
  obtain ⟨k, hk⟩ := ha
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hcop : Nat.Coprime (2 * n) (p ^ k) :=
    Nat.coprime_mul_iff_left.mpr
      ⟨Nat.coprime_two_left.mpr hodd, hp.coprime_pow_of_not_dvd hpn⟩
  obtain ⟨u, hu, g, hg, haeq⟩ :=
    RawAutOmega.exists_inner_mul_field_omegaMinus (n := r) hr hirr hK a
  have hgN : g ^ (2 * n) = 1 :=
    pow_two_mul_eq_one_of_mem_closure_omegaMinus hr hirr hK hg
  exact mem_range_conj_of_eq_mul hk hu hgN hcop haeq

theorem forall_inner_unitaryFour {n p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (a : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n))))
    (ha : ∃ k : ℕ, a ^ p ^ k = 1) :
    a ∈ (MulAut.conj : LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ n)) →* MulAut _).range := by
  obtain ⟨k, hk⟩ := ha
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let h := CFSG.StandardType.unitaryFieldData_of_card hn hK
  obtain ⟨Θ, -, hker, -⟩ :=
    RecipeFieldSU.exists_fieldFactor (d := 4) h (by norm_num) (by omega)
  have h1 : Θ a ^ p ^ k = 1 := by rw [← map_pow, hk, map_one]
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  have hcard : Nat.card (RingAut K) = 2 * n :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK2).1
  have h2 : Θ a ^ (2 * n) = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  have hcop : Nat.Coprime (p ^ k) (2 * n) := by
    have h2p : Nat.Coprime 2 (p ^ k) := Nat.coprime_two_left.mpr hodd
    exact (Nat.coprime_mul_iff_left.mpr ⟨h2p, hp.coprime_pow_of_not_dvd hpn⟩).symm
  have hone : orderOf (Θ a) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one h2)
  have hΘ : Θ a = 1 := orderOf_eq_one_iff.mp hone
  have hmem : a ∈ RecipeFieldSU.recIU 4 h (by norm_num : 1 ≤ 4) := (hker a).mp hΘ
  refine TableB.matConjImage_gu_subset_inn (n := n) (d := 4) hK
    (CFSG.StandardType.coprime_two_pow_add_one_four hn) ?_
  rw [← RecipeFieldSU.coe_recIU h hK (by norm_num : 1 ≤ 4)]
  exact hmem

private lemma labelAll_symplectic {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (ht : lab.tag = .B ∨ lab.tag = .C) (hl : 2 ≤ lab.rank) (hpn : ¬ p ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hl hpn ⊢
  rcases ht with ht | ht <;> subst ht
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    exact ggCoverPTableB_of_forall_inner fun a ha =>
      forall_inner_symplectic hK hl hp hp2 hpn a ha
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    exact ggCoverPTableB_of_forall_inner fun a ha =>
      forall_inner_symplectic hK hl hp hp2 hpn a ha

private lemma labelAll_unitaryFour {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hS : lab.tag = .twA ∨ lab.tag = .twD) (hl : lab.rank = 3) (hn : 1 ≤ lab.n)
    (hpn : ¬ p ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hS hl hn hpn ⊢
  rcases hS with ht | ht
  · subst ht
    subst hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine recipeUnitary_and (fun K _ _ hK => ?_) hQ
    exact ggCoverPTableB_of_forall_inner fun a ha =>
      forall_inner_unitaryFour hK hn hp hp2 hpn a ha
  · subst ht
    subst hl
    intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show (3 : ℕ) ≠ 2 by decide, ↓reduceIte] at hQ ⊢
    refine recipeUnitary_and (fun K _ _ hK => ?_) hQ
    exact ggCoverPTableB_of_forall_inner fun a ha =>
      forall_inner_unitaryFour hK hn hp hp2 hpn a ha

theorem largeEvenLabelAll_coverP_DThree {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (htag : lab.tag = .D) (hl : lab.rank = 3) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hl hpn ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  rw [if_pos hl] at hQ ⊢
  obtain ⟨K, hfield, hfinite, hK, hQ'⟩ := hQ
  refine ⟨K, hfield, hfinite, hK, hQ', ?_⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (R := K) (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ggCoverPTableB_of_mulEquiv (TypeA.recipeEquiv 4 K)
    (fun φ hφ => TypeA.congr_recipeEquiv_mem hφ)
    (ggCoverPTableB_PSL (K := K) hp hpK (le_refl 4))

theorem largeEvenLabelAll_coverP_inner {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (hpn : ¬ p ∣ lab.n)
    (htag : lab.tag = .B ∨ lab.tag = .C ∨ (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ 3 ≤ lab.rank) ∨ (lab.tag = .twA ∧ lab.rank = 3))
    (hD4 : ¬ GGD4Three p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGCoverPTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hD4 ⊢
  dsimp only [GGD4Three] at hD4
  rcases htag with ht | ht | ⟨ht, hl4⟩ | ⟨ht, hl3⟩ | ⟨ht, hl3⟩
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    exact labelAll_symplectic hp hp2 (Or.inl rfl) hlab.2.1 hpn
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    exact labelAll_symplectic hp hp2 (Or.inr rfl) hlab.2.1 hpn
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl hl4 ?_
    intro K _ _ _ hK
    refine ggCoverPTableB_of_forall_inner fun a ha =>
      forall_inner_omegaPlus hK hl4 hp hp2 ?_ hpn a ha
    intro h4 hp3
    exact hD4 ⟨rfl, h4, hp3⟩
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    rcases eq_or_lt_of_le hl3 with h3 | h4
    · exact labelAll_unitaryFour hp hp2 (Or.inr rfl) h3.symm hlab.1 hpn
    · have h4' : 4 ≤ l := by omega
      refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl h4' ?_
      intro K _ _ _ hK b c hirr
      refine ggCoverPTableB_of_forall_inner fun a ha =>
        forall_inner_omegaMinus hK h4' hirr hp hp2 hpn a ha
  · subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    exact labelAll_unitaryFour hp hp2 (Or.inl rfl) hl3 hlab.1 hpn

end CoverPInner

end CFSG.StandardType
