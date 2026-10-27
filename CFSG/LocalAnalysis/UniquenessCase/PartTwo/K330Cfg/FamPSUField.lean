module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddAll
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldUnitary
public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.RankThree.SteinbergR3EUnitaryFieldDescent
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.Classical
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.RankThree.PartOne.CTP
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven (fixedBy mem_fixedBy fixedBy_map_congr)

private lemma k330c_fieldRigidPair_congr {J T : Type} [Group J] [Group T]
    (e : J ≃* T) {ψ : MulAut T} (hrig : FieldRigid ψ) (hpair : FieldPair ψ) :
    FieldRigid ((MulAut.congr e).symm ψ) ∧ FieldPair ((MulAut.congr e).symm ψ) := by
  set φ : MulAut J := (MulAut.congr e).symm ψ with hφ
  have hψ : MulAut.congr e φ = ψ := by
    rw [hφ]
    exact MulEquiv.apply_symm_apply (MulAut.congr e) ψ
  have hfix : (fixedBy (Subgroup.zpowers φ)).map e.toMonoidHom =
      fixedBy (Subgroup.zpowers ψ) := by
    rw [fixedBy_map_congr e (Subgroup.zpowers φ)]
    have hz : (Subgroup.zpowers φ).map (MulAut.congr e).toMonoidHom =
        Subgroup.zpowers ψ := by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hψ]
    rw [hz]
  refine ⟨?_, ?_⟩
  · intro β hβ
    have hβ' : ∀ y ∈ fixedBy (Subgroup.zpowers ψ), MulAut.congr e β y = y := by
      intro y hy
      rw [← hfix] at hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
      rw [hβ x hx]
    have hmem : MulAut.congr e β ∈ Subgroup.zpowers ψ := hrig (MulAut.congr e β) hβ'
    have hz : (Subgroup.zpowers ψ).map (MulAut.congr e).symm.toMonoidHom =
        Subgroup.zpowers φ := by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hφ]
    rw [← hz]
    exact Subgroup.mem_map.mpr ⟨MulAut.congr e β, hmem, by
      simp only [MulEquiv.coe_toMonoidHom]
      exact MulEquiv.symm_apply_apply (MulAut.congr e) β⟩
  · intro n hn
    have hconjmap : ((fixedBy (Subgroup.zpowers φ)).map (MulAut.conj n).toMonoidHom).map
        e.toMonoidHom =
        (fixedBy (Subgroup.zpowers ψ)).map (MulAut.conj (e n)).toMonoidHom := by
      have hcomp : e.toMonoidHom.comp (MulAut.conj n).toMonoidHom =
          (MulAut.conj (e n)).toMonoidHom.comp e.toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, map_mul]
      rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hfix]
    have hn' : (fixedBy (Subgroup.zpowers ψ)).map (MulAut.conj (e n)).toMonoidHom ≠
        fixedBy (Subgroup.zpowers ψ) := by
      intro heq
      apply hn
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hconjmap, heq, hfix]
    have htop := hpair (e n) hn'
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, hfix, hconjmap, htop,
      Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]

private theorem k330c_fixedBy_zpowers_eq_fieldFixedPSU {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (σ : K ≃+* K) :
    fixedBy (Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) =
      fieldFixedPSU h n σ := by
  ext x
  rw [mem_fixedBy]
  constructor
  · intro hx
    exact hx _ (Subgroup.mem_zpowers _)
  · intro hx w hw
    have h1 := smul_eq_self_of_mem_zpowers (G := MulAut
      (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) hw hx
    rwa [MulAut.smul_def] at h1

private theorem k330c_fieldRigid_zpowers {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : n = 4 ∨ n = 5) {σ : K ≃+* K} (hσ : orderOf σ = 7) :
    FieldRigid (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  have hnlt : n < 7 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, hsimple, -⟩ :=
    CFSG.RankThree.Classical.higher_unitary_prime_subfield_fixed_group_and_full_centralizer
      (ℓ := ℓ) (f := f) (n := n) (p := 7) h hn3 hnlt Nat.prime_seven hq σ hσ
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / 7) = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  have hfix : fixingSubgroup (MulAut (primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
        (fieldFixedPSU h n σ : Set (primeFormP h
          ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) =
      Subgroup.zpowers (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
    rw [(hsimple hq₀).2.2.1, (hsimple hq₀).2.2.2.1]
  intro α hα
  have hF := k330c_fixedBy_zpowers_eq_fieldFixedPSU (n := n) h σ
  have hmem : α ∈ fixingSubgroup (MulAut (primeFormP h
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
      (fieldFixedPSU h n σ : Set (primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) := by
    refine (mem_fixingSubgroup_iff _).2 fun x hx => ?_
    rw [MulAut.smul_def]
    exact hα x (by rw [hF]; exact hx)
  rwa [hfix] at hmem

private theorem k330c_fieldPair_zpowers {ℓ f n : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData ℓ f K) (hn : n = 4 ∨ n = 5) {σ : K ≃+* K}
    (hσ : orderOf σ = 7) :
    FieldPair (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) := by
  classical
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  have hnlt : n < 7 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hpf, -, -, -, hrange, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.higher_unitary_prime_subfield_fixed_group_and_full_centralizer
      (ℓ := ℓ) (f := f) (n := n) (p := 7) h hn3 hnlt Nat.prime_seven hq σ hσ
  have hq₀ : ¬(n = 3 ∧ ℓ ^ (f / 7) = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  intro x hne
  have hF := k330c_fixedBy_zpowers_eq_fieldFixedPSU (n := n) h σ
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_seven (by norm_num) hσ with hh₀
  set hbar₀ := fixSubfield_unitaryFieldData_bar h Nat.prime_seven (by norm_num) hσ with hhb
  set N := normOneScalars h (gramSU h
    ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n with hN
  have hsu_range : (suSub h h₀ hbar₀ n).map (QuotientGroup.mk' N) = fieldFixedPSU h n σ := by
    rw [← range_subfieldPSU_eq_map h h₀ hbar₀ n]
    exact hrange
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective N x
  have hg₀' : (g₀ : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = x := hg₀
  set A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    ⟨g₀, (Iff.mp (mem_gramSU_iff_unitary (h := h)
      (C := ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) g₀.2).1⟩ with hA
  have hconj : MulAut.conj x =
      primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, MulAut.conj_apply, ← hg₀', ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hne1 : (fieldFixedPSU h n σ).map (primeFormConjHom h
      ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A).toMonoidHom ≠ fieldFixedPSU h n σ := by
    rw [hF] at hne
    rw [hconj] at hne
    exact hne
  have hmmk := map_primeFormConjHom_map_mk (h := h) (h₀ := h₀) (hbar := hbar₀) (n := n) A
  have hne2 : ((suSub h h₀ hbar₀ n).map
      (primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A).toMonoidHom).map
      (QuotientGroup.mk' N) ≠ (suSub h h₀ hbar₀ n).map (QuotientGroup.mk' N) := by
    rw [← hsu_range] at hne1
    rwa [hmmk] at hne1
  have hne_su : (suSub h h₀ hbar₀ n).map
      (primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) A).toMonoidHom ≠
      suSub h h₀ hbar₀ n := by
    intro hh
    exact hne2 (by rw [hh])
  have hpair := CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_not_three_two ℓ f (f / 7) K h
    (fixSubfield σ) h₀ hbar₀ 7 Nat.prime_seven (by norm_num) (Nat.mul_div_cancel' hpf).symm n
    hn3 hq₀ A hne_su
  have h4 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hpair
  rw [map_closure_union, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h4
  rw [hF, hconj, ← hsu_range, hmmk, Subgroup.sup_eq_closure]
  exact h4

private lemma k330c_prod_bound_four (q : ℤ) (hq : 2 ≤ q) :
    q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1))) ≤ q ^ 15 := by
  have hq0 : (0 : ℤ) ≤ q := by linarith
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 5 := by
    have h : (0 : ℤ) ≤ q ^ 2 * (q - 1) := mul_nonneg (sq_nonneg q) (by linarith)
    nlinarith [h]
  have h2 : q ^ 4 - 1 ≤ q ^ 4 := by linarith
  have h3 : (0 : ℤ) ≤ q ^ 4 - 1 := by
    have h : (2 : ℤ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
    norm_num at h
    linarith
  have h4 : (0 : ℤ) ≤ q ^ 5 := pow_nonneg hq0 5
  have hchain : (q ^ 2 - 1) * ((q ^ 3 + 1) * (q ^ 4 - 1)) ≤ q ^ 9 := by
    have h := mul_le_mul h1 h2 h3 h4
    have e : q ^ 5 * q ^ 4 = q ^ 9 := by ring
    rw [e] at h
    nlinarith [h]
  have h5 : (0 : ℤ) ≤ q ^ 6 := pow_nonneg hq0 6
  have h := mul_le_mul_of_nonneg_left hchain h5
  have e : q ^ 6 * q ^ 9 = q ^ 15 := by ring
  rw [e] at h
  exact h

private lemma k330c_prod_bound_five (q : ℤ) (hq : 2 ≤ q) :
    q ^ 10 * ((q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1)))) ≤ q ^ 24 := by
  have hq0 : (0 : ℤ) ≤ q := by linarith
  have h1 : (q ^ 2 - 1) * (q ^ 3 + 1) ≤ q ^ 5 := by
    have h : (0 : ℤ) ≤ q ^ 2 * (q - 1) := mul_nonneg (sq_nonneg q) (by linarith)
    nlinarith [h]
  have h2 : (q ^ 4 - 1) * (q ^ 5 + 1) ≤ q ^ 9 := by
    have h : (0 : ℤ) ≤ q ^ 4 * (q - 1) := mul_nonneg (pow_nonneg hq0 4) (by linarith)
    nlinarith [h]
  have h3 : (0 : ℤ) ≤ (q ^ 4 - 1) * (q ^ 5 + 1) := by
    have h4 : (1 : ℤ) ≤ q ^ 4 := by
      have h : (2 : ℤ) ^ 4 ≤ q ^ 4 := pow_le_pow_left₀ (by norm_num) hq 4
      norm_num at h
      linarith
    have h5 : (0 : ℤ) ≤ q ^ 5 + 1 := by
      have h : (0 : ℤ) ≤ q ^ 5 := pow_nonneg hq0 5
      linarith
    exact mul_nonneg (by linarith) h5
  have h4 : (0 : ℤ) ≤ q ^ 5 := pow_nonneg hq0 5
  have hprod : (q ^ 2 - 1) * ((q ^ 3 + 1) * ((q ^ 4 - 1) * (q ^ 5 + 1))) ≤ q ^ 14 := by
    have h := mul_le_mul h1 h2 h3 h4
    have e : q ^ 5 * q ^ 9 = q ^ 14 := by ring
    rw [e] at h
    nlinarith [h]
  have h6 : (0 : ℤ) ≤ q ^ 10 := pow_nonneg hq0 10
  have h := mul_le_mul_of_nonneg_left hprod h6
  have e : q ^ 10 * q ^ 14 = q ^ 24 := by ring
  rw [e] at h
  exact h

theorem k330c_card_fieldFixedPSU_le {ℓ f n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hn : n = 4 ∨ n = 5) {σ : K ≃+* K} (hσ : orderOf σ = 7) :
    Nat.card (fieldFixedPSU h n σ) ≤ (ℓ ^ (f / 7)) ^ (n ^ 2 - 1) := by
  classical
  haveI : Finite K := h.finite
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  have hnlt : n < 7 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨hpf, -, -, hinj, hrange, -, -, -, -, -, -⟩ :=
    CFSG.RankThree.Classical.higher_unitary_prime_subfield_fixed_group_and_full_centralizer
      (ℓ := ℓ) (f := f) (n := n) (p := 7) h hn3 hnlt Nat.prime_seven hq σ hσ
  let h₀ : UnitaryFieldData ℓ (f / 7) (fixSubfield σ) :=
    fixSubfield_unitaryFieldData h Nat.prime_seven (by norm_num) hσ
  have hcard_le : Nat.card (fieldFixedPSU h n σ) ≤
      Nat.card (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
    calc Nat.card (fieldFixedPSU h n σ)
        = Nat.card (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
            Matrix (Fin n) (Fin n) (fixSubfield σ))) := by
          rw [← hrange]
          exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      _ ≤ Nat.card (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
            Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
          Nat.card_le_card_of_surjective (QuotientGroup.mk' _)
            (QuotientGroup.mk'_surjective _)
  have hdiv1 : 1 ≤ f / 7 := by
    obtain ⟨m, hm⟩ := hpf
    have hm1 : 1 ≤ m := by
      have : 1 ≤ 7 * m := by rw [← hm]; exact h.one_le
      omega
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num : 0 < 7)]
    exact hm1
  have hq2 : 2 ≤ ℓ ^ (f / 7) := by
    calc 2 ≤ ℓ := h.prime.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ (f / 7) := pow_le_pow_right₀ (le_of_lt h.prime.one_lt) hdiv1
  rcases hn with rfl | rfl
  · let Q : ℤ := ((ℓ ^ (f / 7) : ℕ) : ℤ)
    have hQdef : Q = ((ℓ ^ (f / 7) : ℕ) : ℤ) := rfl
    have hQ2Z : (2 : ℤ) ≤ Q := by rw [hQdef]; exact_mod_cast hq2
    have hSU : (Nat.card (gramSU h₀ ((1 : GL (Fin 4) (fixSubfield σ)) :
          Matrix (Fin 4) (Fin 4) (fixSubfield σ))) : ℤ) =
        Q ^ 6 * ∏ i ∈ Finset.Icc 2 4, (Q ^ i - (-1) ^ i) := by
      have hU := (CFSG.LinearGroups.unitary_full_group_order h₀
        (gramForm_isSymm h₀ (G := (1 : Matrix (Fin 4) (Fin 4) (fixSubfield σ))) (by simp))
        (gramForm_separatingLeft h₀ (by simp))
        (Module.finrank_fin_fun _) (by norm_num)).2.1
      rw [show (4 : ℕ) * (4 - 1) / 2 = 6 by norm_num] at hU
      rw [← hQdef] at hU
      rw [card_gramSU h₀ ((1 : GL (Fin 4) (fixSubfield σ)) :
        Matrix (Fin 4) (Fin 4) (fixSubfield σ))]
      exact hU
    have hp4 : ∏ i ∈ Finset.Icc 2 4, (Q ^ i - (-1 : ℤ) ^ i) =
        (Q ^ 2 - 1) * ((Q ^ 3 + 1) * (Q ^ 4 - 1)) := by
      rw [Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
        Finset.Icc_self, Finset.prod_singleton]
      ring
    have hbound : (Nat.card (gramSU h₀ ((1 : GL (Fin 4) (fixSubfield σ)) :
          Matrix (Fin 4) (Fin 4) (fixSubfield σ))) : ℤ) ≤ Q ^ 15 := by
      rw [hSU, hp4]
      exact k330c_prod_bound_four Q hQ2Z
    have hnat : Nat.card (gramSU h₀ ((1 : GL (Fin 4) (fixSubfield σ)) :
          Matrix (Fin 4) (Fin 4) (fixSubfield σ))) ≤ (ℓ ^ (f / 7)) ^ 15 := by
      rw [hQdef] at hbound
      exact_mod_cast hbound
    have hgoal : Nat.card (fieldFixedPSU h 4 σ) ≤ (ℓ ^ (f / 7)) ^ 15 :=
      hcard_le.trans hnat
    simpa using hgoal
  · let Q : ℤ := ((ℓ ^ (f / 7) : ℕ) : ℤ)
    have hQdef : Q = ((ℓ ^ (f / 7) : ℕ) : ℤ) := rfl
    have hQ2Z : (2 : ℤ) ≤ Q := by rw [hQdef]; exact_mod_cast hq2
    have hSU : (Nat.card (gramSU h₀ ((1 : GL (Fin 5) (fixSubfield σ)) :
          Matrix (Fin 5) (Fin 5) (fixSubfield σ))) : ℤ) =
        Q ^ 10 * ∏ i ∈ Finset.Icc 2 5, (Q ^ i - (-1) ^ i) := by
      have hU := (CFSG.LinearGroups.unitary_full_group_order h₀
        (gramForm_isSymm h₀ (G := (1 : Matrix (Fin 5) (Fin 5) (fixSubfield σ))) (by simp))
        (gramForm_separatingLeft h₀ (by simp))
        (Module.finrank_fin_fun _) (by norm_num)).2.1
      rw [show (5 : ℕ) * (5 - 1) / 2 = 10 by norm_num] at hU
      rw [← hQdef] at hU
      rw [card_gramSU h₀ ((1 : GL (Fin 5) (fixSubfield σ)) :
        Matrix (Fin 5) (Fin 5) (fixSubfield σ))]
      exact hU
    have hp5 : ∏ i ∈ Finset.Icc 2 5, (Q ^ i - (-1 : ℤ) ^ i) =
        (Q ^ 2 - 1) * ((Q ^ 3 + 1) * ((Q ^ 4 - 1) * (Q ^ 5 + 1))) := by
      rw [Finset.prod_Icc_succ_top (by norm_num), Finset.prod_Icc_succ_top (by norm_num),
        Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]
      ring
    have hbound : (Nat.card (gramSU h₀ ((1 : GL (Fin 5) (fixSubfield σ)) :
          Matrix (Fin 5) (Fin 5) (fixSubfield σ))) : ℤ) ≤ Q ^ 24 := by
      rw [hSU, hp5]
      exact k330c_prod_bound_five Q hQ2Z
    have hnat : Nat.card (gramSU h₀ ((1 : GL (Fin 5) (fixSubfield σ)) :
          Matrix (Fin 5) (Fin 5) (fixSubfield σ))) ≤ (ℓ ^ (f / 7)) ^ 24 := by
      rw [hQdef] at hbound
      exact_mod_cast hbound
    have hgoal : Nat.card (fieldFixedPSU h 5 σ) ≤ (ℓ ^ (f / 7)) ^ 24 :=
      hcard_le.trans hnat
    simpa using hgoal

private theorem k330c_hasFieldRP_primeFormP {ℓ f n : ℕ} {K : Type}
    [Field K] [Finite K] (h : UnitaryFieldData ℓ f K) (hn : n = 4 ∨ n = 5) :
    HasFieldRP (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (ℓ ^ f)
      (sltBound n) := by
  classical
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hq : ¬(n = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨h1, -⟩
    rcases hn with rfl | rfl <;> omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  intro W hW h7T
  have h7U : ¬ 7 ∣ Nat.card (unitaryPSU h n) := by
    obtain ⟨eTU⟩ := nonempty_primeFormP_mulEquiv h hC
    rwa [← Nat.card_congr eTU.toEquiv]
  obtain ⟨hℓne, -, -, hqp⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.unitary_prime_numerics h hn3 hq
      Nat.prime_seven (by decide) h7U
  have hcyc : IsCyclic ↥W := isCyclic_of_prime_card hW
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hordg : orderOf g = 7 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hW]
  set a : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    (g : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) with ha
  have haord : orderOf a = 7 := by rw [ha, Subgroup.orderOf_coe, hordg]
  have hWz : W = Subgroup.zpowers a := by
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le, ha]
      exact g.2
    · simp only [hW, Nat.card_zpowers, haord, le_refl]
  obtain ⟨⟨eTU⟩, -, -, -, hnf, hff, -, hFker, -, hinn, hDI⟩ :=
    unitary_prime_form_full_semilinear_realization h hC hn3 hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hT
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hD
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner T with hI
  have hID : I ≤ D := fun α hα => by
    obtain ⟨s, rfl⟩ := (hinn α).1 hα
    exact ⟨_, rfl⟩
  have hDcop : Nat.Coprime (Nat.card D) 7 := by
    rw [← Subgroup.relIndex_mul_card I D, inf_of_le_left hID]
    exact Nat.Coprime.mul_left
      (Nat.Coprime.coprime_dvd_left hDI
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_seven).2 hqp).symm)
      (CFSG.RankThree.Automorphisms.coprime_card_inner (G := primeFormP h
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) Nat.prime_seven h7T)
  have haD : a ∉ D := fun haDmem => by
    have hdvd := orderOf_dvd_natCard (⟨a, haDmem⟩ : D)
    rw [Subgroup.orderOf_mk, haord] at hdvd
    exact Nat.prime_seven.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hDcop.symm hdvd)
  let σ : K ≃+* K := primeFormFieldFactor h hC hn3 hq a
  have hσ1 : σ ≠ 1 := fun h1 => haD (by rw [← hFker]; exact h1)
  have ha7 : a ^ 7 = 1 := by rw [← haord]; exact pow_orderOf_eq_one a
  have hσ7 : σ ^ 7 = 1 := by
    change (primeFormFieldFactor h hC hn3 hq a) ^ 7 = 1
    rw [← map_pow, ha7, map_one]
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hσord : orderOf σ = 7 := orderOf_eq_prime hσ7 hσ1
  obtain ⟨hpf, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hq
      Nat.prime_seven (by norm_num) hℓne a haord σ rfl hσord
  let φ : MulAut T := primeFormFieldHom h hC σ
  let gT : MulAut T := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M
  have hφ7 : φ ^ 7 = 1 := by
    change (primeFormFieldHom h hC σ) ^ 7 = 1
    rw [← map_pow, hσ7, map_one]
  have hφ1 : φ ≠ 1 := by
    intro h1
    apply hσ1
    have h2 : primeFormFieldFactor h hC hn3 hq (primeFormFieldHom h hC σ) = σ := by
      simpa using hff 1 σ
    have h1' : primeFormFieldHom h hC σ = 1 := h1
    rw [h1', map_one] at h2
    exact h2.symm
  have hφord : orderOf φ = 7 := orderOf_eq_prime hφ7 hφ1
  have hWa : a = MulAut.conj gT φ := by
    rw [MulAut.conj_apply]
    change a = (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M) *
      primeFormFieldHom h hC σ *
      (primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹
    rw [← hM]
    group
  have hWφ : W = (Subgroup.zpowers φ).map (MulAut.conj gT).toMonoidHom := by
    rw [hWz, hWa]
    exact (MonoidHom.map_zpowers (f := (MulAut.conj gT).toMonoidHom) φ).symm
  refine ⟨gT, φ, hφord, hWφ, k330c_fieldRigid_zpowers h hn hσord,
    k330c_fieldPair_zpowers h hn hσord, ℓ ^ (f / 7), ?_, ?_⟩
  · rw [← pow_mul, Nat.div_mul_cancel hpf]
  · rw [k330c_fixedBy_zpowers_eq_fieldFixedPSU (n := n) h σ]
    exact k330c_card_fieldFixedPSU_le h hn hσord

private theorem k330c_hasFieldRP_of_mulEquiv {J T : Type} [Group J] [Finite J] [Group T]
    [Finite T] (e : J ≃* T) {Q : ℕ} {B : ℕ → ℕ} (h : HasFieldRP T Q B) :
    HasFieldRP J Q B := by
  intro W hW h7J
  let W' : Subgroup (MulAut T) := W.map (MulAut.congr e).toMonoidHom
  have hW'card : Nat.card W' = 7 := by
    dsimp only [W']
    rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hW]
  have h7T : ¬ 7 ∣ Nat.card T := by rwa [← Nat.card_congr e.toEquiv]
  obtain ⟨g', φ', hφ'ord, hW'eq, hrig', hpair', k, hk, hbound'⟩ := h W' hW'card h7T
  let g : MulAut J := (MulAut.congr e).symm g'
  let φ : MulAut J := (MulAut.congr e).symm φ'
  have hφ : MulAut.congr e φ = φ' := by
    dsimp only [φ]
    exact MulEquiv.apply_symm_apply (MulAut.congr e) φ'
  obtain ⟨hrig, hpair⟩ := k330c_fieldRigidPair_congr e hrig' hpair'
  refine ⟨g, φ, ?_, ?_, hrig, hpair, k, hk, ?_⟩
  · rw [← MulEquiv.orderOf_eq (MulAut.congr e) φ, hφ, hφ'ord]
  · have hback : W'.map (MulAut.congr e).symm.toMonoidHom = W := by
      have hW'def : W' = W.map (MulAut.congr e).toMonoidHom := rfl
      rw [hW'def, Subgroup.map_map]
      have hcomp : (MulAut.congr e).symm.toMonoidHom.comp (MulAut.congr e).toMonoidHom =
          MonoidHom.id (MulAut J) := by
        ext x; simp
      rw [hcomp, Subgroup.map_id]
    rw [← hback, hW'eq, Subgroup.map_map]
    have hcomp2 : ((MulAut.congr e).symm.toMonoidHom).comp (MulAut.conj g').toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.congr e).symm.toMonoidHom := by
      ext w
      simp [MulAut.conj_apply, map_mul, g]
    rw [hcomp2, ← Subgroup.map_map, MonoidHom.map_zpowers]
    rfl
  · have hfix : (fixedBy (Subgroup.zpowers φ)).map e.toMonoidHom =
        fixedBy (Subgroup.zpowers φ') := by
      rw [fixedBy_map_congr e (Subgroup.zpowers φ)]
      have hz : (Subgroup.zpowers φ).map (MulAut.congr e).toMonoidHom =
          Subgroup.zpowers φ' := by
        rw [MonoidHom.map_zpowers]
        simp only [MulEquiv.coe_toMonoidHom]
        rw [hφ]
      rw [hz]
    have hcard : Nat.card (fixedBy (Subgroup.zpowers φ)) =
        Nat.card (fixedBy (Subgroup.zpowers φ')) := by
      rw [← hfix, Subgroup.card_map_of_injective e.injective]
    rwa [hcard]

theorem hasFieldRP_PSU (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type}
    [Group J] [Finite J] {p f : ℕ} (e : LieModel J .PSU n p f) :
    HasFieldRP J (p ^ f) (sltBound n) := by
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> norm_num
  obtain ⟨⟨hprime, hf1, -, -⟩, K, hKfield, hKfin, hKcard, ⟨eSU⟩⟩ :=
    LieModel.statedClassicalModel_of_ne_zero hn0 e
  letI : Field K := hKfield
  haveI : Finite K := hKfin
  have h : UnitaryFieldData p f K :=
    { prime := hprime
      one_le := hf1
      card := by rw [hKcard, ← pow_mul, mul_comm] }
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := n))
  let eJ : J ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    eSU.trans ((unitaryPSUEquiv h (by omega)).symm.trans eP.symm)
  exact k330c_hasFieldRP_of_mulEquiv eJ (k330c_hasFieldRP_primeFormP h hn)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
