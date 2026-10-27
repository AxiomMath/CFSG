module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.U3Defs
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUOddAll
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.KSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LieType.Chevalley (fixSubfield)
open CFSG.RankThree.Classical CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.CTP

private theorem ksu3f_fixedBy_zpowers_eq_fieldFixedPSU {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (σ : K ≃+* K) :
    fixedBy (Subgroup.zpowers (u3Field h σ)) = fieldFixedPSU h 3 σ := by
  ext x
  rw [mem_fixedBy]
  constructor
  · intro hx
    exact hx _ (Subgroup.mem_zpowers _)
  · intro hx w hw
    have h1 := smul_eq_self_of_mem_zpowers (G := MulAut (U3 h)) hw hx
    rwa [MulAut.smul_def] at h1

theorem u3_fixedBy_zpowers_equiv {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (σ : K ≃+* K) (hσ : orderOf σ = 7) :
    ∃ (f₀ : ℕ) (h₀ : UnitaryFieldData p f₀ ↥(fixSubfield σ)), f = 7 * f₀ ∧
      Nonempty (↥(fixedBy (Subgroup.zpowers (u3Field h σ))) ≃* U3 h₀) ∧
      IsSimpleGroup ↥(fixedBy (Subgroup.zpowers (u3Field h σ))) ∧
      ∃ a b : ↥(fixedBy (Subgroup.zpowers (u3Field h σ))), a * b ≠ b * a := by
  classical
  have hq' : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    norm_num at hq
  obtain ⟨hpf, -, -, hinj, hrange, -, -, -, -, hsimple, -⟩ :=
    higher_unitary_prime_subfield_fixed_group_and_full_centralizer (ℓ := p) (f := f) (n := 3)
      (p := 7) h (by norm_num) (by norm_num) Nat.prime_seven hq' σ hσ
  have hq₀ : ¬(3 = 3 ∧ p ^ (f / 7) = 2) := by
    rintro ⟨-, h2⟩
    have hf_eq : f = 7 * (f / 7) := (Nat.mul_div_cancel' hpf).symm
    have hpow : p ^ f = (p ^ (f / 7)) ^ 7 := by
      conv_lhs => rw [hf_eq]
      rw [mul_comm, pow_mul]
    rw [hpow, h2] at hq
    norm_num at hq
  have hF_eq : fixedBy (Subgroup.zpowers (u3Field h σ)) = fieldFixedPSU h 3 σ :=
    ksu3f_fixedBy_zpowers_eq_fieldFixedPSU h σ
  refine ⟨f / 7, fixSubfield_unitaryFieldData h Nat.prime_seven (by norm_num) hσ,
    (Nat.mul_div_cancel' hpf).symm, ?_, ?_, ?_⟩
  · exact ⟨(MulEquiv.subgroupCongr hF_eq).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩
  · haveI : IsSimpleGroup ↥(fieldFixedPSU h 3 σ) := (hsimple hq₀).1
    exact (MulEquiv.subgroupCongr hF_eq).isSimpleGroup
  · obtain ⟨a, ha⟩ := not_forall.mp (hsimple hq₀).2.1
    obtain ⟨b, hab⟩ := not_forall.mp ha
    exact ⟨(MulEquiv.subgroupCongr hF_eq).symm a, (MulEquiv.subgroupCongr hF_eq).symm b,
      fun hh => hab (by simpa using congrArg (MulEquiv.subgroupCongr hF_eq) hh)⟩

theorem u3_mem_zpowers_of_fixes {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : p ^ f % 3 = 1) (σ : K ≃+* K) (hσ : orderOf σ = 7)
    (α : MulAut (U3 h)) (hα : ∀ x ∈ fixedBy (Subgroup.zpowers (u3Field h σ)), α x = x) :
    α ∈ Subgroup.zpowers (u3Field h σ) := by
  classical
  have hq' : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    norm_num at hq
  obtain ⟨hpf, -, -, -, -, -, -, -, -, hsimple, -⟩ :=
    higher_unitary_prime_subfield_fixed_group_and_full_centralizer (ℓ := p) (f := f) (n := 3)
      (p := 7) h (by norm_num) (by norm_num) Nat.prime_seven hq' σ hσ
  have hq₀ : ¬(3 = 3 ∧ p ^ (f / 7) = 2) := by
    rintro ⟨-, h2⟩
    have hf_eq : f = 7 * (f / 7) := (Nat.mul_div_cancel' hpf).symm
    have hpow : p ^ f = (p ^ (f / 7)) ^ 7 := by
      conv_lhs => rw [hf_eq]
      rw [mul_comm, pow_mul]
    rw [hpow, h2] at hq
    norm_num at hq
  obtain ⟨-, -, hfixing, hmapfix, -⟩ := hsimple hq₀
  have hF_eq : fixedBy (Subgroup.zpowers (u3Field h σ)) = fieldFixedPSU h 3 σ :=
    ksu3f_fixedBy_zpowers_eq_fieldFixedPSU h σ
  have hmem : α ∈ fixingSubgroup (MulAut (U3 h)) (fieldFixedPSU h 3 σ : Set (U3 h)) := by
    refine (mem_fixingSubgroup_iff _).2 fun x hx => ?_
    rw [MulAut.smul_def]
    exact hα x (by rw [hF_eq]; exact hx)
  rw [hfixing, hmapfix] at hmem
  exact hmem

theorem u3_fixedBy_sup_conj_eq_top {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (σ : K ≃+* K) (hσ : orderOf σ = 7)
    (x : U3 h)
    (hne : (fixedBy (Subgroup.zpowers (u3Field h σ))).map (MulAut.conj x).toMonoidHom ≠
      fixedBy (Subgroup.zpowers (u3Field h σ))) :
    fixedBy (Subgroup.zpowers (u3Field h σ)) ⊔
      (fixedBy (Subgroup.zpowers (u3Field h σ))).map (MulAut.conj x).toMonoidHom = ⊤ := by
  classical
  have hq' : ¬(3 = 3 ∧ p ^ f = 2) := by
    rintro ⟨-, h2⟩
    rw [h2] at hq
    norm_num at hq
  obtain ⟨hpf, -, -, -, hrange, -, -, -, -, -, -⟩ :=
    higher_unitary_prime_subfield_fixed_group_and_full_centralizer (ℓ := p) (f := f) (n := 3)
      (p := 7) h (by norm_num) (by norm_num) Nat.prime_seven hq' σ hσ
  have hq₀ : ¬(3 = 3 ∧ p ^ (f / 7) = 2) := by
    rintro ⟨-, h2⟩
    have hf_eq : f = 7 * (f / 7) := (Nat.mul_div_cancel' hpf).symm
    have hpow : p ^ f = (p ^ (f / 7)) ^ 7 := by
      conv_lhs => rw [hf_eq]
      rw [mul_comm, pow_mul]
    rw [hpow, h2] at hq
    norm_num at hq
  have hF_eq : fixedBy (Subgroup.zpowers (u3Field h σ)) = fieldFixedPSU h 3 σ :=
    ksu3f_fixedBy_zpowers_eq_fieldFixedPSU h σ
  set h₀ := fixSubfield_unitaryFieldData h Nat.prime_seven (by norm_num) hσ with hh₀
  set hbar₀ := fixSubfield_unitaryFieldData_bar h Nat.prime_seven (by norm_num) hσ with hhb
  set N := normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3 with hN
  have hsu_range : (suSub h h₀ hbar₀ 3).map (QuotientGroup.mk' N) = fieldFixedPSU h 3 σ := by
    rw [← range_subfieldPSU_eq_map h h₀ hbar₀ 3]
    exact hrange
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective N x
  have hg₀' : (g₀ : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = x := hg₀
  set A : primeFormUnitary h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    ⟨g₀, (Iff.mp (mem_gramSU_iff_unitary (h := h)
      (C := ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) g₀.2).1⟩ with hA
  have hconj : MulAut.conj x =
      primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A := by
    refine MulEquiv.ext fun y => QuotientGroup.induction_on y fun g => ?_
    rw [primeFormConjHom_mk, MulAut.conj_apply, ← hg₀', ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hne1 : (fieldFixedPSU h 3 σ).map (primeFormConjHom h
      ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A).toMonoidHom ≠
      fieldFixedPSU h 3 σ := by
    rw [hF_eq] at hne
    rw [hconj] at hne
    exact hne
  have hne2 : ((suSub h h₀ hbar₀ 3).map
      (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A).toMonoidHom).map
      (QuotientGroup.mk' N) ≠ (suSub h h₀ hbar₀ 3).map (QuotientGroup.mk' N) := by
    rw [← hsu_range] at hne1
    rwa [map_primeFormConjHom_map_mk] at hne1
  have hne_su : (suSub h h₀ hbar₀ 3).map
      (primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) A).toMonoidHom ≠
      suSub h h₀ hbar₀ 3 := by
    intro hh
    exact hne2 (by rw [hh])
  have hpair := CFSG.LieType.SeitzGeneration.subfieldPairSUOdd_of_not_three_two p f (f / 7) K h
    (fixSubfield σ) h₀ hbar₀ 7 Nat.prime_seven (by norm_num) (Nat.mul_div_cancel' hpf).symm 3
    (by norm_num) hq₀ A hne_su
  have h4 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hpair
  rw [map_closure_union, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h4
  rw [hF_eq, hconj, ← hsu_range, map_primeFormConjHom_map_mk, Subgroup.sup_eq_closure]
  exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Seven
