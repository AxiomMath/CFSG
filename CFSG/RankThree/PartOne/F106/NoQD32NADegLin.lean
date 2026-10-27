module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

public section

namespace CFSG.RankThree.PartOne.F106.NAD

open Module Module.End

section Sums

variable {L : Type*} [Field L] {M : Type*} [AddCommGroup M] [Module L M] [FiniteDimensional L M]

theorem finrank_biSup_eq_sum {ι : Type*} [DecidableEq ι] (p : ι → Submodule L M)
    (hp : iSupIndep p) (s : Finset ι) :
    finrank L ↥(⨆ i ∈ s, p i) = ∑ i ∈ s, finrank L ↥(p i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hdisj : Disjoint (p a) (⨆ i ∈ s, p i) := by
      refine (iSupIndep_def.1 hp a).mono_right ?_
      refine iSup₂_le fun i hi => ?_
      exact le_iSup₂_of_le i (fun h => ha (h ▸ hi)) le_rfl
    have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (⨆ i ∈ s, p i)
    rw [disjoint_iff.1 hdisj, finrank_bot, add_zero] at h
    rw [Finset.iSup_insert, Finset.sum_insert ha, ← ih]
    exact h

theorem sum_finrank_le {ι : Type*} (p : ι → Submodule L M) (hp : iSupIndep p) (s : Finset ι) :
    ∑ i ∈ s, finrank L ↥(p i) ≤ finrank L M := by
  classical
  rw [← finrank_biSup_eq_sum p hp s]
  exact Submodule.finrank_le _

end Sums

section Eigen

variable {L : Type*} [Field L] {M : Type*} [AddCommGroup M] [Module L M] [FiniteDimensional L M]

theorem mul_finrank_eigenspace_le {q : ℕ} (hq : q.Prime) (A B : Module.End L M)
    (hB : Function.Injective B) {ζ : L} (hζ : ζ ^ q = 1) (hζ1 : ζ ≠ 1)
    (hAB : ∀ v, A (B v) = ζ • B (A v)) {l : L} (hl : l ≠ 0) :
    q * finrank L ↥(A.eigenspace l) ≤ finrank L M := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hord : orderOf ζ = q := orderOf_eq_prime hζ hζ1
  have hshift : ∀ n : ℕ, ∀ v ∈ A.eigenspace l, (B ^ n) v ∈ A.eigenspace (ζ ^ n * l) := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      have h1 := mem_eigenspace_iff.1 (ih v hv)
      have e1 : (B ^ (n + 1)) v = B ((B ^ n) v) := by rw [pow_succ']; rfl
      rw [mem_eigenspace_iff, e1, hAB, h1, map_smul, smul_smul, pow_succ', mul_assoc]
  have hTinj : ∀ i : ℕ, Function.Injective ((B ^ i).restrict (hshift i)) := by
    intro i x y hxy
    have h1 : (B ^ i) (x : M) = (B ^ i) (y : M) := congrArg Subtype.val hxy
    have hBi : Function.Injective (B ^ i) := by
      rw [Module.End.coe_pow]
      exact hB.iterate i
    exact Subtype.ext (hBi h1)
  have hdim : ∀ i : ℕ, finrank L ↥(A.eigenspace l) ≤ finrank L ↥(A.eigenspace (ζ ^ i * l)) :=
    fun i => LinearMap.finrank_le_finrank_of_injective (hTinj i)
  have hinj : Function.Injective (fun i : Fin q => ζ ^ (i : ℕ) * l) := by
    intro i j hij
    have h1 : ζ ^ (i : ℕ) = ζ ^ (j : ℕ) := mul_right_cancel₀ hl hij
    have hi : (i : ℕ) ∈ Set.Iio (orderOf ζ) := by rw [hord]; exact i.2
    have hj : (j : ℕ) ∈ Set.Iio (orderOf ζ) := by rw [hord]; exact j.2
    exact Fin.ext (pow_injOn_Iio_orderOf hi hj h1)
  set s : Finset L := Finset.image (fun i : Fin q => ζ ^ (i : ℕ) * l) Finset.univ with hs
  have hcard : s.card = q := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hsum := sum_finrank_le A.eigenspace A.eigenspaces_iSupIndep s
  have hlow : s.card • finrank L ↥(A.eigenspace l) ≤ ∑ μ ∈ s, finrank L ↥(A.eigenspace μ) :=
    Finset.card_nsmul_le_sum s _ _ fun μ hμ => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hμ
      exact hdim i
  rw [hcard, smul_eq_mul] at hlow
  exact hlow.trans hsum

omit [FiniteDimensional L M] in
theorem ne_zero_of_hasEigenvalue {A : Module.End L M} (hA : Function.Injective A) {l : L}
    (hl : A.HasEigenvalue l) : l ≠ 0 := by
  rintro rfl
  obtain ⟨v, hv, hv0⟩ := hl.exists_hasEigenvector
  rw [mem_eigenspace_iff, zero_smul] at hv
  exact hv0 (hA (hv.trans (map_zero A).symm))

variable [IsAlgClosed L] [Nontrivial M]

theorem le_finrank_of_pair {q : ℕ} (hq : q.Prime) (A B : Module.End L M)
    (hA : Function.Injective A) (hB : Function.Injective B) {ζ : L} (hζ : ζ ^ q = 1)
    (hζ1 : ζ ≠ 1) (hAB : ∀ v, A (B v) = ζ • B (A v)) : q ≤ finrank L M := by
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue A
  have h1 : 1 ≤ finrank L ↥(A.eigenspace l) :=
    Submodule.one_le_finrank_iff.2 (hasEigenvalue_iff.1 hl)
  calc q = q * 1 := (mul_one q).symm
    _ ≤ q * finrank L ↥(A.eigenspace l) := Nat.mul_le_mul_left q h1
    _ ≤ finrank L M :=
      mul_finrank_eigenspace_le hq A B hB hζ hζ1 hAB (ne_zero_of_hasEigenvalue hA hl)

theorem sq_le_finrank_of_two_pairs {q : ℕ} (hq : q.Prime) (A₁ B₁ A₂ B₂ : Module.End L M)
    (hA₁ : Function.Injective A₁) (hB₁ : Function.Injective B₁) (hA₂ : Function.Injective A₂)
    (hB₂ : Function.Injective B₂) {ζ₁ ζ₂ : L} (hζ₁ : ζ₁ ^ q = 1) (hζ₁1 : ζ₁ ≠ 1)
    (hζ₂ : ζ₂ ^ q = 1) (hζ₂1 : ζ₂ ≠ 1) (h₁ : ∀ v, A₁ (B₁ v) = ζ₁ • B₁ (A₁ v))
    (h₂ : ∀ v, A₂ (B₂ v) = ζ₂ • B₂ (A₂ v)) (hc₁ : ∀ v, A₁ (A₂ v) = A₂ (A₁ v))
    (hc₂ : ∀ v, A₁ (B₂ v) = B₂ (A₁ v)) : q ^ 2 ≤ finrank L M := by
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue A₁
  have hl0 : l ≠ 0 := ne_zero_of_hasEigenvalue hA₁ hl
  have hEne : A₁.eigenspace l ≠ ⊥ := hasEigenvalue_iff.1 hl
  have : Nontrivial ↥(A₁.eigenspace l) := Submodule.nontrivial_iff_ne_bot.2 hEne
  have hmap : ∀ C : Module.End L M, (∀ v, A₁ (C v) = C (A₁ v)) →
      ∀ v ∈ A₁.eigenspace l, C v ∈ A₁.eigenspace l := by
    intro C hC v hv
    rw [mem_eigenspace_iff] at hv ⊢
    rw [hC, hv, map_smul]
  let A₂E : Module.End L ↥(A₁.eigenspace l) := A₂.restrict (hmap A₂ hc₁)
  let B₂E : Module.End L ↥(A₁.eigenspace l) := B₂.restrict (hmap B₂ hc₂)
  have hq' : q ≤ finrank L ↥(A₁.eigenspace l) := by
    refine le_finrank_of_pair hq A₂E B₂E ?_ ?_ hζ₂ hζ₂1 ?_
    · intro x y hxy
      exact Subtype.ext (hA₂ (congrArg Subtype.val hxy))
    · intro x y hxy
      exact Subtype.ext (hB₂ (congrArg Subtype.val hxy))
    · intro v
      exact Subtype.ext (h₂ (v : M))
  calc q ^ 2 = q * q := sq q
    _ ≤ q * finrank L ↥(A₁.eigenspace l) := Nat.mul_le_mul_left q hq'
    _ ≤ finrank L M := mul_finrank_eigenspace_le hq A₁ B₁ hB₁ hζ₁ hζ₁1 h₁ hl0

end Eigen

end CFSG.RankThree.PartOne.F106.NAD
