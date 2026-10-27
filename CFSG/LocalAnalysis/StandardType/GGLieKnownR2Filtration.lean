module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open
open scoped commutatorElement Pointwise

section Generic

variable {X : Type*} [Group X]

private theorem conj_mem_coset {A : Subgroup X} {g b y : X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) (hb : ⁅b, g⁆ ∈ A) (hy : y * b⁻¹ ∈ A) :
    g * y * g⁻¹ * b⁻¹ ∈ A := by
  have h1 : g * (y * b⁻¹) * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg _).mp hy
  have h2 : ⁅g, b⁆ ∈ A := by
    rw [← commutatorElement_inv]
    exact A.inv_mem hb
  have h3 := A.mul_mem h1 h2
  have e : g * (y * b⁻¹) * g⁻¹ * ⁅g, b⁆ = g * y * g⁻¹ * b⁻¹ := by
    simp only [commutatorElement_def]
    group
  rwa [e] at h3

theorem exists_mem_inf_centralizer_of_commutator_mem [Finite X] {r : ℕ} (hr : r.Prime) {h : X}
    (hh : orderOf h = r) {A : Subgroup X} (hA : ¬ r ∣ Nat.card A)
    (hhA : h ∈ Subgroup.normalizer (A : Set X)) {b : X} (hb : ⁅b, h⁆ ∈ A) :
    ∃ y : X, y * b⁻¹ ∈ A ∧ h * y = y * h := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hhinvA : h⁻¹ ∈ Subgroup.normalizer (A : Set X) := inv_mem hhA
  have hbinv : ⁅b, h⁻¹⁆ ∈ A := by
    have h1 : h⁻¹ * ⁅h, b⁆ * h ∈ A := by
      have h2 : ⁅h, b⁆ ∈ A := by
        rw [← commutatorElement_inv]
        exact A.inv_mem hb
      simpa using (Subgroup.mem_normalizer_iff.mp hhinvA _).mp h2
    have e : ⁅b, h⁻¹⁆ = (h⁻¹ * ⁅h, b⁆ * h) := by
      simp only [commutatorElement_def]
      group
    rwa [e]
  let S : Type _ := {y : X // y * b⁻¹ ∈ A}
  let σ : Equiv.Perm S :=
    { toFun := fun y => ⟨h * y.1 * h⁻¹, conj_mem_coset hhA hb y.2⟩
      invFun := fun y => ⟨h⁻¹ * y.1 * h⁻¹⁻¹, conj_mem_coset hhinvA hbinv y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc]) }
  have hσpow : ∀ (m : ℕ) (y : S), ((σ ^ m) y).1 = h ^ m * y.1 * (h ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      change h ^ m * (h * y.1 * h⁻¹) * (h ^ m)⁻¹ = h ^ (m + 1) * y.1 * (h ^ (m + 1))⁻¹
      rw [pow_succ, mul_inv_rev]
      group
  have hσr : σ ^ r = 1 := by
    ext y
    rw [hσpow, ← hh, pow_orderOf_eq_one]
    simp
  have hG : IsPGroup r (Subgroup.zpowers σ) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσr, one_zpow]
  have hcard : Nat.card S = Nat.card A :=
    Nat.card_congr
      { toFun := fun y => ⟨y.1 * b⁻¹, y.2⟩
        invFun := fun a => ⟨a.1 * b, by simp⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun a => Subtype.ext (by simp) }
  obtain ⟨y, hy⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card S (by rwa [hcard])
  have hfix : σ y = y := hy ⟨σ, Subgroup.mem_zpowers σ⟩
  refine ⟨y.1, y.2, ?_⟩
  have h1 : h * y.1 * h⁻¹ = y.1 := congrArg Subtype.val hfix
  calc h * y.1 = h * y.1 * h⁻¹ * h := by group
    _ = y.1 * h := by rw [h1]

end Generic

section GG

variable {X : Type} [Group X]

theorem noCentral_of_fixedPoint [Finite X] {K R : Subgroup X} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {h : X} (hh : orderOf h = r) (hhN : h ∈ K ⊓ Subgroup.normalizer (R : Set X))
    (hfix : ∀ y ∈ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set X)), h * y = y * h → y ∈ R) :
    GGRootNoCentralAt K R := by
  intro A B' hRA hAB hBp hNA hNB hcomm
  intro b hb
  have hA2 : IsPGroup 2 A :=
    ((GGRootNorm.isPGroup_pCoreOf (K ⊓ Subgroup.normalizer (R : Set X))).to_le
      (hAB.trans hBp))
  obtain ⟨n, hn⟩ := hA2.exists_card_eq
  have hrA : ¬ r ∣ Nat.card A := by
    rw [hn]
    intro hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hdvd))
  have hbh : ⁅b, h⁆ ∈ A := hcomm (Subgroup.commutator_mem_commutator hb hhN)
  obtain ⟨y, hyA, hyh⟩ :=
    exists_mem_inf_centralizer_of_commutator_mem hr hh hrA (hNA hhN) hbh
  have hyQ : y ∈ pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set X)) := by
    have : y = (y * b⁻¹) * b := by group
    rw [this]
    exact Subgroup.mul_mem _ (hBp (hAB hyA)) (hBp hb)
  have hyR : y ∈ R := hfix y hyQ hyh
  have : b = (y * b⁻¹)⁻¹ * y := by group
  rw [this]
  exact A.mul_mem (A.inv_mem hyA) (hRA hyR)

end GG

end CFSG.StandardType.LieKnownR2
