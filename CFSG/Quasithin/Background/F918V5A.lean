module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open scoped Pointwise

@[instance_reducible] private def core3QuotAction {P A : Type*} [Group P] [CommGroup A]
    [MulDistribMulAction P A] (B : Subgroup A) (hB : ∀ p : P, ∀ b ∈ B, p • b ∈ B) :
    MulAction P (A ⧸ B) where
  smul p := QuotientGroup.map B B (MulDistribMulAction.toMonoidHom A p) (fun b hb => hB p b hb)
  one_smul c := QuotientGroup.induction_on c fun a => by
    change (QuotientGroup.mk ((1 : P) • a) : A ⧸ B) = QuotientGroup.mk a
    rw [one_smul]
  mul_smul p p' c := QuotientGroup.induction_on c fun a => by
    change (QuotientGroup.mk ((p * p') • a) : A ⧸ B) = QuotientGroup.mk (p • p' • a)
    rw [mul_smul]

theorem core3_exists_fixed_coset {P A : Type*} [Group P] [CommGroup A] [Finite A]
    [MulDistribMulAction P A] (hP : IsPGroup 2 P) (hexp : ∀ a : A, a ^ 2 = 1) (B : Subgroup A)
    (hB : ∀ p : P, ∀ b ∈ B, p • b ∈ B) (hne : B ≠ ⊤) :
    ∃ a : A, a ∉ B ∧ ∀ p : P, p • a * a⁻¹ ∈ B := by
  let _ : MulAction P (A ⧸ B) := core3QuotAction B hB
  have hsmul : ∀ (p : P) (a : A), p • (QuotientGroup.mk a : A ⧸ B) = QuotientGroup.mk (p • a) :=
    fun _ _ => rfl
  obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ∉ B := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_top_iff.2 fun a _ => hcon a)
  have hdvd : 2 ∣ Nat.card (A ⧸ B) := by
    have h1 : (QuotientGroup.mk a₀ : A ⧸ B) ≠ 1 := fun h => ha₀ ((QuotientGroup.eq_one_iff a₀).1 h)
    have h2 : (QuotientGroup.mk a₀ : A ⧸ B) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, hexp a₀, QuotientGroup.mk_one]
    have h3 : orderOf (QuotientGroup.mk a₀ : A ⧸ B) = 2 := orderOf_eq_prime h2 h1
    exact h3 ▸ orderOf_dvd_natCard _
  have hfix : (1 : A ⧸ B) ∈ MulAction.fixedPoints P (A ⧸ B) := fun p => by
    rw [← QuotientGroup.mk_one, hsmul, smul_one]
  obtain ⟨b, hb, hb1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (A ⧸ B) hdvd hfix
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, fun ha => hb1 ?_, fun p => ?_⟩
  · exact ((QuotientGroup.eq_one_iff a).2 ha).symm
  · have h1 : p • (QuotientGroup.mk a : A ⧸ B) = QuotientGroup.mk a := hb p
    rw [hsmul] at h1
    have h2 := (QuotientGroup.eq_iff_div_mem).1 h1
    rwa [div_eq_mul_inv] at h2

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[instance_reducible] private def core3SubAction {P : Subgroup Γ} (A : Subgroup Q)
    (hA : ∀ p ∈ P, ∀ x ∈ A, p • x ∈ A) : MulDistribMulAction ↥P ↥A where
  smul p x := ⟨(p : Γ) • (x : Q), hA p p.2 x x.2⟩
  one_smul x := Subtype.ext (one_smul Γ (x : Q))
  mul_smul p p' x := Subtype.ext (mul_smul (p : Γ) (p' : Γ) (x : Q))
  smul_mul p x y := Subtype.ext (smul_mul' (p : Γ) (x : Q) (y : Q))
  smul_one p := Subtype.ext (smul_one (p : Γ))

theorem core3_exists_fixed_coset_sub [Finite Q] (hexp : ∀ x : Q, x ^ 2 = 1) {P : Subgroup Γ}
    (hP : IsPGroup 2 ↥P) {A B : Subgroup Q} (hA : ∀ p ∈ P, ∀ x ∈ A, p • x ∈ A)
    (hB : ∀ p ∈ P, ∀ x ∈ B, p • x ∈ B) (hBA : B ≤ A) (hne : B ≠ A) :
    ∃ x ∈ A, x ∉ B ∧ ∀ p ∈ P, p • x * x⁻¹ ∈ B := by
  let _ : MulDistribMulAction ↥P ↥A := core3SubAction A hA
  have hB' : ∀ p : ↥P, ∀ b ∈ B.subgroupOf A, p • b ∈ B.subgroupOf A := fun p b hb =>
    Subgroup.mem_subgroupOf.2 (hB p p.2 b (Subgroup.mem_subgroupOf.1 hb))
  have hne' : B.subgroupOf A ≠ ⊤ := fun h =>
    hne (le_antisymm hBA (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨a, ha, hfix⟩ := core3_exists_fixed_coset hP (fun a : ↥A => Subtype.ext (hexp a))
    (B.subgroupOf A) hB' hne'
  refine ⟨a, a.2, fun h => ha (Subgroup.mem_subgroupOf.2 h), fun p hp => ?_⟩
  exact Subgroup.mem_subgroupOf.1 (hfix ⟨p, hp⟩)

end CFSG.Quasithin
