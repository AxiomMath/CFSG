module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.Quasithin

namespace S143

section Simple

variable {G : Type*} [Group G]

theorem commutator_top_eq_top_of_simple (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤ := by
  have hn : (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).Normal := inferInstance
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ hG _ hn with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

end Simple

section TwoSteps

variable {G : Type*} [Group G]

theorem commutator_mem_of_two_steps {T P Q : Subgroup G} {d t₀ : G}
    (hPn : ∀ t ∈ T, ∀ p ∈ P, t * p * t⁻¹ ∈ P) (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q)
    (hQT : Q ≤ T) (ht₀ : t₀ ∈ T)
    (hTQ : ∀ a ∈ T, a ∈ Q ∨ t₀⁻¹ * a ∈ Q) (hQP : ∀ q ∈ Q, q ∈ P ∨ d⁻¹ * q ∈ P)
    (hdQ : d ∈ Q) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ P := by
  classical
  have hdT : d ∈ T := hQT hdQ
  let P' : Subgroup T := P.subgroupOf T
  have hP'n : P'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hPn g g.2 n hn⟩
  let dd : T := ⟨d, hdT⟩
  let tt : T := ⟨t₀, ht₀⟩
  have hmem : ∀ a : T, a ∈ P' ↔ (a : G) ∈ P := fun a => Subgroup.mem_subgroupOf
  have hcen : ∀ b : T, Commute (dd : T ⧸ P') (b : T ⧸ P') := by
    intro b
    have hq : (b : G) * d * (b : G)⁻¹ ∈ Q := hQn b b.2 d hdQ
    rcases hQP _ hq with h | h
    · have hdP : d ∈ P := by
        have := hPn (b : G)⁻¹ ((Subgroup.inv_mem _) b.2) _ h
        simpa [mul_assoc] using this
      have h1 : (dd : T ⧸ P') = 1 := (QuotientGroup.eq_one_iff dd).mpr ((hmem dd).mpr hdP)
      rw [h1]
      exact Commute.one_left _
    · have h2 : ((dd : T ⧸ P') = ((b * dd * b⁻¹ : T) : T ⧸ P')) := by
        rw [QuotientGroup.eq]
        exact (hmem _).mpr (by simpa using h)
      have h3 : (dd : T ⧸ P') * (b : T ⧸ P') = (b : T ⧸ P') * (dd : T ⧸ P') := by
        calc (dd : T ⧸ P') * (b : T ⧸ P') = ((b * dd * b⁻¹ : T) : T ⧸ P') * (b : T ⧸ P') := by
              rw [← h2]
          _ = (b : T ⧸ P') * (dd : T ⧸ P') := by
              simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_assoc]
      exact h3
  have hall : ∀ γ : T ⧸ P', γ = 1 ∨ γ = dd ∨ γ = tt ∨ γ = (tt : T ⧸ P') * dd := by
    intro γ
    induction γ using QuotientGroup.induction_on with
    | H a =>
      rcases hTQ a a.2 with ha | ha
      · rcases hQP _ ha with h | h
        · left
          exact (QuotientGroup.eq_one_iff a).mpr ((hmem a).mpr h)
        · right; left
          symm
          rw [QuotientGroup.eq]
          exact (hmem _).mpr (by simpa using h)
      · rcases hQP _ ha with h | h
        · right; right; left
          symm
          rw [QuotientGroup.eq]
          exact (hmem _).mpr (by simpa using h)
        · right; right; right
          rw [← QuotientGroup.mk_mul]
          symm
          rw [QuotientGroup.eq]
          refine (hmem _).mpr ?_
          have e : (((tt * dd : T)⁻¹ * a : T) : G) = d⁻¹ * (t₀⁻¹ * (a : G)) := by
            simp [tt, dd, mul_assoc]
          rw [e]
          exact h
  have hcomm : ∀ γ δ : T ⧸ P', Commute γ δ := by
    intro γ δ
    have hd : ∀ γ : T ⧸ P', Commute (dd : T ⧸ P') γ := by
      intro γ
      induction γ using QuotientGroup.induction_on with
      | H b => exact hcen b
    rcases hall γ with rfl | rfl | rfl | rfl <;> rcases hall δ with rfl | rfl | rfl | rfl
    all_goals first
      | exact Commute.one_left _
      | exact Commute.one_right _
      | exact hd _
      | exact (hd _).symm
      | exact Commute.refl _
      | exact (Commute.refl _).mul_right (hd _).symm
      | exact (Commute.refl _).mul_left (hd _).symm
      | exact ((Commute.refl _).mul_right (hd _).symm).symm
  intro a ha b hb
  have key : ((((⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ : T)) : T ⧸ P') = 1 := by
    have hc := (hcomm ((⟨a, ha⟩ : T) : T ⧸ P') ((⟨b, hb⟩ : T) : T ⧸ P')).eq
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hc]
    group
  have h1 := (hmem _).mp ((QuotientGroup.eq_one_iff _).mp key)
  simpa using h1

end TwoSteps

end S143

end CFSG.Quasithin
