module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

variable {K : Type} [Field K]

theorem eq_of_involution [Finite K] [CharP K 2] {σ σ' : K →+* K}
    (h : ∀ x, σ (σ x) = x) (h' : ∀ x, σ' (σ' x) = x) (hσ : ∃ x, σ x ≠ x)
    (hσ' : ∃ x, σ' x ≠ x) : ∀ x, σ x = σ' x := by
  classical
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcomm : ∀ (τ : K →+* K) (x : ZMod 2), τ (algebraMap (ZMod 2) K x) =
      algebraMap (ZMod 2) K x := fun τ x => by
    have := congrArg (fun φ : ZMod 2 →+* K => φ x)
      (Subsingleton.elim (τ.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
    simpa using this
  let toAlg : (τ : K →+* K) → (∀ x, τ (τ x) = x) → K ≃ₐ[ZMod 2] K := fun τ hτ =>
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective τ ⟨τ.injective, fun y => ⟨τ y, hτ y⟩⟩)
      (hcomm τ)
  have happ : ∀ (τ : K →+* K) (hτ : ∀ x, τ (τ x) = x) (x : K), toAlg τ hτ x = τ x :=
    fun _ _ _ => rfl
  set e := toAlg σ h with he
  set e' := toAlg σ' h' with he'
  have : Fintype (K ≃ₐ[ZMod 2] K) := Fintype.ofFinite _
  have hsq : ∀ (τ : K →+* K) (hτ : ∀ x, τ (τ x) = x), toAlg τ hτ ^ 2 = 1 := fun τ hτ =>
    AlgEquiv.ext fun x => by
      rw [pow_two, AlgEquiv.mul_apply, happ τ hτ, happ τ hτ, hτ, AlgEquiv.one_apply]
  have hne1 : e ≠ 1 := fun h1 => by
    obtain ⟨x, hx⟩ := hσ
    exact hx (by rw [← happ σ h x, ← he, h1]; rfl)
  have hne1' : e' ≠ 1 := fun h1 => by
    obtain ⟨x, hx⟩ := hσ'
    exact hx (by rw [← happ σ' h' x, ← he', h1]; rfl)
  by_contra hne
  push Not at hne
  obtain ⟨x, hx⟩ := hne
  have hee : e ≠ e' := fun h2 => hx (by rw [← happ σ h x, ← happ σ' h' x, ← he, ← he', h2])
  have hcard := IsCyclic.card_pow_eq_one_le (α := K ≃ₐ[ZMod 2] K) (n := 2) (by norm_num)
  have hsub : ({1, e, e'} : Finset (K ≃ₐ[ZMod 2] K)) ⊆
      Finset.univ.filter (fun a : K ≃ₐ[ZMod 2] K => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hsq σ h
    · exact hsq σ' h'
  have h3 : ({1, e, e'} : Finset (K ≃ₐ[ZMod 2] K)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hee]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne1.symm, hne1'.symm⟩
  have := Finset.card_le_card hsub
  omega

variable {G : Type} [Group G]

theorem relIndex_le_two_of_mul_mem {A H : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ A, a ∉ H → b ∉ H → a * b ∈ H) : H.relIndex A ≤ 2 := by
  by_cases hAH : A ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hAH]
    norm_num
  · obtain ⟨a₀, ha₀A, ha₀H⟩ := Set.not_subset.mp hAH
    let φ : Bool → ↥A ⧸ H.subgroupOf A := fun b =>
      bif b then QuotientGroup.mk ⟨a₀, ha₀A⟩ else QuotientGroup.mk 1
    have hφ : Function.Surjective φ := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H a =>
        by_cases haH : (a : G) ∈ H
        · refine ⟨false, QuotientGroup.eq.mpr ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one,
            inv_one, one_mul]
          exact haH
        · refine ⟨true, QuotientGroup.eq.mpr ?_⟩
          rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
          have hinv : a₀⁻¹ ∉ H := fun hi => ha₀H (by simpa using H.inv_mem hi)
          exact h _ (A.inv_mem ha₀A) _ a.2 hinv haH
    have := Nat.card_le_card_of_surjective φ hφ
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    rw [Subgroup.relIndex, Subgroup.index]
    exact this

theorem card_le_half {R : Type} [AddGroup R] [Finite R] {S : AddSubgroup R} (hS : S ≠ ⊤) :
    2 * Nat.card S ≤ Nat.card R := by
  have h1 := AddSubgroup.card_mul_index S
  have h2 : S.index ≠ 1 := fun h => hS (AddSubgroup.index_eq_one.mp h)
  have h3 : S.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have h4 : 2 ≤ S.index := by omega
  rw [← h1]
  calc 2 * Nat.card S ≤ S.index * Nat.card S := Nat.mul_le_mul_right _ h4
    _ = Nat.card S * S.index := mul_comm _ _

end CFSG.Quasithin.Vol2.Ch11.SecO1b
