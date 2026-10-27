module

public import Mathlib.GroupTheory.OrderOfElement
public import CFSG.Quasithin.EmptyFaithful.S146zHRank
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.Quasithin

section Alg

theorem comm_moves_diag {V : Type*} [CommGroup V] (σ β : MulAut V) (W₁ W₂ : Subgroup V)
    (hinf : W₁ ⊓ W₂ = ⊥) (hσσ : ∀ v, σ (σ v) = v)
    (hσ₁ : ∀ w ∈ W₁, σ w ∈ W₂)
    (hβ₂ : ∀ w ∈ W₂, β w = w) (hβ₁ : ∀ w ∈ W₁, β w ∈ W₁)
    (hβ₁' : ∀ w ∈ W₁, β⁻¹ w ∈ W₁)
    {w : V} (hw : w ∈ W₁) (hβw : β w ≠ w) :
    (σ * β * σ⁻¹ * β⁻¹) (w * σ w) ≠ w * σ w := by
  intro h
  have hσinv : ∀ v, σ⁻¹ v = σ v := by
    intro v
    have : σ (σ v) = v := hσσ v
    exact (MulEquiv.symm_apply_eq σ).mpr this.symm
  have hβinv₂ : ∀ v ∈ W₂, β⁻¹ v = v := by
    intro v hv
    have := hβ₂ v hv
    exact (MulEquiv.symm_apply_eq β).mpr this.symm
  simp only [MulAut.mul_apply, hσinv] at h
  have h1 : β⁻¹ (w * σ w) = β⁻¹ w * σ w := by
    rw [map_mul, hβinv₂ _ (hσ₁ w hw)]
  rw [h1] at h
  have h2 : σ (β⁻¹ w * σ w) = σ (β⁻¹ w) * w := by
    rw [map_mul, hσσ]
  rw [h2] at h
  have hσβ : σ (β⁻¹ w) ∈ W₂ := hσ₁ _ (hβ₁' w hw)
  have h3 : β (σ (β⁻¹ w) * w) = σ (β⁻¹ w) * β w := by
    rw [map_mul, hβ₂ _ hσβ]
  rw [h3] at h
  have h4 : σ (σ (β⁻¹ w) * β w) = β⁻¹ w * σ (β w) := by
    rw [map_mul, hσσ]
  rw [h4] at h
  have hAB : β⁻¹ w * w⁻¹ = σ w * (σ (β w))⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    rw [h, mul_comm]
  have hm₁ : β⁻¹ w * w⁻¹ ∈ W₁ := W₁.mul_mem (hβ₁' w hw) (W₁.inv_mem hw)
  have hm₂ : σ w * (σ (β w))⁻¹ ∈ W₂ :=
    W₂.mul_mem (hσ₁ w hw) (W₂.inv_mem (hσ₁ _ (hβ₁ w hw)))
  have hmem : β⁻¹ w * w⁻¹ ∈ W₁ ⊓ W₂ := ⟨hm₁, hAB ▸ hm₂⟩
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at hmem
  apply hβw
  have h6 := congrArg β hmem
  have h7 : w = β w := by simpa using h6
  exact h7.symm

theorem exists_iterate_eq_of_card_four {V : Type*} [CommGroup V] [Finite V] (α : MulAut V)
    (W : Subgroup V) (hW : Nat.card W = 4) (hαW : ∀ w ∈ W, α w ∈ W)
    (hfix : ∀ w ∈ W, α w = w → w = 1) (hpow : ∀ w ∈ W, (⇑α)^[3] w = w) {w w' : V}
    (hw : w ∈ W) (hw1 : w ≠ 1) (hw' : w' ∈ W) (hw'1 : w' ≠ 1) :
    ∃ n : ℕ, (⇑α)^[n] w = w' := by
  classical
  have hper : Function.IsPeriodicPt (⇑α) 3 w := hpow w hw
  have hdvd := hper.minimalPeriod_dvd
  have hne1 : Function.minimalPeriod (⇑α) w ≠ 1 := by
    intro h1
    exact hw1 (hfix w hw (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1))
  have hmp : Function.minimalPeriod (⇑α) w = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne1
  have hinjOn := (Function.iterate_injOn_Iio_minimalPeriod (f := ⇑α) (x := w))
  rw [hmp] at hinjOn
  have hiter : ∀ n : ℕ, (⇑α)^[n] w ∈ W := by
    intro n
    induction n with
    | zero => exact hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hαW _ ih
  have hiter1 : ∀ n : ℕ, (⇑α)^[n] w ≠ 1 := by
    intro n hn
    rw [iterate_eq_pow_mulAut] at hn
    exact hw1 ((map_eq_one_iff (α ^ n) (α ^ n).injective).mp hn)
  let F : Fin 3 → {x : W // x ≠ 1} := fun i =>
    ⟨⟨(⇑α)^[i.val] w, hiter i.val⟩, fun h => hiter1 i.val (congrArg Subtype.val h)⟩
  have hinj : Function.Injective F := by
    intro i j h
    have h' : (⇑α)^[i.val] w = (⇑α)^[j.val] w :=
      congrArg (fun x : {x : W // x ≠ 1} => (x.1 : V)) h
    exact Fin.ext (hinjOn (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) h')
  have : Fintype W := Fintype.ofFinite W
  have hcardX : Fintype.card {x : W // x ≠ 1} = 3 := by
    have h1 := Fintype.card_subtype_compl (fun x : W => x = 1)
    have h2 : Fintype.card {x : W // x = 1} = 1 := by
      rw [Fintype.card_subtype_eq]
    have h3 : Fintype.card W = 4 := by rw [← Nat.card_eq_fintype_card]; exact hW
    simp only [ne_eq] at h1 ⊢
    rw [h1, h2, h3]
  have hbij : Function.Bijective F :=
    (Fintype.bijective_iff_injective_and_card F).mpr ⟨hinj, by rw [hcardX]; simp⟩
  obtain ⟨i, hi⟩ := hbij.2 ⟨⟨w', hw'⟩, fun h => hw'1 (congrArg Subtype.val h)⟩
  exact ⟨i.val, congrArg (fun x : {x : W // x ≠ 1} => (x.1 : V)) hi⟩

theorem exists_fixed_of_involution {V : Type*} [CommGroup V] (β : MulAut V) (W : Subgroup V)
    (hββ : ∀ v, β (β v) = v) (hex : ∀ v ∈ W, β v ∈ W) (hexp : ∀ v : V, v * v = 1)
    (hmv : ∃ u ∈ W, β u ≠ u) : ∃ w ∈ W, w ≠ 1 ∧ β w = w := by
  obtain ⟨u, hu, hβu⟩ := hmv
  refine ⟨β u * u⁻¹, W.mul_mem (hex u hu) (W.inv_mem hu), ?_, ?_⟩
  · intro h
    exact hβu (mul_inv_eq_one.mp h)
  · rw [map_mul, map_inv, hββ]
    have h1 : (β u * u⁻¹)⁻¹ = β u * u⁻¹ := inv_eq_of_mul_eq_one_right (hexp _)
    calc u * (β u)⁻¹ = (β u * u⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv, mul_comm]
      _ = β u * u⁻¹ := h1

theorem card_le_index_of_inf_eq_bot {V : Type*} [Group V] [Finite V] (W D : Subgroup V)
    (h : W ⊓ D = ⊥) : Nat.card W ≤ D.index := by
  have hinj : Function.Injective (fun w : W => (QuotientGroup.mk (w : V) : V ⧸ D)) := by
    intro w w' hww
    have h1 : (w : V)⁻¹ * (w' : V) ∈ D := QuotientGroup.eq.mp hww
    have h2 : (w : V)⁻¹ * (w' : V) ∈ W := W.mul_mem (W.inv_mem w.2) w'.2
    have h3 : (w : V)⁻¹ * (w' : V) ∈ W ⊓ D := ⟨h2, h1⟩
    rw [h, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  exact Nat.card_le_card_of_injective _ hinj

theorem index_le_two_of_forall {Γ : Type*} [Group Γ] [Finite Γ] (D : Subgroup Γ) (y : Γ)
    (h : ∀ z : Γ, z ∈ D ∨ y⁻¹ * z ∈ D) : D.index ≤ 2 := by
  classical
  let F : Bool → Γ ⧸ D := fun b => if b then (QuotientGroup.mk y) else (QuotientGroup.mk 1)
  have hsurj : Function.Surjective F := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rcases h z with hz | hz
    · exact ⟨false, by simp only [F]; exact (QuotientGroup.eq.mpr (by simpa using hz)).symm⟩
    · exact ⟨true, by simp only [F]; exact QuotientGroup.eq.mpr hz⟩
  calc D.index = Nat.card (Γ ⧸ D) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_surjective F hsurj
    _ = 2 := by simp

theorem padicValNat_two_le_one {n : ℕ} (h0 : 0 < n) (h2 : n ≤ 2) : padicValNat 2 n ≤ 1 := by
  interval_cases n <;> simp

theorem eq_one_or_eq_of_card_subgroup_two {G : Type*} [Group G] (K : Subgroup G) (hK : Nat.card K = 2) {x : G}
    (hx : x ∈ K) (hx1 : x ≠ 1) {x' : G} (hx' : x' ∈ K) : x' = 1 ∨ x' = x := by
  obtain ⟨c, hc1, hcu⟩ := (Nat.card_eq_two_iff' (1 : ↥K)).mp hK
  by_cases h1 : x' = 1
  · exact Or.inl h1
  · right
    have h2 : (⟨x', hx'⟩ : ↥K) = c := hcu _ (fun e => h1 (congrArg Subtype.val e))
    have h3 : (⟨x, hx⟩ : ↥K) = c := hcu _ (fun e => hx1 (congrArg Subtype.val e))
    exact congrArg Subtype.val (h2.trans h3.symm)

theorem mul_self_eq_one_of_card_two {G : Type*} [Group G] (K : Subgroup G) (hK : Nat.card K = 2)
    {x : G} (hx : x ∈ K) : x * x = 1 := by
  have h1 : (⟨x, hx⟩ : ↥K) ^ Nat.card K = 1 := pow_card_eq_one'
  rw [hK] at h1
  have h2 := congrArg Subtype.val h1
  simpa [pow_two] using h2

end Alg

end CFSG.Quasithin
