module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin.H13.L827X.LBOrbit

theorem card_le_of_mem_orbit_subset {Γ Ω : Type*} [Group Γ] [MulAction Γ Ω] [Finite Ω]
    (S : Set Ω) (hS : ∀ γ : Γ, ∀ ω ∈ S, γ • ω ∈ S) {ω : Ω} (hω : ω ∈ S) :
    (MulAction.orbit Γ ω).ncard ≤ S.ncard := by
  refine Set.ncard_le_ncard ?_
  intro x hx
  obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact hS γ ω hω

private theorem ncard_eq_sum_ite_mem_orbit {Ω : Type*} [Fintype Ω] (s : Set Ω)
    [DecidablePred (· ∈ s)] :
    s.ncard = ∑ x : Ω, if x ∈ s then 1 else 0 := by
  calc s.ncard = (↑(Finset.univ.filter (· ∈ s)) : Set Ω).ncard := by
        congr 1
        ext x
        simp
    _ = (Finset.univ.filter (· ∈ s)).card := Set.ncard_coe_finset _
    _ = ∑ x : Ω, if x ∈ s then 1 else 0 := Finset.card_filter _ _

private theorem card_filter_mul_orbit_ncard {Γ Ω : Type*} [Group Γ] [Fintype Γ]
    [MulAction Γ Ω] [Fintype Ω] [DecidableEq Ω] (ℓ : Set Ω) [DecidablePred (· ∈ ℓ)] (ω : Ω) :
    (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card * (MulAction.orbit Γ ω).ncard
      = Fintype.card Γ * (MulAction.orbit Γ ω ∩ ℓ).ncard := by
  classical
  obtain ⟨k, hk⟩ : ∃ k : Ω → ℕ, ∀ x, k x = (Finset.univ.filter (fun γ : Γ => γ • ω = x)).card :=
    ⟨fun x => (Finset.univ.filter (fun γ : Γ => γ • ω = x)).card, fun x => rfl⟩
  have hfw : ∀ f : Γ → ℕ, ∑ γ : Γ, f γ
      = ∑ x : Ω, ∑ γ ∈ Finset.univ.filter (fun γ : Γ => γ • ω = x), f γ :=
    fun f => (Finset.sum_fiberwise Finset.univ (fun γ : Γ => γ • ω) f).symm
  have hfib : ∀ x : Ω, k x = if x ∈ MulAction.orbit Γ ω then k ω else 0 := by
    intro x
    by_cases hx : x ∈ MulAction.orbit Γ ω
    · rw [if_pos hx]
      obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
      rw [hk, hk]
      apply Finset.card_nbij' (fun γ : Γ => g⁻¹ * γ) (fun δ : Γ => g * δ)
      · intro γ hγ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hγ ⊢
        rw [mul_smul, hγ, inv_smul_smul]
      · intro δ hδ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hδ ⊢
        rw [mul_smul, hδ]
      · intro γ _
        simp
      · intro δ _
        simp
    · rw [if_neg hx, hk, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro γ _ hγ
      apply hx
      rw [← hγ]
      exact MulAction.mem_orbit ω γ
  have hsum : Fintype.card Γ = ∑ x : Ω, k x := by
    have h := hfw (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
    rw [h]
    exact Finset.sum_congr rfl fun x _ => (hk x).symm
  have hN : (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card
      = ∑ x : Ω, if x ∈ ℓ then k x else 0 := by
    rw [Finset.card_filter, hfw]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hk]
    split_ifs with hx
    · rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [Finset.mem_filter] at hγ
      have hmem : γ • ω ∈ ℓ := by rw [hγ.2]; exact hx
      rw [if_pos hmem]
    · apply Finset.sum_eq_zero
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hmem : γ • ω ∉ ℓ := by rw [hγ.2]; exact hx
      rw [if_neg hmem]
  have hOcard : (MulAction.orbit Γ ω).ncard
      = ∑ x : Ω, if x ∈ MulAction.orbit Γ ω then 1 else 0 :=
    ncard_eq_sum_ite_mem_orbit _
  have hOℓcard : (MulAction.orbit Γ ω ∩ ℓ).ncard
      = ∑ x : Ω, if x ∈ MulAction.orbit Γ ω ∩ ℓ then 1 else 0 :=
    ncard_eq_sum_ite_mem_orbit _
  have hA : (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card
      = k ω * (MulAction.orbit Γ ω ∩ ℓ).ncard := by
    rw [hN, hOℓcard, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hfib x]
    by_cases hxℓ : x ∈ ℓ <;> by_cases hxO : x ∈ MulAction.orbit Γ ω <;> simp [hxℓ, hxO]
  have hB : Fintype.card Γ = k ω * (MulAction.orbit Γ ω).ncard := by
    rw [hsum, hOcard, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hfib x]
    split_ifs <;> simp
  calc (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card * (MulAction.orbit Γ ω).ncard
      = (k ω * (MulAction.orbit Γ ω ∩ ℓ).ncard) * (MulAction.orbit Γ ω).ncard := by rw [hA]
    _ = (MulAction.orbit Γ ω ∩ ℓ).ncard * (k ω * (MulAction.orbit Γ ω).ncard) := by ring
    _ = (MulAction.orbit Γ ω ∩ ℓ).ncard * Fintype.card Γ := by rw [hB]
    _ = Fintype.card Γ * (MulAction.orbit Γ ω ∩ ℓ).ncard := by ring

theorem orbit_weight_third {Γ Ω : Type*} [Group Γ] [Finite Γ] [MulAction Γ Ω] [Fintype Ω]
    [DecidableEq Ω] (S : Finset Ω) (hS : ∀ γ : Γ, ∀ ω ∈ S, γ • ω ∈ S) (c : Ω → ℕ)
    (hc : ∀ γ : Γ, ∀ ω, c (γ • ω) = c ω) (ℓ : Set Ω) [DecidablePred (· ∈ ℓ)]
    (hO3 : ∀ ω ∈ S, 3 * (MulAction.orbit Γ ω ∩ ℓ).ncard ≤ (MulAction.orbit Γ ω).ncard) :
    3 * ∑ ω ∈ S.filter (· ∈ ℓ), c ω ≤ ∑ ω ∈ S, c ω := by
  classical
  haveI : Fintype Γ := Fintype.ofFinite Γ
  have hGpos : 0 < Fintype.card Γ := Fintype.card_pos
  have hreindex : ∀ γ : Γ, ∑ ω ∈ S, (if γ • ω ∈ ℓ then c ω else 0)
      = ∑ ω ∈ S, (if ω ∈ ℓ then c ω else 0) := by
    intro γ
    apply Finset.sum_nbij' (fun ω => γ • ω) (fun ω => γ⁻¹ • ω)
    · intro ω hω
      exact hS γ ω hω
    · intro ω hω
      exact hS γ⁻¹ ω hω
    · intro ω _
      exact inv_smul_smul γ ω
    · intro ω _
      exact smul_inv_smul γ ω
    · intro ω _
      simp only [hc γ ω]
  have hT1 : ∑ γ : Γ, ∑ ω ∈ S, (if γ • ω ∈ ℓ then c ω else 0)
      = Fintype.card Γ * ∑ ω ∈ S.filter (· ∈ ℓ), c ω := by
    rw [Finset.sum_congr rfl fun γ _ => hreindex γ, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Finset.sum_filter]
  have hT2 : ∑ γ : Γ, ∑ ω ∈ S, (if γ • ω ∈ ℓ then c ω else 0)
      = ∑ ω ∈ S, c ω * (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.card_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    split_ifs <;> simp
  have hbound : ∀ ω ∈ S, 3 * (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card
      ≤ Fintype.card Γ := by
    intro ω hω
    have hkey := card_filter_mul_orbit_ncard (Γ := Γ) ℓ ω
    have hO := hO3 ω hω
    have hpos : 0 < (MulAction.orbit Γ ω).ncard :=
      (Set.ncard_pos (Set.toFinite (MulAction.orbit Γ ω))).mpr ⟨ω, MulAction.mem_orbit_self ω⟩
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 3 * (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card * (MulAction.orbit Γ ω).ncard
        = 3 * ((Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card
            * (MulAction.orbit Γ ω).ncard) := by ring
      _ = 3 * (Fintype.card Γ * (MulAction.orbit Γ ω ∩ ℓ).ncard) := by rw [hkey]
      _ = Fintype.card Γ * (3 * (MulAction.orbit Γ ω ∩ ℓ).ncard) := by ring
      _ ≤ Fintype.card Γ * (MulAction.orbit Γ ω).ncard := Nat.mul_le_mul_left _ hO
  have hmain : Fintype.card Γ * ∑ ω ∈ S.filter (· ∈ ℓ), c ω
      = ∑ ω ∈ S, c ω * (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card :=
    hT1.symm.trans hT2
  have hfinal : Fintype.card Γ * (3 * ∑ ω ∈ S.filter (· ∈ ℓ), c ω)
      ≤ Fintype.card Γ * ∑ ω ∈ S, c ω := by
    calc Fintype.card Γ * (3 * ∑ ω ∈ S.filter (· ∈ ℓ), c ω)
        = 3 * (Fintype.card Γ * ∑ ω ∈ S.filter (· ∈ ℓ), c ω) := by ring
      _ = ∑ ω ∈ S, c ω * (3 * (Finset.univ.filter (fun γ : Γ => γ • ω ∈ ℓ)).card) := by
          rw [hmain, Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ ω ∈ S, c ω * Fintype.card Γ :=
          Finset.sum_le_sum fun ω hω => Nat.mul_le_mul_left _ (hbound ω hω)
      _ = Fintype.card Γ * ∑ ω ∈ S, c ω := by
          rw [← Finset.sum_mul, mul_comm]
  exact Nat.le_of_mul_le_mul_left hfinal hGpos

end CFSG.Quasithin.H13.L827X.LBOrbit
