module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.SpecialLinear Matrix

section Vec

variable {F : Type} [Field F]

theorem vec_end_of_swap_fixed {n : ℕ} (hn : 2 ≤ n) {i j : Fin n} (hi : i.val = 0)
    (hj : j.val + 1 = n) (τ : Fˣ) (v : Fin (n + 1) → Fˣ)
    (h1 : GGVecEq (diagAt i τ) (v ∘ Fin.castSucc))
    (h2 : GGVecEq v (v ∘ (Equiv.swap j.castSucc j.succ).symm)) :
    GGVecEq v (diagAt i.castSucc τ) := by
  obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp h1
  obtain ⟨c', hc'⟩ := ggVecEq_iff_exists.mp h2
  simp only [Function.comp_apply] at hc hc'
  have hji : j ≠ i := by
    intro h
    have hv : j.val = i.val := congrArg Fin.val h
    omega
  have hne1 : i.castSucc ≠ j.castSucc := by
    intro h
    have hv : (i.castSucc : Fin (n + 1)).val = (j.castSucc).val := congrArg Fin.val h
    simp only [Fin.val_castSucc] at hv
    omega
  have hne2 : i.castSucc ≠ j.succ := by
    intro h
    have hv : (i.castSucc : Fin (n + 1)).val = (j.succ).val := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hne3 : j.succ ≠ i.castSucc := by
    intro h
    have hv : (j.succ).val = (i.castSucc : Fin (n + 1)).val := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hfix : (Equiv.swap j.castSucc j.succ).symm (i.castSucc) = i.castSucc := by
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
  have hc'1 : c' = 1 := by
    have h := hc' (i.castSucc)
    rw [hfix] at h
    have h2' : (1 : Fˣ) = c' := by
      have := congrArg (fun x : Fˣ => x * (v (i.castSucc))⁻¹) h
      simpa using this
    exact h2'.symm
  have hcinv : ∀ k : Fin (n + 1), v k = v ((Equiv.swap j.castSucc j.succ).symm k) := by
    intro k
    have h := hc' k
    rw [hc'1, one_mul] at h
    exact h
  have hv_castSucc (k : Fin n) : v (Fin.castSucc k) = c⁻¹ * diagAt i τ k := by
    rw [hc k, inv_mul_cancel_left]
  have hlast : Fin.last n = j.succ := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_succ]
    omega
  have hswap : (Equiv.swap j.castSucc j.succ).symm (j.succ) = j.castSucc := by
    rw [Equiv.symm_swap, Equiv.swap_apply_right]
  refine ggVecEq_iff_exists.mpr ⟨c⁻¹, fun k => ?_⟩
  induction k using Fin.lastCases with
  | last =>
    rw [hlast, hcinv (j.succ), hswap, hv_castSucc j, diagAt_apply_of_ne hji τ,
      diagAt_apply_of_ne hne3 τ, mul_one]
  | cast k' =>
    rw [hv_castSucc k']
    have hd : diagAt i.castSucc τ (Fin.castSucc k') = diagAt i τ k' :=
      congrFun (diagAt_castSucc_comp_castSucc (n := n) i τ) k'
    rw [hd]

theorem vec_start_of_swap_fixed {n : ℕ} (hn : 2 ≤ n) {i j : Fin n} (hi : i.val = 0)
    (hj : j.val + 1 = n) (τ : Fˣ) (m : Fin (n + 1) → Fˣ)
    (h1 : GGVecEq (m ∘ Fin.succ) (diagAt j τ))
    (h2 : GGVecEq m (m ∘ (Equiv.swap i.castSucc i.succ).symm)) :
    GGVecEq m (diagAt (Fin.last n) τ) := by
  obtain ⟨c, hc⟩ := ggVecEq_iff_exists.mp h1
  obtain ⟨c', hc'⟩ := ggVecEq_iff_exists.mp h2
  simp only [Function.comp_apply] at hc hc'
  have hij : i ≠ j := by
    intro h
    have hv : i.val = j.val := congrArg Fin.val h
    omega
  have hne1 : Fin.last n ≠ i.castSucc := by
    intro h
    have hv : (Fin.last n).val = (i.castSucc : Fin (n + 1)).val := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  have hne2 : Fin.last n ≠ i.succ := by
    intro h
    have hv : (Fin.last n).val = (i.succ).val := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_succ] at hv
    omega
  have hfix : (Equiv.swap i.castSucc i.succ).symm (Fin.last n) = Fin.last n := by
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
  have hc'1 : c' = 1 := by
    have h := hc' (Fin.last n)
    rw [hfix] at h
    have h2' : (1 : Fˣ) = c' := by
      have := congrArg (fun x : Fˣ => x * (m (Fin.last n))⁻¹) h
      simpa using this
    exact h2'.symm
  have hcinv : ∀ k : Fin (n + 1), m k = m ((Equiv.swap i.castSucc i.succ).symm k) := by
    intro k
    have h := hc' k
    rw [hc'1, one_mul] at h
    exact h
  have hswap : (Equiv.swap i.castSucc i.succ).symm (i.castSucc) = i.succ := by
    rw [Equiv.symm_swap, Equiv.swap_apply_left]
  have hi0 : i.castSucc = (0 : Fin (n + 1)) := by
    apply Fin.ext
    simp [hi]
  have hm0 : m 0 = c := by
    have h := hcinv (i.castSucc)
    rw [hswap] at h
    rw [hi0] at h
    rw [h, hc i, diagAt_apply_of_ne hij τ, mul_one]
  have hjs : j.succ = Fin.last n := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have hd (k' : Fin n) : diagAt (Fin.last n) τ (Fin.succ k') = diagAt j τ k' := by
    have h := congrFun (diagAt_succ_comp_succ (n := n) j τ) k'
    rw [hjs] at h
    exact h
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hv : ((0 : Fin (n + 1))).val = (Fin.last n).val := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega
  refine ggVecEq_iff_exists.mpr ⟨c, fun k => ?_⟩
  induction k using Fin.cases with
  | zero => rw [hm0, diagAt_apply_of_ne h0l τ, mul_one]
  | succ k' => rw [hc k', hd k']

theorem exists_zpow_eq_of_pow_eq_one [Finite F] {p : ℕ} [Fact p.Prime] {τ τ' : Fˣ}
    (hτ : τ ^ p = 1) (hτ' : τ' ^ p = 1) (h1 : τ' ≠ 1) : ∃ k : ℤ, τ = τ' ^ k := by
  classical
  haveI : Fintype Fˣ := Fintype.ofFinite Fˣ
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsub : (Subgroup.zpowers τ' : Set Fˣ) ⊆ {a : Fˣ | a ^ p = 1} := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    show (τ' ^ k) ^ p = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hτ']
    simp
  have hcardT : Fintype.card (↥(Subgroup.zpowers τ' : Set Fˣ)) = p := by
    have h : Nat.card (Subgroup.zpowers τ') = p := by
      rw [Nat.card_zpowers, orderOf_eq_prime hτ' h1]
    rwa [Nat.card_eq_fintype_card] at h
  have hcardS : Fintype.card (↥({a : Fˣ | a ^ p = 1} : Set Fˣ)) ≤ p := by
    have h : Fintype.card {a : Fˣ // a ^ p = 1} ≤ p := by
      rw [Fintype.card_subtype]
      exact IsCyclic.card_pow_eq_one_le (α := Fˣ) hp
    exact h
  have hset : ({a : Fˣ | a ^ p = 1} : Set Fˣ) = (Subgroup.zpowers τ' : Set Fˣ) :=
    (Set.eq_of_subset_of_card_le hsub (by rw [hcardT]; exact hcardS)).symm
  have hmemS : τ ∈ ({a : Fˣ | a ^ p = 1} : Set Fˣ) := hτ
  have hmem : τ ∈ Subgroup.zpowers τ' := by
    change τ ∈ (Subgroup.zpowers τ' : Set Fˣ)
    rw [← hset]
    exact hmemS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact ⟨k, hk.symm⟩

end Vec

section ActsVec

variable {X : Type*} [Group X] {F : Type} [Field F] {m : ℕ}

theorem pow_eq_one_of_actsVec_diagAt {φ : SpecialLinearGroup (Fin m) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin m) F)) (hm : 2 ≤ m) {g : X} {p : ℕ}
    (hg : g ^ p = 1) {k : Fin m} {τ : Fˣ} (a : GGActsVec φ g (diagAt k τ)) : τ ^ p = 1 := by
  have hpow : GGActsVec φ (1 : X) (diagAt k (τ ^ p)) := by
    have h := GGActsVec.zpow a (p : ℤ)
    rw [diagAt_zpow, zpow_natCast, hg] at h
    exact h
  have hone : GGActsVec φ (1 : X) (1 : Fin m → Fˣ) :=
    GGActsVec.one_of_commute (fun s => by simp)
  exact (ggVecEq_diagAt_one_iff hm k (τ ^ p)).mp (GGActsVec.vecEq hker hpow hone)

end ActsVec

end CFSG.StandardType
