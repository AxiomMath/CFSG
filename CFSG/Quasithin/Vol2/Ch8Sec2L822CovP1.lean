module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13

open Subgroup

instance alternatingGroup_five_simple_cv : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup (by simp)

theorem commute_of_perfect_normalizes_three_cv {X G : Type} [Group X] [Group G]
    (hperf : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (χ : X →* G) (g : G) (hg3 : g ^ 3 = 1)
    (hnorm : ∀ x : X, χ x * g * (χ x)⁻¹ ∈ Subgroup.zpowers g) : ∀ x : X, χ x * g = g * χ x := by
  classical
  by_cases hg1 : g = 1
  · intro x
    rw [hg1, mul_one, one_mul]
  have hord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hdich : ∀ x : X, χ x * g * (χ x)⁻¹ = g ∨ χ x * g * (χ x)⁻¹ = g⁻¹ := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hnorm x)
    have hmod : g ^ (k % 3) = χ x * g * (χ x)⁻¹ := by
      have h := zpow_mod_orderOf g k
      rw [hord] at h
      rw [← hk]
      exact_mod_cast h
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      rw [h0, zpow_zero] at hmod
      apply hg1
      have h' := congrArg (fun t => (χ x)⁻¹ * t * χ x) hmod
      simp [mul_assoc] at h'
      exact h'.symm
    · left
      rw [h1, zpow_one] at hmod
      exact hmod.symm
    · right
      rw [h2] at hmod
      have hsq : g ^ (2 : ℤ) * g = 1 := by
        simp only [zpow_ofNat]
        rw [← pow_succ]
        exact hg3
      have hinv : g ^ (2 : ℤ) = g⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [← hmod, hinv]
  have hg2 : g⁻¹ ≠ g := by
    intro h
    apply hg1
    have h2 : g * g = 1 := by
      have h' : g * g⁻¹ = 1 := mul_inv_cancel g
      rw [h] at h'
      exact h'
    have h3 : g ^ 3 = g * g * g := by simp [pow_succ, mul_assoc]
    calc g = (g * g * g) * (g * g)⁻¹ := by group
      _ = 1 := by
        rw [← h3, hg3, h2, inv_one, mul_one]
  let ε : X →* ℤˣ := MonoidHom.mk'
    (fun x : X => if χ x * g * (χ x)⁻¹ = g then (1 : ℤˣ) else -1) (by
      intro a b
      have hab : χ (a * b) * g * (χ (a * b))⁻¹ = χ a * (χ b * g * (χ b)⁻¹) * (χ a)⁻¹ := by
        rw [map_mul]
        group
      rcases hdich b with hR | hR
      · simp only [hab, hR]
        simp
      · simp only [hab, hR, if_neg hg2]
        have hinvconj : χ a * g⁻¹ * (χ a)⁻¹ = (χ a * g * (χ a)⁻¹)⁻¹ := by group
        rw [hinvconj]
        rcases hdich a with hP | hP
        · rw [hP, if_neg hg2]
          simp [hP]
        · rw [hP, inv_inv]
          simp [hg2])
  intro x
  have h1 : ε x = 1 := by
    have hle : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ ≤ ε.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    have hx : x ∈ ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ := by
      rw [hperf]
      exact mem_top x
    exact MonoidHom.mem_ker.1 (hle hx)
  change (if χ x * g * (χ x)⁻¹ = g then (1 : ℤˣ) else -1) = 1 at h1
  have hconj : χ x * g * (χ x)⁻¹ = g := by
    by_contra hne
    rw [if_neg hne] at h1
    exact absurd h1 (by decide)
  calc χ x * g = χ x * g * (χ x)⁻¹ * χ x := by group
    _ = g * χ x := by rw [hconj]

theorem false_of_centrality_trap_cv {D : Type} [Group D] (K : Subgroup D)
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (φ : K →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (y : D) (hyK : y ∈ K) (hy3 : y ^ 3 = 1) (hφy : φ ⟨y, hyK⟩ ≠ 1)
    {Q : Type} [Group Q] (ρ : D →* Q)
    (hker : ∀ d ∈ ρ.ker, ∃ n : ℕ, d ^ (2 ^ n) = 1)
    (hnorm : ∀ d ∈ K, ρ d * ρ y * (ρ d)⁻¹ ∈ Subgroup.zpowers (ρ y)) : False := by
  classical
  let ρK : K →* Q := ρ.comp K.subtype
  have hg3 : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have hcomm : ∀ x : K, ρK x * ρ y = ρ y * ρK x :=
    fun x => commute_of_perfect_normalizes_three_cv hperf ρK (ρ y) hg3 (fun x => hnorm x x.2) x
  set N₀ : Subgroup (alternatingGroup (Fin 5)) := ρK.ker.map φ with hN₀
  haveI hN₀n : N₀.Normal := Subgroup.Normal.map inferInstance φ hφ
  have hN₀2 : ∀ a ∈ N₀, ∃ n : ℕ, a ^ (2 ^ n) = 1 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 ha
    have hxk : (x : D) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact (MonoidHom.mem_ker.1 hx : ρK x = 1)
    obtain ⟨n, hn⟩ := hker x.1 hxk
    refine ⟨n, ?_⟩
    have hx2 : x ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hn)
    rw [← map_pow, hx2, map_one]
  let a3 : alternatingGroup (Fin 5) :=
    ⟨List.formPerm [0, 1, 2], Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
  have ha3 : a3 ^ 3 = 1 := Subtype.ext (by decide)
  have ha3ne : a3 ≠ 1 := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hN₀bot : N₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N₀ with h | h
    · exact h
    · exfalso
      have ha : a3 ∈ N₀ := by
        rw [h]
        exact mem_top _
      obtain ⟨n, hn⟩ := hN₀2 a3 ha
      have hcop : Nat.gcd 3 (2 ^ n) = 1 :=
        Nat.Coprime.pow_right n (by norm_num)
      have h1 : a3 ^ (Nat.gcd 3 (2 ^ n)) = 1 := pow_gcd_eq_one.2 ⟨ha3, hn⟩
      rw [hcop, pow_one] at h1
      exact ha3ne h1
  have hcommφ : ∀ x : K, φ x * φ ⟨y, hyK⟩ = φ ⟨y, hyK⟩ * φ x := by
    intro x
    have hc : (x : D) * y * (x : D)⁻¹ * y⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem (K.mul_mem x.2 hyK) (K.inv_mem x.2)) (K.inv_mem hyK)
    have hcker : (⟨(x : D) * y * (x : D)⁻¹ * y⁻¹, hc⟩ : K) ∈ ρK.ker := by
      rw [MonoidHom.mem_ker]
      have h := hcomm x
      change ρ x * ρ y = ρ y * ρ x at h
      change ρ ((x : D) * y * (x : D)⁻¹ * y⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ = ρ y * ρ x * (ρ x)⁻¹ * (ρ y)⁻¹ := by rw [h]
        _ = 1 := by group
    have hφc : φ ⟨(x : D) * y * (x : D)⁻¹ * y⁻¹, hc⟩ ∈ N₀ := Subgroup.mem_map_of_mem φ hcker
    rw [hN₀bot, Subgroup.mem_bot] at hφc
    have hsplit : (⟨(x : D) * y * (x : D)⁻¹ * y⁻¹, hc⟩ : K) =
        x * ⟨y, hyK⟩ * x⁻¹ * ⟨y, hyK⟩⁻¹ := by
      apply Subtype.ext
      simp
    rw [hsplit, map_mul, map_mul, map_mul, map_inv, map_inv] at hφc
    calc φ x * φ ⟨y, hyK⟩ = (φ x * φ ⟨y, hyK⟩ * (φ x)⁻¹ * (φ ⟨y, hyK⟩)⁻¹) * (φ ⟨y, hyK⟩ * φ x) := by
          group
      _ = φ ⟨y, hyK⟩ * φ x := by rw [hφc, one_mul]
  have hcen : φ ⟨y, hyK⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨x, rfl⟩ := hφ b
    exact hcommφ x
  have hZ : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 5))) with h | h
    · exact h
    · exfalso
      let b3 : alternatingGroup (Fin 5) :=
        ⟨List.formPerm [0, 1, 3], Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩
      have ha : a3 ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
        rw [h]
        exact mem_top _
      have hcomm' := (Subgroup.mem_center_iff.1 ha) b3
      have hne : (a3 : Equiv.Perm (Fin 5)) * b3 ≠ b3 * a3 := by
        revert hcomm'
        decide
      exact hne (congrArg Subtype.val hcomm').symm
  have hφy1 : φ ⟨y, hyK⟩ = 1 := by
    have hmem : φ ⟨y, hyK⟩ ∈ (⊥ : Subgroup (alternatingGroup (Fin 5))) := by
      rw [← hZ]
      exact hcen
    exact Subgroup.mem_bot.1 hmem
  exact hφy hφy1

end CFSG.Quasithin.H13
