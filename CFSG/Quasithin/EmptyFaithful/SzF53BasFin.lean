module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.F53

section F5c

open Equiv

theorem perm_center_trivial5 : ∀ σ : Perm (Fin 5), (∀ τ : Perm (Fin 5), τ * σ = σ * τ) → σ = 1 := by
  decide +kernel

theorem perm_center_trivial3 : ∀ σ : Perm (Fin 3), (∀ τ : Perm (Fin 3), τ * σ = σ * τ) → σ = 1 := by
  decide +kernel

theorem normal_ge_alt_of_simple {n : ℕ} [IsSimpleGroup (alternatingGroup (Fin n))]
    (hc : ∀ σ : Perm (Fin n), (∀ τ : Perm (Fin n), τ * σ = σ * τ) → σ = 1)
    (N : Subgroup (Perm (Fin n))) [hNn : N.Normal] (hN : N ≠ ⊥) :
    alternatingGroup (Fin n) ≤ N := by
  have hK : (N.subgroupOf (alternatingGroup (Fin n))).Normal :=
    Subgroup.Normal.subgroupOf hNn _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin n)))
    with h | h
  · exfalso
    apply hN
    rw [eq_bot_iff]
    intro σ hσ
    have hcomm : ∀ τ : Perm (Fin n), τ * σ = σ * τ := by
      intro τ
      have h1 : σ * τ * σ⁻¹ * τ⁻¹ ∈ N := by
        have := N.mul_mem hσ (hNn.conj_mem σ⁻¹ (N.inv_mem hσ) τ)
        simpa [mul_assoc] using this
      have h2 : σ * τ * σ⁻¹ * τ⁻¹ ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup]
        simp only [map_mul, map_inv]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
          rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h' <;> simp [h, h']
      have h3 : (⟨σ * τ * σ⁻¹ * τ⁻¹, h2⟩ : alternatingGroup (Fin n)) ∈
          N.subgroupOf (alternatingGroup (Fin n)) := h1
      rw [h, Subgroup.mem_bot] at h3
      have h4 : σ * τ * σ⁻¹ * τ⁻¹ = 1 := congrArg Subtype.val h3
      have h5 : σ * τ = τ * σ := by
        have := congrArg (· * (τ * σ)) h4
        simp only [one_mul] at this
        calc σ * τ = σ * τ * σ⁻¹ * τ⁻¹ * (τ * σ) := by group
          _ = τ * σ := by rw [h4]; simp
      exact h5.symm
    exact hc σ hcomm
  · intro x hx
    have : (⟨x, hx⟩ : alternatingGroup (Fin n)) ∈ N.subgroupOf (alternatingGroup (Fin n)) := by
      rw [h]; exact Subgroup.mem_top _
    exact this

theorem normal_ge_alt5 (N : Subgroup (Perm (Fin 5))) [N.Normal] (hN : N ≠ ⊥) :
    alternatingGroup (Fin 5) ≤ N := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact normal_ge_alt_of_simple perm_center_trivial5 N hN

theorem normal_ge_alt3 (N : Subgroup (Perm (Fin 3))) [N.Normal] (hN : N ≠ ⊥) :
    alternatingGroup (Fin 3) ≤ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsSimpleGroup (alternatingGroup (Fin 3)) := by
    refine isSimpleGroup_of_prime_card (p := 3) ?_
    have h := two_mul_nat_card_alternatingGroup (α := Fin 3)
    rw [Nat.card_perm] at h
    have e : Nat.card (Fin 3) = 3 := by simp
    rw [e] at h
    rw [show Nat.factorial 3 = 6 from rfl] at h
    omega
  exact normal_ge_alt_of_simple perm_center_trivial3 N hN

end F5c

section F5a

open Equiv

@[expose] def c4 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def s0 : Perm (Fin 5) := swap 0 2

@[expose] def D0fin : Finset (Perm (Fin 5)) :=
  Finset.univ.image fun p : Fin 4 × Fin 2 => c4 ^ (p.1 : ℕ) * s0 ^ (p.2 : ℕ)

theorem D0fin_card : D0fin.card = 8 := by decide +kernel

theorem D0fin_mul : ∀ x ∈ D0fin, ∀ y ∈ D0fin, x * y ∈ D0fin := by decide +kernel

theorem D0fin_inv : ∀ x ∈ D0fin, x⁻¹ ∈ D0fin := by decide +kernel

theorem D0fin_one : (1 : Perm (Fin 5)) ∈ D0fin := by decide +kernel

@[expose] def D0 : Subgroup (Perm (Fin 5)) where
  carrier := ↑D0fin
  one_mem' := D0fin_one
  mul_mem' := fun {a b} ha hb => D0fin_mul a ha b hb
  inv_mem' := fun {a} ha => D0fin_inv a ha

theorem normalizer_D0 : ∀ x : Perm (Fin 5), (∀ h : Perm (Fin 5), h ∈ D0fin ↔ x * h * x⁻¹ ∈ D0fin) →
    x ∈ D0fin := by decide +kernel

theorem card_perm5 : Nat.card (Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm]; simp [Nat.factorial]

theorem D0_card : Nat.card D0 = 8 := by
  have : Nat.card D0 = D0fin.card := by
    show Nat.card (↑D0fin : Set (Perm (Fin 5))) = D0fin.card
    simp
  rw [this, D0fin_card]

theorem D0_normalizer : Subgroup.normalizer (D0 : Set (Perm (Fin 5))) = D0 := by
  apply le_antisymm
  · intro x hx
    have := Subgroup.mem_normalizer_iff.mp hx
    exact normalizer_D0 x (fun h => this h)
  · exact Subgroup.le_normalizer

theorem sylow_of_card_eight (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    IsPGroup 2 P ∧ ¬ 2 ∣ P.index ∧ P.index = 15 := by
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hPi : P.index = 15 := by
    have := P.card_mul_index
    rw [hP, card_perm5] at this
    omega
  exact ⟨hP2, by rw [hPi]; decide, hPi⟩

theorem normalizer_eq_of_card_eight (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    Subgroup.normalizer (P : Set (Perm (Fin 5))) = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, hPi⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, hDi⟩ := sylow_of_card_eight D0 D0_card
  have e1 := Sylow.card_eq_index_normalizer (hP2.toSylow hPs)
  have e2 := Sylow.card_eq_index_normalizer (hD2.toSylow hDs)
  have e3 : (Subgroup.normalizer (P : Set (Perm (Fin 5)))).index =
      (Subgroup.normalizer (D0 : Set (Perm (Fin 5)))).index := by
    have h1 : ((hP2.toSylow hPs : Sylow 2 (Perm (Fin 5))) : Set (Perm (Fin 5))) = (P : Set _) := rfl
    have h2 : ((hD2.toSylow hDs : Sylow 2 (Perm (Fin 5))) : Set (Perm (Fin 5))) =
        (D0 : Set _) := rfl
    rw [h1] at e1
    rw [h2] at e2
    exact e1.symm.trans e2
  rw [D0_normalizer, hDi] at e3
  have e4 := (Subgroup.normalizer (P : Set (Perm (Fin 5)))).card_mul_index
  rw [e3, card_perm5] at e4
  have e5 : Nat.card (Subgroup.normalizer (P : Set (Perm (Fin 5)))) = 8 := by omega
  exact (Subgroup.eq_of_le_of_card_ge Subgroup.le_normalizer (by rw [e5, hP])).symm

end F5a

section F5b

open Equiv
open scoped Pointwise

theorem D0_fix : ∀ x ∈ D0fin, x 4 = 4 := by decide +kernel

theorem D0_trans : ∀ q : Fin 5, q ≠ 4 → ∀ j : Fin 5, j ≠ 4 → ∃ d ∈ D0fin, d q = j := by
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  rw [Nat.card_perm] at h
  have e : Nat.card (Fin 5) = 5 := by simp
  rw [e] at h
  rw [show Nat.factorial 5 = 120 from rfl] at h
  omega

theorem F5b_core (P K : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) (p₀ : Fin 5)
    (htr : ∀ q j : Fin 5, q ≠ p₀ → j ≠ p₀ → ∃ d ∈ P, d q = j)
    (hPK : P ≤ K) (hKT : ¬ K ≤ MulAction.stabilizer (Perm (Fin 5)) p₀) : K = ⊤ := by
  have hK : ∀ j : Fin 5, ∃ k ∈ K, k p₀ = j := by
    intro j
    simp only [IsConcreteLE.le_iff, MulAction.mem_stabilizer_iff, not_forall] at hKT
    obtain ⟨k, hk, hkp⟩ := hKT
    by_cases hj : j = p₀
    · exact ⟨1, K.one_mem, by simp [hj]⟩
    · obtain ⟨d, hd, hdj⟩ := htr (k p₀) j hkp hj
      exact ⟨d * k, K.mul_mem (hPK hd) hk, by simpa using hdj⟩
  have h5 : 5 ∣ Nat.card K := by
    have horb : (MulAction.orbit K p₀).ncard = 5 := by
      have : MulAction.orbit K p₀ = Set.univ := by
        ext j
        simp only [Set.mem_univ, iff_true]
        obtain ⟨k, hk, rfl⟩ := hK j
        exact ⟨⟨k, hk⟩, rfl⟩
      rw [this, Set.ncard_univ]; simp
    have h1 := MulAction.index_stabilizer K p₀
    rw [horb] at h1
    have h2 : (MulAction.stabilizer K p₀).index ∣ Nat.card K := Subgroup.index_dvd_card _
    rwa [h1] at h2
  have h8 : 8 ∣ Nat.card K := hP ▸ Subgroup.card_dvd_of_le hPK
  have h120 : Nat.card K ∣ 120 := card_perm5 ▸ Subgroup.card_subgroup_dvd_card K
  have hle : Nat.card K ≤ 120 := Nat.le_of_dvd (by norm_num) h120
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hcases : Nat.card K = 40 ∨ Nat.card K = 80 ∨ Nat.card K = 120 := by omega
  rcases hcases with h | h | h
  · exfalso
    have hidx : K.index = 3 := by
      have := K.card_mul_index
      rw [h, card_perm5] at this
      omega
    have : K.FiniteIndex := ⟨by omega⟩
    have hdvd : K.normalCore.index ∣ Nat.factorial K.index := K.index_normalCore_dvd_factorial_index
    rw [hidx, show Nat.factorial 3 = 6 from rfl] at hdvd
    have hN : K.normalCore.Normal := K.normalCore_normal
    have h6 : K.normalCore.index ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hNcard : 20 ≤ Nat.card K.normalCore := by
      have h1 := K.normalCore.card_mul_index
      rw [card_perm5] at h1
      by_contra hlt
      push Not at hlt
      have : Nat.card K.normalCore * K.normalCore.index ≤ 19 * 6 :=
        Nat.mul_le_mul (by omega) h6
      omega
    have hne : K.normalCore ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hNcard
      omega
    have halt := normal_ge_alt5 K.normalCore hne
    have := Subgroup.card_le_of_le (halt.trans K.normalCore_le)
    rw [card_alt5, h] at this
    omega
  · exfalso
    rw [h] at h120
    omega
  · exact Subgroup.eq_top_of_card_eq K (by rw [h, card_perm5])

theorem exists_fix_trans_of_card_eight (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    ∃ p₀ : Fin 5, (∀ x ∈ P, x p₀ = p₀) ∧
      ∀ q j : Fin 5, q ≠ p₀ → j ≠ p₀ → ∃ d ∈ P, d q = j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, -⟩ := sylow_of_card_eight D0 D0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) (hP2.toSylow hPs)
  have hPeq : ∀ x, x ∈ P ↔ ∃ y ∈ D0fin, g * y * g⁻¹ = x := by
    intro x
    have h1 : P = MulAut.conj g • D0 := by
      have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply, D0]
  refine ⟨g 4, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hPeq x).mp hx
    simp [Perm.mul_apply, D0_fix y hy]
  · intro q j hq hj
    have hq' : g⁻¹ q ≠ 4 := by
      intro h
      apply hq
      rw [Perm.inv_def, Equiv.symm_apply_eq] at h
      exact h
    have hj' : g⁻¹ j ≠ 4 := by
      intro h
      apply hj
      rw [Perm.inv_def, Equiv.symm_apply_eq] at h
      exact h
    obtain ⟨d, hd, hdq⟩ := D0_trans (g⁻¹ q) hq' (g⁻¹ j) hj'
    refine ⟨g * d * g⁻¹, (hPeq _).mpr ⟨d, hd, rfl⟩, ?_⟩
    have h3 : (g * d * g⁻¹) q = g (d (g⁻¹ q)) := rfl
    rw [h3, hdq]
    simp

theorem exists_unique_max_card_eight (P : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8) :
    ∃ T : Subgroup (Perm (Fin 5)), P ≤ T ∧ T.index = 5 ∧
      ∀ K : Subgroup (Perm (Fin 5)), P ≤ K → K ≠ ⊤ → K ≤ T := by
  obtain ⟨p₀, hfix, htr⟩ := exists_fix_trans_of_card_eight P hP
  refine ⟨MulAction.stabilizer (Perm (Fin 5)) p₀, fun x hx => hfix x hx, ?_, ?_⟩
  · rw [MulAction.index_stabilizer_of_transitive]
    simp
  · intro K hPK hK
    by_contra hKT
    exact hK (F5b_core P K hP p₀ htr hPK hKT)

end F5b

end CFSG.Quasithin.F53
