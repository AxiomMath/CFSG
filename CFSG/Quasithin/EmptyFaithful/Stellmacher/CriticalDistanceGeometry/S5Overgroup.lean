module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasFin

public section

namespace CFSG.Quasithin.F53

open Equiv
open scoped Pointwise

@[expose] def T0fin : Finset (Perm (Fin 5)) := {1, c4 ^ 2, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2}
@[expose] def That0fin : Finset (Perm (Fin 5)) := {1, swap 0 2, swap 1 3, swap 0 2 * swap 1 3}

theorem klein_classify : ∀ F ∈ D0fin.powerset, F.card = 4 → (∀ x ∈ F, ∀ y ∈ F, x * y ∈ F) →
    (∀ x ∈ F, x * x = 1) → F = T0fin ∨ F = That0fin := by decide +kernel

theorem T0fin_even : ∀ x ∈ T0fin, Perm.sign x = 1 := by decide +kernel
theorem That0fin_comm : ∀ x ∈ That0fin, swap 0 2 * x = x * swap 0 2 := by decide +kernel
theorem card_cent : (Finset.univ.filter fun g : Perm (Fin 5) => swap 0 2 * g = g * swap 0 2).card = 12 := by decide +kernel

theorem card_centralizer_swap : Nat.card (Subgroup.centralizer {swap (0 : Fin 5) 2}) = 12 := by
  have : Nat.card (Subgroup.centralizer {swap (0 : Fin 5) 2}) =
      (Finset.univ.filter fun g : Perm (Fin 5) => swap 0 2 * g = g * swap 0 2).card := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun g => by
      simp [Subgroup.mem_centralizer_iff, eq_comm])
  rw [this, card_cent]

theorem klein_overgroup_D0 (R : Subgroup (Perm (Fin 5))) (hRP : R ≤ D0) (hR : Nat.card R = 4)
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) :
    ∃ K : Subgroup (Perm (Fin 5)), R ≤ K ∧ (Nat.card K = 60 ∨ Nat.card K = 12) ∧ K ⊔ D0 = ⊤ := by
  classical
  set F := D0fin.filter (fun x => x ∈ R) with hF
  have hmem : ∀ x, x ∈ F ↔ x ∈ R := by
    intro x
    simp only [hF, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hRP h, h⟩⟩
  have hFc : F.card = 4 := by
    rw [← hR]
    have : (R : Set (Perm (Fin 5))) = ↑F := by ext x; simp [hmem]
    show F.card = Nat.card (R : Set (Perm (Fin 5)))
    rw [this]; simp
  have hcl := klein_classify F (by simp [hF]) hFc
    (fun x hx y hy => (hmem _).mpr (R.mul_mem ((hmem _).mp hx) ((hmem _).mp hy)))
    (fun x hx => by have := hR2 x ((hmem _).mp hx); rwa [pow_two] at this)
  rcases hcl with h | h
  · refine ⟨alternatingGroup (Fin 5), ?_, Or.inl card_alt5, ?_⟩
    · intro x hx
      have := T0fin_even x (h ▸ (hmem x).mpr hx)
      exact Perm.mem_alternatingGroup.mpr this
    · have h60 : 60 ∣ Nat.card (alternatingGroup (Fin 5) ⊔ D0 :) := card_alt5 ▸ Subgroup.card_dvd_of_le le_sup_left
      have h8 : 8 ∣ Nat.card (alternatingGroup (Fin 5) ⊔ D0 :) := D0_card ▸ Subgroup.card_dvd_of_le le_sup_right
      have h120 : Nat.card (alternatingGroup (Fin 5) ⊔ D0 :) ∣ 120 :=
        card_perm5 ▸ Subgroup.card_subgroup_dvd_card _
      have hpos : 0 < Nat.card (alternatingGroup (Fin 5) ⊔ D0 :) := Nat.card_pos
      have h120' : Nat.card (alternatingGroup (Fin 5) ⊔ D0 :) = 120 := by
        have := Nat.le_of_dvd (by norm_num) h120
        omega
      exact Subgroup.eq_top_of_card_eq _ (by rw [card_perm5]; exact h120')
  · refine ⟨Subgroup.centralizer {swap (0 : Fin 5) 2}, ?_, Or.inr card_centralizer_swap, ?_⟩
    · intro x hx
      have := That0fin_comm x (h ▸ (hmem x).mpr hx)
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      exact this
    · apply F5b_core D0 _ D0_card 4 (fun q j hq hj => D0_trans q hq j hj)
          (le_sup_right)
      intro hle
      have h1 : swap (1 : Fin 5) 4 ∈ Subgroup.centralizer {swap (0 : Fin 5) 2} := by
        simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
        decide +kernel
      have := hle (le_sup_left (a := Subgroup.centralizer {swap (0 : Fin 5) 2}) (b := D0) h1)
      simp [MulAction.mem_stabilizer_iff] at this

theorem exists_overgroup_of_klein (P R : Subgroup (Perm (Fin 5))) (hP : Nat.card P = 8)
    (hRP : R ≤ P) (hR : Nat.card R = 4) (hR2 : ∀ r ∈ R, r ^ 2 = 1) :
    ∃ K : Subgroup (Perm (Fin 5)), R ≤ K ∧ ¬ 2 ∣ (R.subgroupOf K).index ∧ K ⊔ P = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPs, -⟩ := sylow_of_card_eight P hP
  obtain ⟨hD2, hDs, -⟩ := sylow_of_card_eight D0 D0_card
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 5)) (hD2.toSylow hDs) (hP2.toSylow hPs)
  have hPeq : ∀ x, x ∈ P ↔ ∃ y ∈ D0, g * y * g⁻¹ = x := by
    intro x
    have h1 : P = MulAut.conj g • D0 := by
      have := congrArg (fun Q : Sylow 2 (Perm (Fin 5)) => (Q : Subgroup (Perm (Fin 5)))) hg
      simpa [Sylow.coe_subgroup_smul] using this.symm
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    simp [MulAut.conj_apply]
  let φ : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj g).toMonoidHom
  let ψ : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj g⁻¹).toMonoidHom
  have hφψ : ∀ x, φ (ψ x) = x := by intro x; simp [φ, ψ, MulAut.conj_apply]; group
  have hψφ : ∀ x, ψ (φ x) = x := by intro x; simp [φ, ψ, MulAut.conj_apply]; group
  have hφinj : Function.Injective φ := fun a b h => by simpa [hψφ] using congrArg ψ h
  have hψinj : Function.Injective ψ := fun a b h => by simpa [hφψ] using congrArg φ h
  have hPmap : D0.map φ = P := by
    ext x
    rw [hPeq, Subgroup.mem_map]
    simp [φ, MulAut.conj_apply]
  have hR' : R.map ψ ≤ D0 := by
    rintro y ⟨r, hr, rfl⟩
    obtain ⟨y', hy', hyr⟩ := (hPeq r).mp (hRP hr)
    have : ψ r = y' := by rw [← hyr]; simp [ψ]; group
    rw [this]; exact hy'
  obtain ⟨K', hRK', hK'c, hK'top⟩ := klein_overgroup_D0 (R.map ψ) hR'
    (by rw [Subgroup.card_map_of_injective hψinj]; exact hR)
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_pow, hR2 r hr, map_one])
  refine ⟨K'.map φ, ?_, ?_, ?_⟩
  · intro r hr
    exact ⟨ψ r, hRK' ⟨r, hr, rfl⟩, hφψ r⟩
  · have hRK : R ≤ K'.map φ := fun r hr => ⟨ψ r, hRK' ⟨r, hr, rfl⟩, hφψ r⟩
    have h1 := Subgroup.relIndex_mul_index hRK
    have h2 := R.card_mul_index
    have h3 := (K'.map φ).card_mul_index
    rw [hR, card_perm5] at h2
    rw [card_perm5] at h3
    show ¬ 2 ∣ R.relIndex (K'.map φ)
    rw [Subgroup.card_map_of_injective hφinj] at h3
    rcases hK'c with h | h <;> rw [h] at h3
    · have hi : (K'.map φ).index = 2 := by omega
      rw [hi] at h1
      omega
    · have hi : (K'.map φ).index = 10 := by omega
      rw [hi] at h1
      omega
  · rw [← hPmap, ← Subgroup.map_sup, hK'top, Subgroup.map_top_of_surjective _ (fun x => ⟨ψ x, hφψ x⟩)]

theorem exponent_two_or_cyclic_of_card_four {X : Type*} [Group X] (h : Nat.card X = 4) :
    (∀ x : X, x ^ 2 = 1) ∨ ∃ x : X, orderOf x = 4 := by
  by_cases hall : ∀ x : X, x ^ 2 = 1
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨x, hx⟩ := hall
    have hd : orderOf x ∣ 4 := h ▸ orderOf_dvd_natCard x
    refine ⟨x, ?_⟩
    have h2 : ¬ orderOf x ∣ 2 := fun hh => hx (orderOf_dvd_iff_pow_eq_one.mp hh)
    have hp : orderOf x ∣ 2 ^ 2 := by simpa using hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hp
    interval_cases k
    · simp at hk'; rw [hk'] at h2; simp at h2
    · simp at hk'; rw [hk'] at h2; simp at h2
    · simpa using hk'

theorem sq_ne_one_of_orderOf_four {n : ℕ} {r : Perm (Fin n)} (h : orderOf r = 4) :
    r ^ 2 ≠ 1 ∧ (r ^ 2) ^ 2 = 1 ∧ r ^ 2 ∈ alternatingGroup (Fin n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [h] at this
    omega
  · rw [← pow_mul, show 2 * 2 = 4 by rfl, ← h]; exact pow_orderOf_eq_one r
  · rw [Perm.mem_alternatingGroup, map_pow]
    rcases Int.units_eq_one_or (Perm.sign r) with h | h <;> simp [h]
end CFSG.Quasithin.F53
