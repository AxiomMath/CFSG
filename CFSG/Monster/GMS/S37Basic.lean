module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Monster.GMS.S37

section Product

variable {G : Type*} [Group G]

theorem card_mul_card_le [Finite G] {A B L : Subgroup G} (hA : A ≤ L) (hB : B ≤ L) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card L := by
  have h1 := Subgroup.relIndex_inf_le (H := A) (K := B) (L := L)
  have eA : A.relIndex L * Nat.card A = Nat.card L := by
    have := Subgroup.relIndex_mul_card A L
    rwa [inf_eq_left.mpr hA] at this
  have eB : B.relIndex L * Nat.card B = Nat.card L := by
    have := Subgroup.relIndex_mul_card B L
    rwa [inf_eq_left.mpr hB] at this
  have eAB : (A ⊓ B).relIndex L * Nat.card ↥(A ⊓ B) = Nat.card L := by
    have := Subgroup.relIndex_mul_card (A ⊓ B) L
    rwa [inf_eq_left.mpr (inf_le_left.trans hA)] at this
  have hL : 0 < Nat.card L := Nat.card_pos
  have h2 : Nat.card L * (Nat.card A * Nat.card B) ≤
      Nat.card L * (Nat.card ↥(A ⊓ B) * Nat.card L) :=
    calc Nat.card L * (Nat.card A * Nat.card B)
        = ((A ⊓ B).relIndex L * Nat.card ↥(A ⊓ B)) * (Nat.card A * Nat.card B) := by rw [eAB]
      _ ≤ ((A.relIndex L * B.relIndex L) * Nat.card ↥(A ⊓ B)) * (Nat.card A * Nat.card B) := by
          gcongr
      _ = (A.relIndex L * Nat.card A) * (B.relIndex L * Nat.card B) * Nat.card ↥(A ⊓ B) := by
          ring
      _ = Nat.card L * (Nat.card ↥(A ⊓ B) * Nat.card L) := by rw [eA, eB]; ring
  exact Nat.le_of_mul_le_mul_left h2 hL

theorem odd_card_of_forall_orderOf_ne_two [Finite G] (M : Subgroup G)
    (h : ∀ t ∈ M, orderOf t ≠ 2) : Odd (Nat.card M) := by
  by_contra hev
  have h2 : 2 ∣ Nat.card M := (Nat.not_odd_iff_even.mp hev).two_dvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact h x.1 x.2 (by rw [Subgroup.orderOf_coe]; exact hx)

theorem le_two_pow_mul_of_dvd {d m n k : ℕ} (hm : 0 < m) (hd : d ∣ 2 ^ n * m)
    (hk : ¬ 2 ^ (k + 1) ∣ d) : d ≤ 2 ^ k * m := by
  obtain ⟨d₁, d₂, h1, h2, rfl⟩ := Nat.dvd_mul.mp hd
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hik : i ≤ k := by
    by_contra hlt
    exact hk ((pow_dvd_pow 2 (by omega)).trans (dvd_mul_right _ _))
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hik) (Nat.le_of_dvd hm h2)

end Product

section TwoGroups

variable {G : Type*} [Group G] [Finite G]

theorem exists_sq_mem_of_card_dvd {K V : Subgroup G} (hVK : V ≤ K) {n : ℕ}
    (hV : Nat.card V = 2 ^ n) (hK : 2 ^ (n + 1) ∣ Nat.card K) :
    ∃ K' : Subgroup G, V ≤ K' ∧ K' ≤ K ∧ Nat.card K' = 2 ^ (n + 1) ∧ ∀ g ∈ K', g * g ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' : Nat.card (V.subgroupOf K) = 2 ^ n := by
    rw [← hV]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  obtain ⟨K'', hK''c, hVK''⟩ := Sylow.exists_subgroup_card_pow_succ hK hV'
  refine ⟨K''.map K.subtype, ?_, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨⟨g, hVK hg⟩, hVK'' hg, rfl⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hK''c]
  · rintro _ ⟨k, hk, rfl⟩
    have hrel : (V.subgroupOf K).relIndex K'' = 2 := by
      have h := Subgroup.relIndex_mul_card (V.subgroupOf K) K''
      rw [inf_eq_left.mpr hVK'', hV', hK''c, pow_succ] at h
      rw [mul_comm (2 ^ n) 2] at h
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (by norm_num) n) h
    have : ((V.subgroupOf K).subgroupOf K'').Normal :=
      Subgroup.normal_of_index_eq_two hrel
    have hpow := Subgroup.pow_index_mem ((V.subgroupOf K).subgroupOf K'') ⟨k, hk⟩
    have hidx : ((V.subgroupOf K).subgroupOf K'').index = 2 := hrel
    rw [hidx, pow_two] at hpow
    exact hpow

theorem exists_subgroup_card_mul_two {K : Subgroup G} (h2 : 2 ∣ Nat.card K)
    (h4 : ¬ 4 ∣ Nat.card K) : ∃ N : Subgroup G, N ≤ K ∧ Nat.card N * 2 = Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 K := default
  have hfac : (Nat.card K).factorization 2 = 1 := by
    have hpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hge : 1 ≤ (Nat.card K).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mp (by simpa using h2)
    have hlt : ¬ 2 ≤ (Nat.card K).factorization 2 := fun h =>
      h4 (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).mpr h)
    omega
  have hPcard : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hfac]
    rfl
  have hcyc : IsCyclic P := isCyclic_of_prime_card hPcard
  have hminFac : (Nat.card K).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hcompl := IsCyclic.isComplement' hminFac hcyc
  have hmul := hcompl.card_mul_card
  rw [hPcard] at hmul
  refine ⟨(MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hminFac)).ker.map
    K.subtype, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact hmul

end TwoGroups

section FourGroup

variable {G : Type*} [Group G]

@[expose] def fourSub (b t : G) (hb : b * b = 1) (ht : t * t = 1) (hbt : b * t = t * b) :
    Subgroup G where
  carrier := {1, b, t, b * t}
  one_mem' := by simp
  mul_mem' := by
    have hbt' : t * b = b * t := hbt.symm
    have h1 : b * (b * t) = t := by rw [← mul_assoc, hb, one_mul]
    have h4 : (b * t) * t = b := by rw [mul_assoc, ht, mul_one]
    have h2 : t * (b * t) = b := by
      calc t * (b * t) = (t * b) * t := (mul_assoc _ _ _).symm
        _ = (b * t) * t := by rw [hbt']
        _ = b := h4
    have h3 : (b * t) * b = t := by rw [hbt, mul_assoc, hb, mul_one]
    have h5 : (b * t) * (b * t) = 1 := by
      calc (b * t) * (b * t) = ((b * t) * b) * t := (mul_assoc _ _ _).symm
        _ = t * t := by rw [h3]
        _ = 1 := ht
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [hb, ht, hbt', h1, h2, h3, h4, h5]
  inv_mem' := by
    have h5 : (b * t) * (b * t) = 1 := by
      calc (b * t) * (b * t) = b * (t * b) * t := by group
        _ = b * (b * t) * t := by rw [← hbt]
        _ = 1 := by rw [← mul_assoc, hb, one_mul, ht]
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have hbti : (b * t)⁻¹ = b * t := inv_eq_of_mul_eq_one_right h5
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx] <;> simp [hbi, hti, hbti]

theorem mem_fourSub {b t : G} {hb : b * b = 1} {ht : t * t = 1} {hbt : b * t = t * b} {g : G} :
    g ∈ fourSub b t hb ht hbt ↔ g = 1 ∨ g = b ∨ g = t ∨ g = b * t := Iff.rfl

theorem card_fourSub {b t : G} (hb : b * b = 1) (ht : t * t = 1) (hbt : b * t = t * b)
    (hb1 : b ≠ 1) (ht1 : t ≠ 1) (hne : b ≠ t) : Nat.card (fourSub b t hb ht hbt) = 4 := by
  have hbti : b * t ≠ 1 := by
    intro h
    exact hne (by rw [eq_inv_of_mul_eq_one_left h]; exact inv_eq_of_mul_eq_one_right ht)
  have hbtb : b * t ≠ b := fun h => ht1 (by simpa using h)
  have hbtt : b * t ≠ t := fun h => hb1 (by simpa using h)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  change ({1, b, t, b * t} : Set G).ncard = 4
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hbtt.symm]
  · simp [hne, hbtb.symm]
  · simp [hb1.symm, ht1.symm, hbti.symm]

end FourGroup

end CFSG.Monster.GMS.S37
