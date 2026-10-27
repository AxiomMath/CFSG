module

public import CFSG.Quasithin.Vol2.Asc94.TS39c

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

structure Frame3 (G : Type) [Group G] (z : G) extends Frame2 G z where
  Δ : Fin 7 → Set G
  Δ_disj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)
  Δ_union : (⋃ i, Δ i) = (A : Set G) \ {1}
  Δ_inv : ∀ i, ∀ a ∈ Δ i, ∀ x ∈ Cz z ⊓ Subgroup.normalizer (A : Set G), x⁻¹ * a * x ∈ Δ i
  Δ_trans : ∀ i, ∀ a ∈ Δ i, ∀ b ∈ Δ i,
    ∃ x ∈ Cz z ⊓ Subgroup.normalizer (A : Set G), b = x⁻¹ * a * x
  Δ_card : ∀ i, (Δ i).ncard = ![1, 6, 2, 6, 12, 12, 24] i
  Δ0 : Δ 0 = {z}
  Δ1 : Δ 1 = ((A ⊓ U : Subgroup G) : Set G) \ {1, z}
  Δ2_sub : ∀ a ∈ Δ 2, a ∈ U2 ∧ a ≠ 1 ∧ a ≠ z
  Δ3_sub : ∀ a ∈ Δ 3, a ∈ TQ

@[expose] def Frame2.NA (F : Frame2 G z) : Subgroup G :=
  Cz z ⊓ Subgroup.normalizer (F.A : Set G)

@[expose] def Frame2.Sz (F : Frame2 G z) : Set G := {a | a ∈ F.A ∧ a ≠ 1 ∧ InZG z a}

theorem Frame2.z_ne_one (F : Frame2 G z) : z ≠ 1 := F.toFrame1.toFrame0.z_ne_one

theorem Frame2.conj_mem_A (F : Frame2 G z) {a l : G} (ha : a ∈ F.A)
    (hl : l ∈ Subgroup.normalizer (F.A : Set G)) : l⁻¹ * a * l ∈ F.A := by
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl) a).1 ha
  simpa using this

theorem Frame2.conj_mem_Sz (F : Frame2 G z) {a l : G} (ha : a ∈ F.Sz)
    (hl : l ∈ Subgroup.normalizer (F.A : Set G)) : l⁻¹ * a * l ∈ F.Sz := by
  obtain ⟨haA, ha1, g, hg⟩ := ha
  refine ⟨F.conj_mem_A haA hl, fun h => ha1 ?_, g * l, ?_⟩
  · have : a = l * (l⁻¹ * a * l) * l⁻¹ := by group
    rw [this, h]
    group
  · rw [hg]
    group

theorem Frame2.card_normalizer_A (F : Frame2 G z) :
    Nat.card ↥(Subgroup.normalizer (F.A : Set G)) = F.Sz.ncard * Nat.card ↥F.NA := by
  have h := Gen.card_conjOrbit_mul_card_stab (Subgroup.normalizer (F.A : Set G)) z
  have hO : {x : G | ∃ l ∈ Subgroup.normalizer (F.A : Set G), x = l⁻¹ * z * l} = F.Sz := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact F.conj_mem_Sz ⟨F.z_mem_A, F.z_ne_one, 1, by simp⟩ hl
    · rintro ⟨haA, ha1, g, hg⟩
      obtain ⟨n, hn, hnx⟩ := s39_6_3 F F.z_mem_A haA hg.symm
      exact ⟨n, hn, hnx.symm⟩
  have h1 : Nat.card {x : G // ∃ l ∈ Subgroup.normalizer (F.A : Set G), x = l⁻¹ * z * l} =
      F.Sz.ncard := by
    rw [← hO, ← Nat.card_coe_set_eq]
    rfl
  have hNA : Subgroup.normalizer (F.A : Set G) ⊓ Subgroup.centralizer ({z} : Set G) = F.NA := by
    rw [inf_comm]
    rfl
  rw [h1, hNA] at h
  exact h.symm

open Classical in
theorem Frame3.ncard_Sz_eq_sum (F : Frame3 G z)
    (hdich : ∀ i, F.Δ i ⊆ F.Sz ∨ Disjoint (F.Δ i) F.Sz) :
    F.Sz.ncard = ∑ i : Fin 7, if F.Δ i ⊆ F.Sz then (F.Δ i).ncard else 0 := by
  have hS : F.Sz ⊆ ⋃ i, F.Δ i := by
    intro a ha
    rw [F.Δ_union]
    exact ⟨ha.1, ha.2.1⟩
  have hU : F.Sz = ⋃ i, F.Sz ∩ F.Δ i := by
    ext a
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro ha
      have := hS ha
      simp only [Set.mem_iUnion] at this
      obtain ⟨i, hi⟩ := this
      exact ⟨i, ha, hi⟩
    · rintro ⟨i, ha, -⟩
      exact ha
  have hpair : Pairwise (Function.onFun Disjoint fun i => F.Sz ∩ F.Δ i) := by
    intro i j hij
    exact (F.Δ_disj i j hij).mono Set.inter_subset_right Set.inter_subset_right
  have hfin : ∀ i, (F.Sz ∩ F.Δ i).Finite := fun i => Set.toFinite _
  conv_lhs => rw [hU]
  rw [Set.ncard_iUnion_of_finite hfin hpair, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hdich i with h | h
  · rw [if_pos h, Set.inter_eq_right.2 h]
  · have hsub : ¬ F.Δ i ⊆ F.Sz := by
      intro hsub
      have hne : (F.Δ i).Nonempty := Set.nonempty_of_ncard_ne_zero (by
        rw [F.Δ_card i]
        fin_cases i <;> simp)
      obtain ⟨a, ha⟩ := hne
      exact Set.disjoint_left.1 h ha (hsub ha)
    rw [if_neg hsub, Set.inter_comm, h.inter_eq, Set.ncard_empty]

theorem Frame2.not_prime_dvd_card_normalizer (F : Frame2 G z) (p : ℕ) [hp : Fact p.Prime]
    (hpH : ¬ p ∣ 21504) (hcong : ∀ c : ℕ, c ∣ 64 → Nat.ModEq p 64 c → c = 64) :
    ¬ p ∣ Nat.card ↥(Subgroup.normalizer (F.A : Set G)) := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.normalizer (F.A : Set G))) p
    hdvd
  set y : G := (x : G) with hy
  have hyo : orderOf y = p := by rw [hy, Subgroup.orderOf_coe]; exact hx
  have hyN : y ∈ Subgroup.normalizer (F.A : Set G) := x.2
  have hmod := Gen.card_modEq_card_centralizer_inf hyo hyN
  have hdvdc : Nat.card ↥(F.A ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 64 := by
    rw [← F.card_A]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [F.card_A] at hmod
  have hc := hcong _ hdvdc hmod
  have hle : F.A ≤ Subgroup.centralizer ({y} : Set G) := by
    have heq : F.A ⊓ Subgroup.centralizer ({y} : Set G) = F.A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, F.card_A])
    exact inf_eq_left.1 heq
  have hyH : y ∈ Cz z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle F.z_mem_A)
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  have hord : orderOf (⟨y, hyH⟩ : ↥(Cz z)) = p := by
    rw [← Subgroup.orderOf_coe]
    exact hyo
  apply hpH
  have := orderOf_dvd_natCard (⟨y, hyH⟩ : ↥(Cz z))
  rwa [hord, F.card_H] at this

end CFSG.Quasithin.A94
