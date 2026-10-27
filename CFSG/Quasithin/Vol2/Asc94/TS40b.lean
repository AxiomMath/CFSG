module

public import CFSG.Quasithin.Vol2.Asc94.TS40a
public import CFSG.Quasithin.Vol2.Asc94.TS39g

public section

namespace CFSG.Quasithin.A94

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem ncard_eq_sum_of_dich {α : Type} [Finite α] {n : ℕ} (Δ : Fin n → Set α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) (S : Set α) (hS : S ⊆ ⋃ i, Δ i)
    (hdich : ∀ i, Δ i ⊆ S ∨ Disjoint (Δ i) S) (hne : ∀ i, (Δ i).Nonempty) :
    S.ncard = ∑ i : Fin n, open Classical in if Δ i ⊆ S then (Δ i).ncard else 0 := by
  classical
  have hU : S = ⋃ i, S ∩ Δ i := by
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
  have hpair : Pairwise (Function.onFun Disjoint fun i => S ∩ Δ i) := by
    intro i j hij
    exact (hdisj i j hij).mono Set.inter_subset_right Set.inter_subset_right
  have hfin : ∀ i, (S ∩ Δ i).Finite := fun i => Set.toFinite _
  conv_lhs => rw [hU]
  rw [Set.ncard_iUnion_of_finite hfin hpair, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hdich i with h | h
  · rw [if_pos h, Set.inter_eq_right.2 h]
  · have hsub : ¬ Δ i ⊆ S := by
      intro hsub
      obtain ⟨a, ha⟩ := hne i
      exact Set.disjoint_left.1 h ha (hsub ha)
    rw [if_neg hsub, Set.inter_comm, h.inter_eq, Set.ncard_empty]

theorem conj_mem_of_mem_normalizer {X : Subgroup G} {a l : G} (ha : a ∈ X)
    (hl : l ∈ Subgroup.normalizer (X : Set G)) : l⁻¹ * a * l ∈ X := by
  have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hl) a).1 ha
  simpa using this

@[expose] def Frame4.Gz (F : Frame4 G z) : Set G :=
  {b | b ∈ F.A ⊓ F.A' ∧ b ≠ 1 ∧ InZG z b}

theorem Frame4.z_mem_B (F : Frame4 G z) : z ∈ F.A ⊓ F.A' := ⟨F.z_mem_A, F.z_mem_A'⟩

theorem Frame4.conj_mem_Gz_of {F : Frame4 G z} {b l : G} (hb : b ∈ F.Gz)
    (hlA : l⁻¹ * b * l ∈ F.A ⊓ F.A') : l⁻¹ * b * l ∈ F.Gz := by
  obtain ⟨-, hb1, g, hg⟩ := hb
  refine ⟨hlA, fun h => hb1 ?_, g * l, ?_⟩
  · have : b = l * (l⁻¹ * b * l) * l⁻¹ := by group
    rw [this, h]
    group
  · rw [hg]
    group

theorem Frame4.conj_mem_Gz_J (F : Frame4 G z) {b l : G} (hb : b ∈ F.Gz)
    (hl : l ∈ Subgroup.normalizer (F.J : Set G)) : l⁻¹ * b * l ∈ F.Gz := by
  obtain ⟨hlA, hlA'⟩ := F.normalizer_J_le hl
  exact F.conj_mem_Gz_of hb ⟨conj_mem_of_mem_normalizer (Subgroup.mem_inf.1 hb.1).1 hlA,
    conj_mem_of_mem_normalizer (Subgroup.mem_inf.1 hb.1).2 hlA'⟩

theorem Frame4.conj_mem_Gz_T (F : Frame4 G z) {b l : G} (hb : b ∈ F.Gz) (hl : l ∈ F.T) :
    l⁻¹ * b * l ∈ F.Gz :=
  F.conj_mem_Gz_of hb ⟨F.A_normal l hl b (Subgroup.mem_inf.1 hb.1).1,
    F.A'_normal l hl b (Subgroup.mem_inf.1 hb.1).2⟩

theorem Frame4.card_normalizer_J (F : Frame4 G z) :
    Nat.card ↥(Subgroup.normalizer (F.J : Set G)) = F.Gz.ncard * 1024 := by
  have hO : {x : G | ∃ l ∈ Subgroup.normalizer (F.J : Set G), x = l⁻¹ * z * l} = F.Gz := by
    ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact F.conj_mem_Gz_J ⟨F.z_mem_B, F.z_ne_one, 1, by simp⟩ hl
    · rintro ⟨hxB, hx1, g, hg⟩
      obtain ⟨n, hn, hnx⟩ := F.fusion_B F.z_mem_B hxB hg.symm
      exact ⟨n, hn, hnx.symm⟩
  have h := card_orbit_eq_ncard (Subgroup.normalizer (F.J : Set G)) z F.Gz hO
  have hstab : Subgroup.normalizer (F.J : Set G) ⊓ Subgroup.centralizer ({z} : Set G) = F.T := by
    apply le_antisymm
    · intro x hx
      exact F.NH_J x (Subgroup.mem_inf.1 hx).2 (Subgroup.mem_inf.1 hx).1
    · intro t ht
      exact ⟨F.T_le_normalizer_J ht, F.T_le_H ht⟩
  rw [hstab, F.card_T] at h
  exact h.symm

theorem Frame4.not_prime_dvd_card_normalizer_J (F : Frame4 G z) (p : ℕ) [hp : Fact p.Prime]
    (hpH : ¬ p ∣ 21504) (hcong : ∀ c : ℕ, c ∣ 16 → Nat.ModEq p 16 c → c = 16) :
    ¬ p ∣ Nat.card ↥(Subgroup.normalizer (F.J : Set G)) := by
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.normalizer (F.J : Set G))) p hdvd
  set y : G := (x : G) with hy
  have hyo : orderOf y = p := by rw [hy, Subgroup.orderOf_coe]; exact hx
  have hyN : y ∈ Subgroup.normalizer (F.J : Set G) := x.2
  obtain ⟨hyA, hyA'⟩ := F.normalizer_J_le hyN
  have hyB : y ∈ Subgroup.normalizer ((F.A ⊓ F.A' : Subgroup G) : Set G) := by
    rw [Gen.mem_normalizer_iff_cj, Gen.cj_inf, Gen.mem_normalizer_iff_cj.1 hyA,
      Gen.mem_normalizer_iff_cj.1 hyA']
  have hmod := Gen.card_modEq_card_centralizer_inf hyo hyB
  have hdvdc : Nat.card ↥((F.A ⊓ F.A') ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 16 := by
    rw [← F.card_B]
    exact Subgroup.card_dvd_of_le inf_le_left
  rw [F.card_B] at hmod
  have hc := hcong _ hdvdc hmod
  have hle : (F.A ⊓ F.A') ≤ Subgroup.centralizer ({y} : Set G) := by
    have heq : (F.A ⊓ F.A') ⊓ Subgroup.centralizer ({y} : Set G) = F.A ⊓ F.A' :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, F.card_B])
    exact inf_eq_left.1 heq
  have hyH : y ∈ Cz z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hle F.z_mem_B)
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  exact F.toFrame2.not_mem_H_of_order p hpH hyo hyH

end CFSG.Quasithin.A94
