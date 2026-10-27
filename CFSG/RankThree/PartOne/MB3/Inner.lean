module

public import CFSG.RankThree.PartOne.MB3.Rank

public section

namespace CFSG.RankThree.PartOne.MB3

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

variable {G : Type} [Group G]

theorem mem_zpowers_pow_of_coprime {g : G} {k m : ℕ} (hcop : Nat.Coprime k m) (hg : g ^ m = 1) :
    g ∈ Subgroup.zpowers (g ^ k) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨u, ?_⟩
  have h2 : g ^ (v * (m : ℤ)) = 1 := by
    rw [mul_comm, zpow_mul, zpow_natCast, hg, one_zpow]
  calc (g ^ k) ^ u = g ^ (u * (k : ℤ)) := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm]
    _ = g ^ (u * (k : ℤ) + v * (m : ℤ)) := by rw [zpow_add, h2, mul_one]
    _ = g := by rw [huv, zpow_one]

theorem exists_pow_orderOf_seven {K : Subgroup G} {g : G} (hg : g ∈ K)
    (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K)) (h7 : ∀ k ∈ K, g ^ 7 * k = k * g ^ 7)
    (hnc : ∃ k ∈ K, g * k ≠ k * g) : ∃ m : ℕ, orderOf (g ^ m) = 7 := by
  have hw : (⟨g ^ 7, K.pow_mem hg 7⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun k => Subtype.ext (h7 k k.2).symm
  have hm : orderOf (⟨⟨g ^ 7, K.pow_mem hg 7⟩, hw⟩ : Subgroup.center K) ∣
      Nat.card (Subgroup.center K) := orderOf_dvd_natCard _
  have hcop : Nat.Coprime 7 (orderOf (⟨⟨g ^ 7, K.pow_mem hg 7⟩, hw⟩ : Subgroup.center K)) :=
    (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr fun h => hZ (h.trans hm)
  have hwm : (g ^ 7) ^ orderOf (⟨⟨g ^ 7, K.pow_mem hg 7⟩, hw⟩ : Subgroup.center K) = 1 := by
    simp
  set m := orderOf (⟨⟨g ^ 7, K.pow_mem hg 7⟩, hw⟩ : Subgroup.center K) with hmdef
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine ⟨m, orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul]; exact hwm) fun h1 => ?_⟩
  obtain ⟨a, ha'⟩ := mem_zpowers_pow_of_coprime hcop h1
  have ha : (g ^ 7) ^ a = g := ha'
  obtain ⟨k, hk, hne⟩ := hnc
  apply hne
  calc g * k = (g ^ 7) ^ a * k := by rw [ha]
    _ = k * (g ^ 7) ^ a := (Commute.zpow_left (show Commute (g ^ 7) k from h7 k hk) a).eq
    _ = k * g := by rw [ha]

namespace Branch

variable [Finite G] {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ} {b : G}
  {S K K' : Subgroup G} {a' : G} {x : G} {lam : ℤ}

theorem comm_b₀ (H : Branch 7 A c L B n b S K K' a') : ∀ k ∈ K, b * k = k * b := fun _ hk =>
  (H.commute_b_of_mem_K hk).symm

theorem comm_b₁ (H : Branch 7 A c L B n b S K K' a') (X : Xdata A c L B x lam) :
    ∀ k ∈ conjBy x K, b * k = k * b := fun _ hk =>
  (mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp (H.K₁_mem X)).1 hk)).symm

theorem comm_b₂ (H : Branch 7 A c L B n b S K K' a') (X : Xdata A c L B x lam) :
    ∀ k ∈ conjBy x (conjBy x K), b * k = k * b := fun _ hk =>
  (mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp (H.K₂_mem X)).1 hk)).symm

theorem c_notMem_sup_centralizer (H : Branch 7 A c L B n b S K K' a') (X : Xdata A c L B x lam)
    (hKq : CFSG.IsQuasisimple K) (hZ : ¬ 7 ∣ Nat.card (Subgroup.center K))
    (hr : localRank 7 G ≤ 3) : c ∉ K ⊔ Subgroup.centralizer (K : Set G) := by
  intro hc
  have hT : Triple K x := ⟨H.comm₀₁ X hKq, H.comm₀₂ X hKq, H.comm₁₂ X hKq⟩
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.centralizer (K : Set G)) K
    (fun g hg => Subgroup.centralizer_le_normalizer _ hg)
  have hc' : c ∈ ((Subgroup.centralizer (K : Set G) ⊔ K : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hc
  rw [hmul] at hc'
  obtain ⟨z, hz, c', hc'K, hzc'⟩ := hc'
  have hzc : z * c' = c := hzc'
  have hzK : ∀ k ∈ K, k * z = z * k := Subgroup.mem_centralizer_iff.mp hz
  have hcS : c ∈ Subgroup.normalizer (S : Set G) := H.witness.S_norm H.config.c_mem
  have hzS : z ∈ Subgroup.normalizer (S : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr H.S_le) hz)
  have hc'eq : c' = z⁻¹ * c := by rw [← hzc]; group
  have hc'S : c' ∈ Subgroup.normalizer (S : Set G) := by
    rw [hc'eq]
    exact (Subgroup.normalizer (S : Set G)).mul_mem
      ((Subgroup.normalizer (S : Set G)).inv_mem hzS) hcS
  have hcomm : Commute z c' := (hzK c' hc'K).symm
  have hc7 : c ^ 7 = 1 := H.config.pow_p_eq_one H.config.c_mem
  have hpow7 : c' ^ 7 = (z ^ 7)⁻¹ := by
    have h1 : z ^ 7 * c' ^ 7 = 1 := by rw [← hcomm.mul_pow, hzc, hc7]
    exact eq_inv_of_mul_eq_one_right h1
  have h7 : ∀ k ∈ K, c' ^ 7 * k = k * c' ^ 7 := by
    intro k hk
    have hz7 : (z ^ 7)⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).inv_mem ((Subgroup.centralizer (K : Set G)).pow_mem hz 7)
    rw [hpow7]
    exact (Subgroup.mem_centralizer_iff.mp hz7 k hk).symm
  have hnc : ∃ k ∈ K, c' * k ≠ k * c' := by
    by_contra hno
    push Not at hno
    apply H.witness.S_ne_bot
    have hcK : ∀ k ∈ K, c * k = k * c := fun k hk => by
      rw [← hzc]
      calc z * c' * k = z * (c' * k) := by group
        _ = z * (k * c') := by rw [hno k hk]
        _ = (z * k) * c' := by group
        _ = (k * z) * c' := by rw [hzK k hk]
        _ = k * (z * c') := by group
    have hS' : S ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (Commute.zpow_left (show Commute c s from hcK s (H.S_le hs)) j).eq
    have h0 : ⁅S, Subgroup.zpowers c⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hS'
    calc S = ⁅S, Subgroup.zpowers c⁆ := H.witness.S_comm
      _ = ⊥ := h0
  obtain ⟨m, hm⟩ := exists_pow_orderOf_seven hc'K hZ h7 hnc
  exact no_order_seven hT hr H.orderOf_b H.comm_b₀ (H.comm_b₁ X) (H.comm_b₂ X) hZ
    (K.pow_mem hc'K m) hm H.S_le H.witness.S_ne_bot H.witness.S_two
    ((Subgroup.normalizer (S : Set G)).pow_mem hc'S m)

end Branch

end CFSG.RankThree.PartOne.MB3
