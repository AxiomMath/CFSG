module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16t3_le_sup_of_sylow {M₀ : Type*} [Group M₀] [Finite M₀]
    {H N₀ L₀ P : Subgroup M₀} (hN₀H : N₀ ≤ H) (hN₀ : (N₀.subgroupOf H).Normal)
    (hL₀ : L₀ ≤ N₀)
    (hthirds : ∀ a b c : M₀, a ∈ N₀ → b ∈ N₀ → c ∈ N₀ →
      a⁻¹ * b ∈ L₀ ∨ a⁻¹ * c ∈ L₀ ∨ b⁻¹ * c ∈ L₀)
    (hP : IsSylowIn 2 P H) :
    N₀ ≤ L₀ ⊔ P := by
  have hL₀' : L₀.subgroupOf N₀ = ⊤ ∨ (L₀.subgroupOf N₀).index = 2 := by
    refine s16t3_index_eq_two_of_thirds (L₀.subgroupOf N₀) ?_
    intro x y z
    have h := hthirds x.1 y.1 z.1 x.2 y.2 z.2
    simpa [Subgroup.mem_subgroupOf] using h
  have hnorm : (L₀.subgroupOf N₀).Normal := by
    rcases hL₀' with h | h
    · rw [h]; exact Subgroup.normal_top
    · exact Subgroup.normal_of_index_eq_two h
  have hPinf : IsSylowIn 2 (P ⊓ N₀) N₀ := hP.inf_normal hN₀H hN₀
  have hq : ∀ x ∈ N₀, ∃ k : ℕ, x ^ 2 ^ k ∈ L₀ := by
    intro x hx
    rcases hL₀' with h | h
    · refine ⟨0, ?_⟩
      have hx' : (⟨x, hx⟩ : ↥N₀) ∈ L₀.subgroupOf N₀ := by
        rw [h]; exact Subgroup.mem_top _
      simpa [Subgroup.mem_subgroupOf] using hx'
    · refine ⟨1, ?_⟩
      have hx' : (⟨x, hx⟩ : ↥N₀) ^ 2 ∈ L₀.subgroupOf N₀ :=
        Subgroup.sq_mem_of_index_two h _
      simpa [Subgroup.mem_subgroupOf, pow_one] using hx'
  intro x hx
  obtain ⟨s, hs, n, hn, hxsn⟩ := exists_mul_eq_of_pow_mem hnorm hq hPinf x hx
  rw [hxsn]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hs.1) (Subgroup.mem_sup_left hn)

theorem s16t3_card_subgroupOf {A : Type*} [Group A] {X Y : Subgroup A} (h : X ≤ Y) :
    Nat.card ↥(X.subgroupOf Y) = Nat.card ↥X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem s16t3_le_sup_of_sup_eq {A : Type*} [Group A] {M N L K T : Subgroup A}
    (hNK : N ⊔ K = M) (hN : N ≤ L ⊔ T) : M ≤ (L ⊔ K) ⊔ T := by
  rw [← hNK]
  calc N ⊔ K ≤ (L ⊔ T) ⊔ K := sup_le_sup_right hN _
    _ = (L ⊔ K) ⊔ T := by rw [sup_assoc, sup_comm T K, ← sup_assoc]

theorem s16t3_inf_inf_eq_of_inf_eq {A : Type*} [Lattice A] {N S C R : A}
    (hNS : N ≤ S) (hC : N ⊓ C = R) : N ⊓ (S ⊓ C) = R := by
  rw [← inf_assoc, inf_eq_left.mpr hNS, hC]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
