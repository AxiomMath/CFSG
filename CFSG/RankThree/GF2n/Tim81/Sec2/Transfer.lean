module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Basic

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.QuasithinUnique.Setup.X7

variable {X : Type*} [Group X] [Finite X] {N : Type*} [AddCommGroup N] [Module (ZMod 2) N]
  (ρ : Representation (ZMod 2) X N)

theorem exists_fixedSub_sub_mem_of_odd_index
    (N₀ : Submodule (ZMod 2) N)
    (htriv : ∀ g n, ρ g n - n ∈ N₀)
    {S : Subgroup X} (hS : Odd S.index)
    {v : N} (hv : v ∈ fixedSub ρ S) :
    ∃ u ∈ fixedSub ρ ⊤, v - u ∈ N₀ := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  let f : X ⧸ S → N :=
    Quotient.lift (s := QuotientGroup.leftRel S) (fun g : X => ρ g v) (by
      intro a b hab
      have hmem : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
      have hv' : ρ (a⁻¹ * b) v = v := (mem_fixedSub.mp hv) _ hmem
      calc ρ a v = ρ a (ρ (a⁻¹ * b) v) := by rw [hv']
        _ = ρ (a * (a⁻¹ * b)) v := by simp only [map_mul, Module.End.mul_apply]
        _ = ρ b v := by congr 1; group)
  let u : N := ∑ q : X ⧸ S, f q
  have hu : u ∈ fixedSub ρ ⊤ := by
    rw [mem_fixedSub]
    intro h _
    dsimp only [u]
    rw [map_sum]
    have hperm : ∀ q : X ⧸ S, ρ h (f q) = f (h • q) := by
      intro q
      refine QuotientGroup.induction_on q ?_
      intro g
      change ρ h (ρ g v) = ρ (h * g) v
      rw [← Module.End.mul_apply, ← map_mul]
    calc ∑ q, ρ h (f q) = ∑ q, f (h • q) :=
          Finset.sum_congr rfl fun q _ => hperm q
      _ = ∑ q, f q :=
          Fintype.sum_equiv (MulAction.toPerm h) (fun q => f (h • q)) f
            (fun q => rfl)
  have hsum : u - (S.index : ℕ) • v = ∑ q : X ⧸ S, (f q - v) := by
    dsimp only [u]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
  have hmem : u - (S.index : ℕ) • v ∈ N₀ := by
    rw [hsum]
    refine Submodule.sum_mem N₀ fun q _ => ?_
    refine QuotientGroup.induction_on q ?_
    intro g
    change ρ g v - v ∈ N₀
    exact htriv g v
  have hoddnsmul : (S.index : ℕ) • v = v := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2) (S.index) v]
    obtain ⟨k, hk⟩ := hS
    rw [hk]
    push_cast
    have h2 : (2 : ZMod 2) = 0 := rfl
    rw [h2, zero_mul, zero_add, one_smul]
  have huv : u - v ∈ N₀ := by
    have := hmem
    rwa [hoddnsmul] at this
  refine ⟨u, hu, ?_⟩
  rw [← neg_sub]
  exact N₀.neg_mem huv

theorem mem_of_odd_index_of_fixedSub_top_le
    (N₀ : Submodule (ZMod 2) N)
    (htriv : ∀ g n, ρ g n - n ∈ N₀)
    {S : Subgroup X} (hS : Odd S.index) (hfix : fixedSub ρ ⊤ ≤ N₀)
    {v : N} (hv : v ∈ fixedSub ρ S) : v ∈ N₀ := by
  obtain ⟨u, hu, hvu⟩ := exists_fixedSub_sub_mem_of_odd_index ρ N₀ htriv hS hv
  have huN : u ∈ N₀ := hfix hu
  have : u + (v - u) ∈ N₀ := N₀.add_mem huN hvu
  simpa [add_sub_cancel] using this

theorem mem_of_odd_index_of_fixedSub_top_eq_bot
    (N₀ : Submodule (ZMod 2) N)
    (htriv : ∀ g n, ρ g n - n ∈ N₀)
    {S : Subgroup X} (hS : Odd S.index) (hfix : fixedSub ρ ⊤ = ⊥)
    {v : N} (hv : v ∈ fixedSub ρ S) : v ∈ N₀ := by
  apply mem_of_odd_index_of_fixedSub_top_le ρ N₀ htriv hS _ hv
  rw [hfix]
  exact bot_le

end CFSG.RankThree.GF2n.Tim81.Sec2
