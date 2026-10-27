module

public import CFSG.RankThree.PartOne.SEITZ5.UTorus

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2
open CFSG.RankThree.PartOne.CTP (u2 l2)

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

@[expose] def sSub (P : Frame σ n) (H : Subgroup (SUid σ n)) (hL : lSub P H = ⊤) :
    Submodule (fixSub σ) K where
  carrier := {τ | ((0 : K), τ) ∈ xTrans P H}
  add_mem' := by
    intro a b ha hb
    have := (xTrans P H).add_mem ha hb
    simpa using this
  zero_mem' := (xTrans P H).zero_mem
  smul_mem' := by
    intro c τ hτ
    by_cases hc : c = 0
    · have : c • τ = 0 := by rw [hc, zero_smul]
      change ((0 : K), c • τ) ∈ xTrans P H
      rw [this]
      exact (xTrans P H).zero_mem
    · have hm : dg c⁻¹ (inv_ne_zero hc) ∈ lSub P H := hL ▸ Subgroup.mem_top _
      have := xTrans_mul_mem hτ hm
      simp only [ent_dg_zero_zero, ent_dg_zero_one, ent_dg_one_zero, ent_dg_one_one, mul_zero,
        zero_mul, zero_add, Subfield.coe_inv, inv_inv] at this
      exact this

theorem mem_sSub {P : Frame σ n} {H : Subgroup (SUid σ n)} {hL : lSub P H = ⊤} {τ : K} :
    τ ∈ sSub P H hL ↔ ((0 : K), τ) ∈ xTrans P H := Iff.rfl

theorem fst_mem_sSub {P : Frame σ n} {H : Subgroup (SUid σ n)} (hL : lSub P H = ⊤)
    {θ : K × K} (hθ : θ ∈ xTrans P H) : θ.1 ∈ sSub P H hL := by
  have hm : u2 (1 : fixSub σ) ∈ lSub P H := hL ▸ Subgroup.mem_top _
  have h1 := xTrans_mul_mem hθ hm
  obtain ⟨h00, h01, h10, h11⟩ := ent_u2 (σ := σ) (1 : fixSub σ)
  simp only [h00, h01, h10, h11, one_mul, zero_mul, add_zero, Subfield.coe_one] at h1
  have h2 := (xTrans P H).sub_mem h1 hθ
  have h3 : ((0 : K), θ.1) = (θ.1, θ.1 + θ.2) - θ := by
    ext <;> simp
  rw [mem_sSub, h3]
  exact h2

theorem snd_mem_sSub {P : Frame σ n} {H : Subgroup (SUid σ n)} (hL : lSub P H = ⊤)
    {θ : K × K} (hθ : θ ∈ xTrans P H) : θ.2 ∈ sSub P H hL := by
  have hm : l2 (1 : fixSub σ) ∈ lSub P H := hL ▸ Subgroup.mem_top _
  have h1 := xTrans_mul_mem hθ hm
  obtain ⟨h00, h01, h10, h11⟩ := ent_l2 (σ := σ) (1 : fixSub σ)
  simp only [h00, h01, h10, h11, one_mul, zero_mul, zero_add, Subfield.coe_one] at h1
  have h2 := (xTrans P H).sub_mem h1 hθ
  have h3 : (θ.2, (0 : K)) = (θ.1 + θ.2, θ.2) - θ := by
    ext <;> simp
  rw [← h3] at h2
  exact fst_mem_sSub hL h2

theorem xTrans_eq_top {P : Frame σ n} {H : Subgroup (SUid σ n)} (hL : lSub P H = ⊤)
    (hS : sSub P H hL = ⊤) : xTrans P H = ⊤ := by
  refine eq_top_iff.2 fun θ _ => ?_
  have h2 : ((0 : K), θ.2) ∈ xTrans P H := by
    have : θ.2 ∈ sSub P H hL := hS ▸ Submodule.mem_top
    exact this
  have h1 : ((0 : K), θ.1) ∈ xTrans P H := by
    have : θ.1 ∈ sSub P H hL := hS ▸ Submodule.mem_top
    exact this
  have hm : l2 (1 : fixSub σ) ∈ lSub P H := hL ▸ Subgroup.mem_top _
  have h3 := xTrans_mul_mem h1 hm
  obtain ⟨h00, h01, h10, h11⟩ := ent_l2 (σ := σ) (1 : fixSub σ)
  simp only [h00, h01, h10, h11, one_mul, zero_add, mul_zero, Subfield.coe_one] at h3
  have h6 : (θ.1, (0 : K)) = (θ.1, θ.1) - ((0 : K), θ.1) := by ext <;> simp
  have h7 : θ = (θ.1, (0 : K)) + ((0 : K), θ.2) := by ext <;> simp
  rw [h7]
  rw [h6]
  exact (xTrans P H).add_mem ((xTrans P H).sub_mem h3 h1) h2

end CFSG.RankThree.PartOne.SEITZ5
