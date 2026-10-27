module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBinary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.PartOne.Quotient36
open scoped IsMulCommutative

theorem smallExtraspecialOddActionRecognition_of (h32 : ExtraspecialThirtyTwoFiveRecognition) :
    SmallExtraspecialOddActionRecognition := by
  intro p n A S _ _ _ _ _ _ hp hp3 hS hn1 hn3 hcard hirr
  classical
  have hS2 : IsPGroup 2 S := hS.1
  obtain ⟨d, hVd, -, h6, hcyc, hcardr, hker, hkercard⟩ := binary_action_data hp hp3 hS2 hirr
  have hΦcard : Nat.card (frattini S) = 2 := by
    rw [hS.2.2.1]
    exact hS.2.2.2
  have hV : Nat.card (S ⧸ frattini S) = 2 ^ (2 * n) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini S)
    rw [hΦcard, hcard] at h1
    have h2 : 2 ^ (2 * n) * 2 = Nat.card (S ⧸ frattini S) * 2 := by
      rw [← h1]
      ring
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h2).symm
  have hdn : d = 2 * n := Nat.pow_right_injective (le_refl 2) (hVd.symm.trans hV)
  have h5 : p = 5 ∧ d = 4 := h6 ⟨n, by omega⟩ (by omega)
  have hn2 : n = 2 := by omega
  refine ⟨h5.1, hn2, ?_, hcyc, hcardr.trans h5.1, hker, hkercard⟩
  have hS32 : Nat.card S = 32 := by rw [hcard, hn2]; norm_num
  obtain ⟨hnt, hirr'⟩ := hirr
  obtain ⟨a₀, v₀, hav₀⟩ := hnt
  let α : MulAut S := MulDistribMulAction.toMulAut A S a₀
  have hαs : ∀ s : S, α s = a₀ • s := fun s => rfl
  have hα1 : α ≠ 1 := by
    intro h
    apply hav₀
    refine (hker a₀).mp (fun s => ?_) v₀
    rw [← hαs, h]
    rfl
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hα5 : orderOf α = 5 := by
    have h1 : (⟨α, a₀, rfl⟩ : (MulDistribMulAction.toMulAut A S).range) ^ 5 = 1 := by
      have := pow_card_eq_one' (x := (⟨α, a₀, rfl⟩ : (MulDistribMulAction.toMulAut A S).range))
      rwa [hcardr.trans h5.1] at this
    exact orderOf_eq_prime (congrArg Subtype.val h1) hα1
  let F : Subgroup (S ⧸ frattini S) :=
    { carrier := {v | (letI := frattiniQuotientAction A S; a₀ • v = v)}
      mul_mem' := fun {x y} hx hy => by
        let _ := frattiniQuotientAction A S
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [smul_mul', hx, hy]
      one_mem' := by
        let _ := frattiniQuotientAction A S
        exact smul_one a₀
      inv_mem' := fun {x} hx => by
        let _ := frattiniQuotientAction A S
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [smul_inv', hx] }
  have hFinv : letI := frattiniQuotientAction A S
      ∀ b : A, ∀ v ∈ F, b • v ∈ F := by
    let _ := frattiniQuotientAction A S
    intro b v hv
    change a₀ • (b • v) = b • v
    have hv' : a₀ • v = v := hv
    have hcomm : a₀ * b = b * a₀ := IsMulCommutative.is_comm.comm a₀ b
    calc a₀ • (b • v) = (a₀ * b) • v := (mul_smul a₀ b v).symm
      _ = (b * a₀) • v := by rw [hcomm]
      _ = b • (a₀ • v) := mul_smul b a₀ v
      _ = b • v := by rw [hv']
  have hFbot : F = ⊥ := by
    rcases hirr' F hFinv with h | h
    · exact h
    · exfalso
      apply hav₀
      have : v₀ ∈ F := by rw [h]; exact Subgroup.mem_top _
      exact this
  have hfix : ∀ x : S, α x * x⁻¹ ∈ Subgroup.center S → x ∈ Subgroup.center S := by
    intro x hx
    have hx' : (a₀ • x) * x⁻¹ ∈ frattini S := by rw [hS.2.2.1]; exact hx
    have h1 : ((a₀ • x : S) : S ⧸ frattini S) = (x : S ⧸ frattini S) := by
      rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
      exact hx'
    have h2 : (x : S ⧸ frattini S) ∈ F := h1
    rw [hFbot, Subgroup.mem_bot] at h2
    rw [← hS.2.2.1]
    exact (QuotientGroup.eq_one_iff x).mp h2
  exact h32 S hS hS32 α hα5 hfix

end CFSG.RankThree.PartOne
