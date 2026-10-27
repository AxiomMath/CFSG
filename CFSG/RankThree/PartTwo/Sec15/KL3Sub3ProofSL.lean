module

public import CFSG.RankThree.SubgroupLists.LinearThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub3Proof

open Matrix CFSG.RankThree.SubgroupLists
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem forall_mem_iff_det_of_card {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3)
    (hS : Nat.card (H ⧸ Subgroup.center H) * Nat.gcd (Nat.card K - 1) 3 =
      Nat.card SL(3, K)) :
    ∀ g : GL (Fin 3) K, g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  classical
  set SLp := (SpecialLinearGroup.toGL : SL(3, K) →* GL (Fin 3) K).range with hSLp
  have hHle : H ≤ SLp := fun x hx => (mem_range_toGL_iff x).mpr (hdet x hx)
  set N := Nat.card SL(3, K) with hN
  have hcardSLp : Nat.card SLp = N := by
    rw [hN]
    exact (Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv).symm
  have hNpos : 0 < N := Nat.card_pos
  set d := Nat.gcd (Nat.card K - 1) 3 with hd
  have hdp : Nat.card (Subgroup.center SL(3, K)) = d := card_center_sl3
  set c := Nat.card (Subgroup.center H) with hc
  have hHcard : Nat.card H = Nat.card (H ⧸ Subgroup.center H) * c :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hHN : Nat.card H ≤ N := hcardSLp ▸ Subgroup.card_le_of_le hHle
  have hd3 : d = 1 ∨ d = 3 := (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_right _ _)
  have hc3 : c = 1 ∨ c = 3 := (Nat.dvd_prime Nat.prime_three).mp hZ
  have hfull : Nat.card H = N → ∀ g : GL (Fin 3) K,
      g ∈ H ↔ (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    intro hHN' g
    have hEq : H = SLp := Subgroup.eq_of_le_of_card_ge hHle (by rw [hcardSLp, hHN'])
    rw [hEq, mem_range_toGL_iff]
  rcases hd3 with hd1 | hd3 <;> rcases hc3 with hc1 | hc3'
  · exact hfull (by rw [hHcard, hc1, mul_one, ← hS, hd1, mul_one])
  · exfalso
    have : Nat.card H = 3 * N := by rw [hHcard, hc3', ← hS, hd1, mul_one, mul_comm]
    omega
  ·
    exfalso
    have hH3 : Nat.card H * 3 = N := by
      rw [hHcard, hc1, mul_one, ← hS, hd3]
    set W := (Subgroup.center SL(3, K)).map
      (SpecialLinearGroup.toGL : SL(3, K) →* GL (Fin 3) K) with hW
    have hWcard : Nat.card W = 3 := by
      calc Nat.card W = Nat.card (Subgroup.center SL(3, K)) :=
            (Nat.card_congr ((Subgroup.center SL(3, K)).equivMapOfInjective _
              SpecialLinearGroup.toGL_injective).toEquiv).symm
        _ = 3 := by rw [hdp, hd3]
    have hWc : ∀ w ∈ W, ∀ g : GL (Fin 3) K, g * w = w * g := by
      rintro _ ⟨z, hz, rfl⟩ g
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
      apply Units.ext
      simp only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix, ← hr]
      exact (Matrix.scalar_commute r (fun _ => Commute.all _ _) _).symm
    have hWle : W ≤ SLp := by
      rintro _ ⟨z, -, rfl⟩
      exact ⟨z, rfl⟩
    have hHW : ∀ w ∈ W, w ∈ H → w = 1 := by
      intro w hw hwH
      have hz : (⟨w, hwH⟩ : H) ∈ Subgroup.center H := by
        rw [Subgroup.mem_center_iff]
        intro h
        exact Subtype.ext (hWc w hw h)
      have : Subgroup.center H = ⊥ := by
        rw [← Subgroup.card_eq_one, ← hc, hc1]
      rw [this, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz
    let μ : H × W → SLp := fun hw => ⟨hw.1 * hw.2, SLp.mul_mem (hHle hw.1.2) (hWle hw.2.2)⟩
    have hμ : Function.Injective μ := by
      rintro ⟨h₁, w₁⟩ ⟨h₂, w₂⟩ heq
      have heq' : (h₁ : GL (Fin 3) K) * w₁ = h₂ * w₂ := congrArg Subtype.val heq
      have hx : (h₂ : GL (Fin 3) K)⁻¹ * h₁ = w₂ * (w₁ : GL (Fin 3) K)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← heq', mul_inv_cancel_right]
      have h1 : (h₂ : GL (Fin 3) K)⁻¹ * h₁ = 1 :=
        hHW _ (by rw [hx]; exact W.mul_mem w₂.2 (W.inv_mem w₁.2))
          (H.mul_mem (H.inv_mem h₂.2) h₁.2)
      have hh : h₁ = h₂ := Subtype.ext (by rw [inv_mul_eq_one] at h1; exact h1.symm)
      subst hh
      have hw : w₁ = w₂ := Subtype.ext (mul_left_cancel heq')
      rw [hw]
    have hμs : Function.Surjective μ := by
      have : Finite (H × W) := inferInstance
      have hcard : Nat.card (H × W) = Nat.card SLp := by
        rw [Nat.card_prod, hWcard, hH3, hcardSLp]
      exact (Function.Injective.bijective_of_nat_card_le hμ hcard.ge).2
    have hcommH : ⁅SLp, SLp⁆ ≤ H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨⟨h₁, w₁⟩, hμ1⟩ := hμs ⟨a, ha⟩
      obtain ⟨⟨h₂, w₂⟩, hμ2⟩ := hμs ⟨b, hb⟩
      have ha' : a = h₁ * w₁ := (congrArg Subtype.val hμ1).symm
      have hb' : b = h₂ * w₂ := (congrArg Subtype.val hμ2).symm
      have hcomm : ⁅a, b⁆ = ⁅(h₁ : GL (Fin 3) K), (h₂ : GL (Fin 3) K)⁆ := by
        rw [ha', hb']
        exact commutatorElement_mul_mul_of_central (hWc w₁ w₁.2) (hWc w₂ w₂.2)
      rw [hcomm, commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem h₁.2 h₂.2) (H.inv_mem h₁.2)) (H.inv_mem h₂.2)
    have hperf : Group.IsPerfect SL(3, K) :=
      CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect le_rfl
    have hSLperf : ⁅SLp, SLp⁆ = SLp := by
      rw [hSLp, MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
        hperf.commutator_eq_top]
    have hle : SLp ≤ H := hSLperf.ge.trans hcommH
    have := Subgroup.card_le_of_le hle
    omega
  · exact hfull (by rw [hHcard, hc3', ← hS, hd3])

end KL3Sub3Proof

end CFSG.RankThree.PartTwo.Sec15
