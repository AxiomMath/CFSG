module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofNine
public import CFSG.RankThree.PartTwo.Sec21.Item224Res5ProofDefs
public import CFSG.RankThree.PartTwo.KFacts.K71Sp48Class

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof
open CFSG.GH74.GLS.IVK (fixedField)

theorem exists_commuting_three_sp4 {K : Type} [Field K] [Finite K] [CharP K 2]
    (y : StatedSp 2 K) (hy : orderOf y = 3) :
    ∃ z : StatedSp 2 K, orderOf z = 3 ∧ z * y = y * z ∧ z ∉ Subgroup.zpowers y := by
  have hy3 : y ^ 3 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    norm_num at hy
  have key : ∀ g a b : StatedSp 2 K, orderOf b = 3 → b * a = a * b →
      b ∉ Subgroup.zpowers a → y = g * a * g⁻¹ →
      ∃ z : StatedSp 2 K, orderOf z = 3 ∧ z * y = y * z ∧ z ∉ Subgroup.zpowers y := by
    intro g a b hb hba hbn hya
    have hya' : y = MulAut.conj g a := hya
    refine ⟨MulAut.conj g b, ?_, ?_, ?_⟩
    · rw [MulEquiv.orderOf_eq, hb]
    · rw [hya', ← map_mul, ← map_mul, hba]
    · rw [hya']
      intro hmem
      apply hbn
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [← map_zpow] at hi
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, (MulAut.conj g).injective hi⟩
  have hTord : orderOf (sp4T K) = 3 := orderOf_eq_prime (sp4T_pow_three K) (sp4T_ne_one K)
  have hT'1 : sp4T' K ≠ 1 := fun h1 => sp4T'_not_mem_zpowers K (h1 ▸ one_mem _)
  have hT'ord : orderOf (sp4T' K) = 3 := orderOf_eq_prime (sp4T'_pow_three K) hT'1
  by_cases hN : ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 2 +
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) + 1 = 0
  · obtain ⟨g, hg⟩ := exists_conj_eq_sp4TT hy3 hy1 hN
    refine key g (sp4TT K) (sp4T K) hTord ?_ ?_ hg
    · change sp4T K * (sp4T K * sp4T' K) = sp4T K * sp4T' K * sp4T K
      rw [mul_assoc, sp4T_commute K]
    · exact not_mem_zpowers_mul (sp4T_commute K) hTord (sp4T'_pow_three K)
        (sp4T'_not_mem_zpowers K)
  · obtain ⟨g, hg⟩ := exists_conj_eq_sp4T hy3 hy1 hN
    exact key g (sp4T K) (sp4T' K) hT'ord (sp4T_commute K).symm (sp4T'_not_mem_zpowers K) hg

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem conj_injective_sp4 :
    Function.Injective (MulAut.conj : StatedProj (StatedSp 2 F) →*
      MulAut (StatedProj (StatedSp 2 F))) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
  have hcen : g ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h1 : proj 2 F g * proj 2 F h * (proj 2 F g)⁻¹ = proj 2 F h := by
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ (proj 2 F h)) hx
      simpa [MulAut.conj_apply] using this
    apply proj_injective_of_charTwo
    rw [map_mul, map_mul]
    calc proj 2 F h * proj 2 F g = proj 2 F g * proj 2 F h * (proj 2 F g)⁻¹ * proj 2 F g := by
          rw [h1]
      _ = proj 2 F g * proj 2 F h := by group
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hcen
  have h2 : g ∈ spScalars 2 F := hcen
  rw [spScalars_eq_bot, Subgroup.mem_bot] at h2
  rw [h2, map_one, Subgroup.mem_bot]

theorem le_inner_of_innerThreeFixed_sp4 {E : Subgroup (MulAut (StatedProj (StatedSp 2 F)))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hI : InnerThreeFixed (StatedProj (StatedSp 2 F)) E)
    (hx : ∃ x : StatedProj (StatedSp 2 F), orderOf x = 3 ∧
      x ∉ Subgroup.center (StatedProj (StatedSp 2 F)) ∧ ∀ e ∈ E, e x = x) :
    E ≤ (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range := by
  classical
  have hcinj := conj_injective_sp4 (F := F)
  obtain ⟨x₀, hx₀3, -, hx₀E⟩ := hx
  have hcx₀E : MulAut.conj x₀ ∈ E := hI x₀ hx₀3 hx₀E
  have hcx₀ord : orderOf (MulAut.conj x₀) = 3 := by rw [orderOf_injective _ hcinj, hx₀3]
  intro e he
  by_contra hein
  have he3 : e ^ 3 = 1 := hE.2 e he
  have hD : e ∉ (conjAut 2 F).range := by
    rintro ⟨A, rfl⟩
    exact hein (conjAut_mem_inner_of_charTwo A)
  obtain ⟨σ, hσ3, H, hH⟩ := sp4_even_order_three_field_descent e he3 hD
  set cH := conjAut 2 F H with hcH
  set fσ := fieldAut 2 F σ with hfσ
  have hx'fix : fσ (cH⁻¹ x₀) = cH⁻¹ x₀ := by
    have h1 : fσ = cH⁻¹ * e * cH := by rw [hH]; group
    rw [h1]
    change cH⁻¹ (e (cH (cH⁻¹ x₀))) = cH⁻¹ x₀
    rw [MulAut.apply_inv_self, hx₀E e he]
  obtain ⟨y, hy⟩ := (mem_range_proj_spIncl_iff σ (cH⁻¹ x₀)).mpr hx'fix
  set j := (proj 2 F).comp (spIncl σ) with hj
  have hjinj : Function.Injective j := proj_spIncl_injective σ
  have hjfix : ∀ w, fσ (j w) = j w := fun w =>
    (mem_range_proj_spIncl_iff σ (j w)).mp ⟨w, rfl⟩
  have hy3 : orderOf y = 3 := by
    rw [← orderOf_injective j hjinj y, hy, MulEquiv.orderOf_eq, hx₀3]
  obtain ⟨z₀, hz₀3, hz₀c, hz₀n⟩ := exists_commuting_three_sp4 y hy3
  obtain ⟨z, hz⟩ : ∃ z : StatedProj (StatedSp 2 F), z = cH (j z₀) := ⟨_, rfl⟩
  have he' : e = cH * fσ * cH⁻¹ := hH
  have hez : e z = z := by
    rw [he', hz]
    change cH (fσ (cH⁻¹ (cH (j z₀)))) = cH (j z₀)
    rw [MulAut.inv_apply_self, hjfix]
  have hx₀' : x₀ = cH (j y) := by rw [hy, MulAut.apply_inv_self]
  have hyz : y * z₀ * y⁻¹ = z₀ := by rw [← hz₀c, mul_inv_cancel_right]
  have hcz : MulAut.conj x₀ z = z := by
    rw [MulAut.conj_apply, hx₀', hz]
    calc cH (j y) * cH (j z₀) * (cH (j y))⁻¹ = cH (j (y * z₀ * y⁻¹)) := by
          simp only [map_mul, map_inv]
      _ = cH (j z₀) := by rw [hyz]
  have hS : E ⊓ MulAction.stabilizer (MulAut (StatedProj (StatedSp 2 F))) z = E := by
    refine eq_of_card_nine hE9 inf_le_left (a := MulAut.conj x₀) (b := e)
      (Subgroup.mem_inf.mpr ⟨hcx₀E, ?_⟩) hcx₀ord (Subgroup.mem_inf.mpr ⟨he, ?_⟩) ?_
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hcz
    · rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hez
    · intro hmem
      have hle : Subgroup.zpowers (MulAut.conj x₀) ≤
          (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))).range :=
        Subgroup.zpowers_le.mpr ⟨x₀, rfl⟩
      exact hein (hle hmem)
  have hfixE : ∀ g ∈ E, g z = z := by
    intro g hg
    have h1 : g ∈ E ⊓ MulAction.stabilizer (MulAut (StatedProj (StatedSp 2 F))) z := by
      rw [hS]
      exact hg
    have h2 := (Subgroup.mem_inf.mp h1).2
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h2
  have hz3 : orderOf z = 3 := by
    rw [hz, MulEquiv.orderOf_eq, orderOf_injective j hjinj, hz₀3]
  have hczE : MulAut.conj z ∈ E := hI z hz3 hfixE
  have hczmem : MulAut.conj z ∈ Subgroup.zpowers (MulAut.conj x₀) := by
    by_contra hnot
    have hEI : E ⊓ (MulAut.conj : StatedProj (StatedSp 2 F) →*
        MulAut (StatedProj (StatedSp 2 F))).range = E :=
      eq_of_card_nine hE9 inf_le_left (Subgroup.mem_inf.mpr ⟨hcx₀E, ⟨x₀, rfl⟩⟩) hcx₀ord
        (Subgroup.mem_inf.mpr ⟨hczE, ⟨z, rfl⟩⟩) hnot
    apply hein
    have h1 : e ∈ E ⊓ (MulAut.conj : StatedProj (StatedSp 2 F) →*
        MulAut (StatedProj (StatedSp 2 F))).range := by
      rw [hEI]
      exact he
    exact (Subgroup.mem_inf.mp h1).2
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hczmem
  rw [← map_zpow] at hi
  have hzx : x₀ ^ i = z := hcinj hi
  apply hz₀n
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  apply hjinj
  apply cH.injective
  rw [map_zpow, map_zpow, ← hx₀', hzx, hz]

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
