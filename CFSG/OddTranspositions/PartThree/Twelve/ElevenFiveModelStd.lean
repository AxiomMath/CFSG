module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveChart
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveAdjoin
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm
import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModelHyp

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge Matrix

private lemma FiveAdjoin.a_ne_zero {k : ℕ} {ε π : Bool} (A : FiveAdjoin k ε π) : A.a ≠ 0 :=
  fun h => A.sign_a.1 (by rw [h]; simp [fiveForm])

theorem FiveAdjoin.exists_j_eq {k : ℕ} {ε π : Bool} (A : FiveAdjoin k ε π)
    {w : Fin (k + 2) → ZMod 5} (hw : fiveForm (k + 1) (ε == π) w A.a = 0) : ∃ x, A.j x = w := by
  have hane : A.a ≠ 0 := FiveAdjoin.a_ne_zero A
  have hdim : Module.finrank (ZMod 5) ↥(LinearMap.range A.j) = k + 1 := by
    rw [LinearMap.finrank_range_of_inj A.inj, Module.finrank_fin_fun]
  have hle : LinearMap.range A.j ≤
      fiveOrth (k + 1) (ε == π) (Submodule.span (ZMod 5) {A.a}) := by
    rintro y ⟨x, rfl⟩
    rw [mem_fiveOrth]
    intro u hu
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [fiveForm_smul_right, A.perp x, mul_zero]
  have horth : Module.finrank (ZMod 5)
      ↥(fiveOrth (k + 1) (ε == π) (Submodule.span (ZMod 5) {A.a})) = k + 1 := by
    have h := finrank_inf_fiveOrth_add (k := k + 1) (ε := (ε == π))
      (W := ⊤) (U := Submodule.span (ZMod 5) {A.a})
      (isFiveNondeg_top (k + 1) (ε == π)) le_top
    rw [top_inf_eq, finrank_span_singleton hane, finrank_top, Module.finrank_fin_fun] at h
    omega
  have heq : LinearMap.range A.j =
      fiveOrth (k + 1) (ε == π) (Submodule.span (ZMod 5) {A.a}) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, horth])
  have hmem : w ∈ fiveOrth (k + 1) (ε == π) (Submodule.span (ZMod 5) {A.a}) := by
    rw [mem_fiveOrth]
    intro u hu
    obtain ⟨μ, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [fiveForm_smul_right, hw, mul_zero]
  rw [← heq] at hmem
  exact hmem

private lemma fiveReflection_eq_or_eq_neg {k : ℕ} (hk : 4 ≤ k) {ε π : Bool}
    {g r : fiveReflectionGroup (k + 1) (ε == π) π}
    (h : (QuotientGroup.mk g : fiveProjective (k + 1) (ε == π) π) = QuotientGroup.mk r) :
    (g : GL (Fin (k + 2)) (ZMod 5)) = (r : GL (Fin (k + 2)) (ZMod 5)) ∨
      (r : GL (Fin (k + 2)) (ZMod 5)) = -(g : GL (Fin (k + 2)) (ZMod 5)) := by
  have hmem : g⁻¹ * r ∈ Subgroup.center (fiveReflectionGroup (k + 1) (ε == π) π) := by
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h]
    exact inv_mul_cancel _
  rcases (mem_center_fiveReflectionGroup_iff (by omega : 4 ≤ k + 1) (ε == π) π
    (g⁻¹ * r)).mp hmem with h1 | hneg
  · left
    have h' : ((g⁻¹ * r : fiveReflectionGroup (k + 1) (ε == π) π) :
        GL (Fin (k + 2)) (ZMod 5)) = 1 := h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h'
    rw [← mul_one (g : GL (Fin (k + 2)) (ZMod 5)), ← h', ← mul_assoc, mul_inv_cancel, one_mul]
  · right
    have h' : ((g : GL (Fin (k + 2)) (ZMod 5))⁻¹) * (r : GL (Fin (k + 2)) (ZMod 5)) = -1 := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hneg
    calc (r : GL (Fin (k + 2)) (ZMod 5))
        = (g : GL (Fin (k + 2)) (ZMod 5)) * ((g : GL (Fin (k + 2)) (ZMod 5))⁻¹ *
            (r : GL (Fin (k + 2)) (ZMod 5))) := by group
      _ = (g : GL (Fin (k + 2)) (ZMod 5)) * (-1) := by rw [h']
      _ = -(g : GL (Fin (k + 2)) (ZMod 5)) := by
          apply Units.ext
          simp [mul_neg]

private lemma fiveReflection_ne_neg_of_apply_eq {k : ℕ} {ε π : Bool} {A : FiveAdjoin k ε π}
    {ra : fiveReflectionGroup (k + 1) (ε == π) π}
    (hra' : (ra : GL (Fin (k + 2)) (ZMod 5)) = fiveReflOf (k + 1) (ε == π) A.a)
    {g r : fiveReflectionGroup (k + 1) (ε == π) π}
    (hg_a : ((g : GL (Fin (k + 2)) (ZMod 5)) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a = A.a)
    (hrref : (r : GL (Fin (k + 2)) (ZMod 5)) ∈ fiveReflections (k + 1) (ε == π) π)
    (hne : (QuotientGroup.mk r : fiveProjective (k + 1) (ε == π) π) ≠ QuotientGroup.mk ra) :
    (r : GL (Fin (k + 2)) (ZMod 5)) ≠ -(g : GL (Fin (k + 2)) (ZMod 5)) := by
  intro hgr
  obtain ⟨u, -, -, hr_u⟩ := exists_eq_fiveReflOf hrref
  have hane : A.a ≠ 0 := FiveAdjoin.a_ne_zero A
  have hr_a2 : ((r : GL (Fin (k + 2)) (ZMod 5)) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a =
      A.a - (2 * fiveForm (k + 1) (ε == π) A.a u *
        (fiveForm (k + 1) (ε == π) u u)⁻¹) • u := by
    rw [hr_u, fiveReflOf_mulVec]
  have hr_a : ((r : GL (Fin (k + 2)) (ZMod 5)) :
      Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a = -A.a := by
    rw [hgr, Units.val_neg, Matrix.neg_mulVec, hg_a]
  have haμ : A.a = ((2 : ZMod 5)⁻¹ * (2 * fiveForm (k + 1) (ε == π) A.a u *
      (fiveForm (k + 1) (ε == π) u u)⁻¹)) • u := by
    have htwo : (2 : ZMod 5) • A.a = (2 * fiveForm (k + 1) (ε == π) A.a u *
        (fiveForm (k + 1) (ε == π) u u)⁻¹) • u := by
      linear_combination (norm := module) (hr_a2.symm.trans hr_a)
    rw [← smul_smul, ← htwo, smul_smul, inv_mul_cancel₀ (by decide : (2 : ZMod 5) ≠ 0),
      one_smul]
  have hμ0 : (2 : ZMod 5)⁻¹ * (2 * fiveForm (k + 1) (ε == π) A.a u *
      (fiveForm (k + 1) (ε == π) u u)⁻¹) ≠ 0 := by
    intro h
    exact hane (by rw [haμ, h, zero_smul])
  have hra_r : ra = r := by
    apply Subtype.ext
    rw [hra', hr_u, haμ]
    exact fiveReflOf_smul (k + 1) (ε == π) u hμ0
  exact hne (by rw [hra_r])

theorem FiveHyperplaneData.of_fiveAdjoin {k : ℕ} (hk : 4 ≤ k) {ε π : Bool} (A : FiveAdjoin k ε π)
    {ra : fiveReflectionGroup (k + 1) (ε == π) π}
    (hra : ∀ x, ((ra : GL (Fin (k + 2)) (ZMod 5)) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ x =
      x - (2 * fiveForm (k + 1) (ε == π) x A.a * (fiveForm (k + 1) (ε == π) A.a A.a)⁻¹) • A.a)
    (c : FiveLocalModel (fiveProjClass (k + 1) (ε == π) π)
      (QuotientGroup.mk ra : fiveProjective (k + 1) (ε == π) π) k ε π)
    (hc : ∀ y : Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk ra : fiveProjective (k + 1) (ε == π) π)),
      (y : fiveProjective (k + 1) (ε == π) π) ∈
          commSet (fiveProjClass (k + 1) (ε == π) π) (QuotientGroup.mk ra) →
        ∃ g : fiveReflectionGroup (k + 1) (ε == π) π,
          (QuotientGroup.mk g : fiveProjective (k + 1) (ε == π) π) = y ∧
          ((g : GL (Fin (k + 2)) (ZMod 5)) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ A.a =
            A.a ∧
          ∀ x, ((g : GL (Fin (k + 2)) (ZMod 5)) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ
              A.j x =
            A.j (((c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)) :
    FiveHyperplaneData c := by
  intro s hs hsa
  have hk' : 4 ≤ k + 1 := by omega
  have hra' : (ra : GL (Fin (k + 2)) (ZMod 5)) = fiveReflOf (k + 1) (ε == π) A.a := by
    apply Units.ext
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [hra, fiveReflOf_mulVec]
  obtain ⟨w, hw0, hwa, hsign, hcomm⟩ :=
    exists_hyperplane_vector_proj (k := k + 1) hk' (ε := (ε == π)) (π := π) (a := A.a)
      A.sign_a.2 (ra := ra) hra' hs hsa
  obtain ⟨z, hz⟩ := FiveAdjoin.exists_j_eq A hwa
  have hz0 : z ≠ 0 := by
    intro h
    apply hw0
    rw [← hz, h, LinearMap.map_zero]
  have hQz : fiveForm k ε z z = fiveForm (k + 1) (ε == π) w w := by
    rw [← hz]
    exact (A.isom z z).symm
  refine ⟨z, hz0, ?_, ?_⟩
  · simpa only [hQz] using hsign
  · intro y hyD
    obtain ⟨g, hg_eq, hg_a, hg_j⟩ := hc y hyD
    obtain ⟨hycls, hycomm, hyne⟩ := hyD
    obtain ⟨r, hrref, hr_eq⟩ := hycls
    have hcommr : Commute (QuotientGroup.mk r : fiveProjective (k + 1) (ε == π) π) s ↔
        ((r : GL (Fin (k + 2)) (ZMod 5)) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ w =
          w :=
      hcomm r hrref (by rw [hr_eq]; exact hycomm) (by rw [hr_eq]; exact hyne)
    have hgJ : ((g : GL (Fin (k + 2)) (ZMod 5)) : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ w =
        A.j (((c.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ z) := by
      rw [← hz]
      exact hg_j z
    rcases fiveReflection_eq_or_eq_neg hk (hg_eq.trans hr_eq.symm) with hgr | hgr
    · rw [← hr_eq, hcommr, ← hgr, hgJ, ← hz]
      exact ⟨fun h => A.inj h, fun h => by rw [h]⟩
    · exact (fiveReflection_ne_neg_of_apply_eq hra' hg_a hrref
        (by rw [hr_eq]; exact hyne) hgr).elim

end CFSG.OddTranspositions.PartThree

end
