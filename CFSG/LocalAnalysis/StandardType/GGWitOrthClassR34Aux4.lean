module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Aux2
public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Aux3
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTransport

public section

namespace CFSG.StandardType.ZS

open Subgroup

abbrev owR34_QQ (w : Fin 4 → ZMod 3) : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) :=
  @QuadraticMap.weightedSumSquares (ZMod 3) (ZMod 3) _ (Fin 4) _ _ _ _ w

abbrev owR34_W (w : Fin 4 → ZMod 3) : Prop :=
  @LinWeyl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))
    (@Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
      (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ w) 1))

theorem owR34_QQ_apply_smul (w : Fin 4 → ZMod 3) (c : ZMod 3) (v : Fin 4 → ZMod 3) :
    owR34_QQ (c⁻¹ • w) v = c⁻¹ * owR34_QQ w v := by
  simp only [owR34_QQ, QuadraticMap.weightedSumSquares_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem owR34_classRefl_smul_gen {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (c u : ZMod 3) (hu : u ≠ 0) :
    ClassRefl 3 Q c = ClassRefl 3 (u • Q) (u * c) := by
  ext t
  simp only [ClassRefl, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hr, hiso, a, ha, hta⟩
    refine ⟨hr, ?_, a, ?_, hta⟩
    · intro v
      show (u • Q) (t v) = (u • Q) v
      simp only [QuadraticMap.smul_apply, smul_eq_mul]
      rw [hiso v]
    · show (u • Q) a = u * c
      rw [QuadraticMap.smul_apply, ha]
      rfl
  · rintro ⟨hr, hiso, a, ha, hta⟩
    refine ⟨hr, ?_, a, ?_, hta⟩
    · intro v
      have h := hiso v
      simp only [QuadraticMap.smul_apply, smul_eq_mul] at h
      exact mul_left_cancel₀ hu h
    · have h := ha
      simp only [QuadraticMap.smul_apply, smul_eq_mul] at h
      exact mul_left_cancel₀ hu h

theorem owR34_classRefl_smul (w : Fin 4 → ZMod 3) (c : ZMod 3) (hc : c ≠ 0) :
    @ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ (c⁻¹ • w)) 1 =
    @ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ w) c := by
  have hu : c⁻¹ ≠ 0 := by
    have h : ∀ c : ZMod 3, c ≠ 0 → c⁻¹ ≠ 0 := by decide +kernel
    exact h c hc
  have hcinv : c⁻¹ * c = 1 := by
    have h : ∀ c : ZMod 3, c ≠ 0 → c⁻¹ * c = 1 := by decide +kernel
    exact h c hc
  have hQ : owR34_QQ (c⁻¹ • w) = c⁻¹ • owR34_QQ w := by
    ext v
    rw [owR34_QQ_apply_smul]
    rfl
  rw [hQ]
  have h := @owR34_classRefl_smul_gen (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ w) c c⁻¹ hu
  rw [hcinv] at h
  exact h.symm

theorem owR34_linWeyl_of_iso (v canon : Fin 4 → ZMod 3)
    (e : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    (he : ∀ x, owR34_QQ canon (e x) = owR34_QQ v x) (h : owR34_W canon) : owR34_W v := by
  let A := @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
    (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ v) 1)
  let A' := @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
    (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ canon) 1)
  have hA : A = @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
      (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ v) 1) := rfl
  have hA' : A' = @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)))
      (@ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_QQ canon) 1) := rfl
  obtain ⟨φ, hφ⟩ := @wit_classRefl_transport 3 (by norm_num) (by decide)
    (Fin 4 → ZMod 3) (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))
    (owR34_QQ v) (owR34_QQ canon) e he 1 A A' hA hA'
  exact @wit_linWeyl_transport 3 (Fin 4 → ZMod 3) (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) e A A' φ hφ h

noncomputable def owR34_e_1_1_1_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 0, 1, 0; 2, 0, 0, 0; 0, 0, 0, 2; 0, 1, 0, 0]) (M' := !![0, 2, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 2, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_1_1_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 1, 0, 1; 0, 0, 2, 0; 2, 2, 0, 1; 2, 1, 0, 0]) (M' := !![1, 0, 2, 1; 1, 0, 2, 2; 0, 2, 0, 0; 2, 0, 2, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_1_2_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 0, 1, 2; 0, 2, 2, 1; 1, 1, 1, 1; 2, 2, 0, 1]) (M' := !![1, 0, 2, 2; 0, 2, 2, 2; 1, 2, 2, 0; 1, 2, 1, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_1_2_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![2, 2, 1, 1; 1, 2, 1, 2; 0, 1, 1, 0; 1, 0, 0, 1]) (M' := !![2, 1, 0, 2; 2, 2, 2, 0; 1, 1, 2, 0; 1, 2, 0, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_2_1_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 2, 1, 2; 0, 1, 1, 0; 0, 1, 2, 2; 2, 0, 0, 0]) (M' := !![0, 0, 0, 2; 2, 2, 1, 0; 1, 2, 2, 0; 1, 0, 1, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_2_1_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 0, 0, 2; 1, 0, 1, 0; 0, 2, 0, 0; 2, 0, 1, 0]) (M' := !![0, 2, 0, 1; 0, 0, 2, 0; 0, 2, 0, 2; 2, 0, 0, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_2_2_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 0, 2, 0; 0, 2, 0, 2; 0, 2, 0, 1; 2, 0, 0, 0]) (M' := !![0, 0, 0, 2; 0, 1, 1, 0; 2, 0, 0, 0; 0, 1, 2, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_1_2_2_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 1, 0, 1; 1, 2, 0, 0; 1, 1, 1, 2; 1, 1, 2, 2]) (M' := !![1, 2, 2, 2; 1, 1, 2, 2; 0, 0, 2, 1; 2, 0, 2, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_1_1_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![2, 2, 2, 2; 1, 1, 0, 2; 1, 0, 1, 2; 0, 1, 1, 2]) (M' := !![1, 1, 1, 0; 1, 1, 0, 1; 1, 0, 1, 1; 2, 1, 1, 1])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_1_1_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 2, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 1, 0]) (M' := !![0, 0, 1, 0; 1, 0, 0, 2; 2, 0, 0, 2; 0, 1, 0, 0])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_1_2_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![2, 0, 0, 1; 2, 2, 1, 2; 0, 2, 2, 0; 1, 2, 1, 1]) (M' := !![1, 2, 0, 1; 0, 2, 1, 2; 0, 1, 1, 1; 2, 2, 0, 1])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_1_2_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 0, 1, 0; 2, 0, 1, 2; 1, 2, 2, 2; 1, 1, 2, 2]) (M' := !![2, 2, 2, 2; 0, 0, 1, 2; 2, 1, 1, 1; 0, 1, 2, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_2_1_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 1, 0, 0; 0, 0, 1, 2; 1, 2, 1, 1; 1, 2, 2, 2]) (M' := !![2, 0, 1, 1; 2, 0, 2, 2; 0, 2, 1, 2; 0, 1, 1, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_2_1_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![1, 0, 2, 0; 2, 2, 2, 1; 2, 0, 2, 2; 1, 2, 1, 2]) (M' := !![2, 1, 2, 2; 0, 1, 0, 1; 1, 1, 2, 2; 0, 1, 1, 2])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_2_2_1 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![2, 1, 1, 1; 1, 1, 2, 2; 2, 0, 2, 0; 2, 0, 1, 2]) (M' := !![1, 2, 1, 2; 2, 2, 0, 0; 2, 1, 1, 1; 1, 2, 0, 1])
    (by decide +kernel) (by decide +kernel)

noncomputable def owR34_e_2_2_2_2 : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  Matrix.toLin'OfInv (M := !![0, 2, 0, 1; 0, 2, 0, 2; 2, 0, 1, 0; 1, 0, 1, 0]) (M' := !![0, 0, 1, 2; 1, 1, 0, 0; 0, 0, 2, 2; 2, 1, 0, 0])
    (by decide +kernel) (by decide +kernel)

theorem owR34_lw_1_1_1_1 : owR34_W ![1, 1, 1, 1] :=
  owR34_linWeyl_of_iso ![1, 1, 1, 1] owR34_wD4 owR34_e_1_1_1_1
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_1_1_1_2 : owR34_W ![1, 1, 1, 2] :=
  owR34_linWeyl_of_iso ![1, 1, 1, 2] owR34_wA5 owR34_e_1_1_1_2
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_1_1_2_1 : owR34_W ![1, 1, 2, 1] :=
  owR34_linWeyl_of_iso ![1, 1, 2, 1] owR34_wA5 owR34_e_1_1_2_1
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_1_1_2_2 : owR34_W ![1, 1, 2, 2] :=
  owR34_linWeyl_of_iso ![1, 1, 2, 2] owR34_wD4 owR34_e_1_1_2_2
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_1_2_1_1 : owR34_W ![1, 2, 1, 1] :=
  owR34_linWeyl_of_iso ![1, 2, 1, 1] owR34_wA5 owR34_e_1_2_1_1
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_1_2_1_2 : owR34_W ![1, 2, 1, 2] :=
  owR34_linWeyl_of_iso ![1, 2, 1, 2] owR34_wD4 owR34_e_1_2_1_2
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_1_2_2_1 : owR34_W ![1, 2, 2, 1] :=
  owR34_linWeyl_of_iso ![1, 2, 2, 1] owR34_wD4 owR34_e_1_2_2_1
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_1_2_2_2 : owR34_W ![1, 2, 2, 2] :=
  owR34_linWeyl_of_iso ![1, 2, 2, 2] owR34_wA5 owR34_e_1_2_2_2
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_2_1_1_1 : owR34_W ![2, 1, 1, 1] :=
  owR34_linWeyl_of_iso ![2, 1, 1, 1] owR34_wA5 owR34_e_2_1_1_1
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_2_1_1_2 : owR34_W ![2, 1, 1, 2] :=
  owR34_linWeyl_of_iso ![2, 1, 1, 2] owR34_wD4 owR34_e_2_1_1_2
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_2_1_2_1 : owR34_W ![2, 1, 2, 1] :=
  owR34_linWeyl_of_iso ![2, 1, 2, 1] owR34_wD4 owR34_e_2_1_2_1
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_2_1_2_2 : owR34_W ![2, 1, 2, 2] :=
  owR34_linWeyl_of_iso ![2, 1, 2, 2] owR34_wA5 owR34_e_2_1_2_2
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_2_2_1_1 : owR34_W ![2, 2, 1, 1] :=
  owR34_linWeyl_of_iso ![2, 2, 1, 1] owR34_wD4 owR34_e_2_2_1_1
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_lw_2_2_1_2 : owR34_W ![2, 2, 1, 2] :=
  owR34_linWeyl_of_iso ![2, 2, 1, 2] owR34_wA5 owR34_e_2_2_1_2
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_2_2_2_1 : owR34_W ![2, 2, 2, 1] :=
  owR34_linWeyl_of_iso ![2, 2, 2, 1] owR34_wA5 owR34_e_2_2_2_1
    (by decide +kernel) owR34_A5_linWeyl

theorem owR34_lw_2_2_2_2 : owR34_W ![2, 2, 2, 2] :=
  owR34_linWeyl_of_iso ![2, 2, 2, 2] owR34_wD4 owR34_e_2_2_2_2
    (by decide +kernel) owR34_D4_linWeyl

theorem owR34_W_congr (v w : Fin 4 → ZMod 3) (h : v = w) (hw : owR34_W w) : owR34_W v := by
  subst h
  exact hw

theorem owR34_linWeyl_abcd : ∀ a b c d : ZMod 3, (a = 1 ∨ a = 2) → (b = 1 ∨ b = 2) →
    (c = 1 ∨ c = 2) → (d = 1 ∨ d = 2) → owR34_W ![a, b, c, d] := by
  intro a b c d ha hb hc hd
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl
  · exact owR34_lw_1_1_1_1
  · exact owR34_lw_1_1_1_2
  · exact owR34_lw_1_1_2_1
  · exact owR34_lw_1_1_2_2
  · exact owR34_lw_1_2_1_1
  · exact owR34_lw_1_2_1_2
  · exact owR34_lw_1_2_2_1
  · exact owR34_lw_1_2_2_2
  · exact owR34_lw_2_1_1_1
  · exact owR34_lw_2_1_1_2
  · exact owR34_lw_2_1_2_1
  · exact owR34_lw_2_1_2_2
  · exact owR34_lw_2_2_1_1
  · exact owR34_lw_2_2_1_2
  · exact owR34_lw_2_2_2_1
  · exact owR34_lw_2_2_2_2

theorem owR34_linWeyl_vec (v : Fin 4 → ZMod 3) (hv : ∀ i, v i = 1 ∨ v i = 2) :
    owR34_W v := by
  have hv_eq : v = ![v 0, v 1, v 2, v 3] := by
    funext i; fin_cases i <;> rfl
  exact owR34_W_congr v _ hv_eq (owR34_linWeyl_abcd _ _ _ _ (hv 0) (hv 1) (hv 2) (hv 3))

end CFSG.StandardType.ZS

end
