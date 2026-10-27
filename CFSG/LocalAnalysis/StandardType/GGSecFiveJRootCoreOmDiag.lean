module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.ClassicalGroups.Orthogonal.Eichler
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.TorusM8POmegaPlus
import CFSG.LieType.Universal.Spin.Generation.Eichler

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal

@[expose] def JCoreOmRootPair (n : ℕ) (F : Type) [Field F]
    (T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ∃ s t : Bool, ∀ c : F,
    eichler (quadPlus n F) (plusVec n F j t) (c • plusVec n F i s) ∈ T ∧
      eichler (quadPlus n F) (plusVec n F i (!s)) (c • plusVec n F j (!t)) ∈ T

theorem jcoreOm_diag {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    {u : ↥(spinGroup (quadPlus n F))} (hu : u ∈ ggTorus (plusDatum n F hn)) :
    ∃ a : Fin n → Fˣ, ∀ (v : Fin n ⊕ Fin n → F) (c : Fin n ⊕ Fin n),
      spinAction (quadPlus n F) u v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c := by
  classical
  set d : Fin n ⊕ Fin n → F := fun c => spinAction (quadPlus n F) u (Pi.single c 1) c
  have hoff : ∀ c b : Fin n ⊕ Fin n, c ≠ b →
      spinAction (quadPlus n F) u (Pi.single b 1) c = 0 := by
    intro c b hcb
    have h := ClassicalPosition.ggTorus_apply_eq_zero_POmegaPlus n F hn hu hcb
    rwa [coe_spinMatrix, LinearMap.toMatrix'_apply] at h
  have hdiag : ∀ v c, spinAction (quadPlus n F) u v c = d c * v c := by
    intro v c
    have h1 := LinearMap.toMatrix'_mulVec (spinAction (quadPlus n F) u).toLinearMap v
    rw [LinearEquiv.coe_coe] at h1
    rw [← h1]
    change ∑ b, LinearMap.toMatrix' (spinAction (quadPlus n F) u).toLinearMap c b * v b = _
    rw [Finset.sum_eq_single c (fun b _ hbc => ?_) (fun h => absurd (Finset.mem_univ c) h)]
    · rfl
    · rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, hoff c b (Ne.symm hbc), zero_mul]
  have hsingle : ∀ c, spinAction (quadPlus n F) u (Pi.single c 1) = d c • Pi.single c 1 := by
    intro c
    funext b
    rw [hdiag, Pi.smul_apply, smul_eq_mul]
    by_cases hbc : b = c
    · rw [hbc]
    · rw [Pi.single_eq_of_ne hbc, mul_zero, mul_zero]
  have hprod : ∀ k, d (.inl k) * d (.inr k) = 1 := by
    intro k
    have h := polar_spinAction (quadPlus n F) u (Pi.single (.inl k) 1) (Pi.single (.inr k) 1)
    rw [hsingle, hsingle, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      polar_quadPlus_single_inr, Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one] at h
    exact h
  refine ⟨fun k => ⟨d (.inl k), d (.inr k), hprod k, by rw [mul_comm]; exact hprod k⟩,
    fun v c => ?_⟩
  rw [hdiag]
  rcases c with k | k <;> rfl

theorem jcoreOm_rootLevi {n : ℕ} {F : Type} [Field F] (hn : 3 ≤ n)
    {T : Subgroup ((Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F))}
    {J : Subgroup ↥(spinGroup (quadPlus n F))}
    (hT : ∀ z, spinAction (quadPlus n F) z ∈ T → z ∈ J) (hP : JCoreOmRootPair n F T) :
    ∃ γ ∈ (plusDatum n F hn).roots, ggRootLevi (plusDatum n F hn) γ ≤ J := by
  obtain ⟨i, j, hij, s, t, hc⟩ := hP
  obtain ⟨γ, hγ, hγeq⟩ := exists_mem_rootsD_toStdD_eq n hij (boolSign_eq_one_or_eq_neg_one s)
    (boolSign_eq_one_or_eq_neg_one t)
  have hneg : toStdD n (-γ) = Pi.single j (boolSign (!t)) + Pi.single i (boolSign (!s)) := by
    rw [toStdD_neg, hγeq, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add,
      add_comm]
  refine ⟨γ, hγ, sup_le ?_ ?_⟩
  · change plusRootGroup n F hn γ ≤ J
    rw [plusRootGroup_eq hn hij s t hγeq]
    rintro _ ⟨y, rfl⟩
    apply hT
    have h := (plusFrame n F hn).spinAction_longRoot_eq_eichler hij s t (Multiplicative.toAdd y)
    rw [ofAdd_toAdd, plusFrame_vec] at h
    rw [h]
    exact (hc _).1
  · change plusRootGroup n F hn (-γ) ≤ J
    rw [plusRootGroup_eq hn hij.symm (!t) (!s) hneg]
    rintro _ ⟨y, rfl⟩
    apply hT
    have h := (plusFrame n F hn).spinAction_longRoot_eq_eichler hij.symm (!t) (!s)
      (Multiplicative.toAdd y)
    rw [ofAdd_toAdd, plusFrame_vec] at h
    rw [h]
    exact (hc _).2

end CFSG.StandardType

end
