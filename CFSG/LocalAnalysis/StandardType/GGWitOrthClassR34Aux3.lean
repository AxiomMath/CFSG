module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34DataD4
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTypeD4
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord
public import CFSG.LocalAnalysis.StandardType.GGWitOrthPolar

public section

namespace CFSG.StandardType.ZS

open Subgroup

abbrev owR34_QD4 : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) :=
  @QuadraticMap.weightedSumSquares (ZMod 3) (ZMod 3) _ (Fin 4) _ _ _ _ owR34_wD4

theorem owR34_QD4_hD4_ne_zero (i : Fin 4) : owR34_QD4 (owR34_aD4 i) ≠ 0 := by
  rw [owR34_QD4]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  rw [owR34_normD4 i]
  decide

theorem owR34_polarD4 (x y : Fin 4 → ZMod 3) :
    QuadraticMap.polar owR34_QD4 x y = 2 * ∑ k, owR34_wD4 k * (x k * y k) :=
  owPo_polar_weightedSumSquares (K := ZMod 3) owR34_wD4 x y

def owR34_alphaD4 (i : Fin 4) : (Fin 4 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun v := (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wD4 k * (v k * (owR34_aD4 i) k)
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem owR34_alphaD4_apply (i : Fin 4) (v : Fin 4 → ZMod 3) :
    owR34_alphaD4 i v = (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wD4 k * (v k * (owR34_aD4 i) k) := by
  simp only [owR34_alphaD4]
  rfl

theorem owR34_alphaD4_self (i : Fin 4) : owR34_alphaD4 i (owR34_aD4 i) = 2 := by
  rw [owR34_alphaD4_apply, owR34_cartanD4 i i, owR34_diagD4 i]

noncomputable def owR34_sD4 (i : Fin 4) :
    (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @Module.reflection (ZMod 3) (Fin 4 → ZMod 3) (ZMod.commRing 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_aD4 i) (owR34_alphaD4 i)
    (owR34_alphaD4_self i)

theorem owR34_hs_D4 : ∀ i v, owR34_sD4 i v = v - owR34_alphaD4 i v • owR34_aD4 i := by
  intro i v
  simp only [owR34_sD4, Module.reflection_apply]
  rfl

theorem owR34_hP_D4 : ∀ i j : Fin 4,
    owR34_alphaD4 i (owR34_aD4 j) = (CartanMatrix.D 4 i j : ZMod 3) := by
  intro i j
  rw [owR34_alphaD4_apply]
  exact owR34_cartanD4 i j

@[expose] def owR34_classReflD4 : Set ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  @ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 1

@[expose] def owR34_AD4 : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) owR34_classReflD4

theorem owR34_hs_mem_D4 : ∀ i, owR34_sD4 i ∈ owR34_classReflD4 := by
  intro i
  unfold owR34_classReflD4 owR34_QD4
  refine (wit_coord_classRefl_iff (p := 3) (hp := by norm_num) (hp2 := by decide)
    (d := 4) (w := owR34_wD4) (c := 1) (hc := by decide) (owR34_sD4 i)).mpr ?_
  exact ⟨owR34_aD4 i, owR34_normD4 i,
    fun v => by rw [owR34_hs_D4 i v, owR34_alphaD4_apply]⟩

noncomputable def owR34_rD4 (a : Fin 4 → ZMod 3) (ha : owR34_QD4 a ≠ 0) :
    (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @owCr_orthRefl (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 a ha

theorem owR34_rD4_apply (a : Fin 4 → ZMod 3) (ha : owR34_QD4 a ≠ 0) (v : Fin 4 → ZMod 3) :
    owR34_rD4 a ha v = v - (QuadraticMap.polar owR34_QD4 v a / owR34_QD4 a) • a := by
  rw [owR34_rD4]
  exact @owCr_orthRefl_apply (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 a ha v

theorem owR34_rD4_conj (g : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    (hg : ∀ v, owR34_QD4 (g v) = owR34_QD4 v) (a : Fin 4 → ZMod 3) (ha : owR34_QD4 a ≠ 0)
    (hga : owR34_QD4 (g a) ≠ 0) :
    g * owR34_rD4 a ha * g⁻¹ = owR34_rD4 (g a) hga :=
  @owCr_orthRefl_conj (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 g hg a ha hga

theorem owR34_rD4_neg (a : Fin 4 → ZMod 3) (ha : owR34_QD4 a ≠ 0) (h : owR34_QD4 (-a) ≠ 0) :
    owR34_rD4 (-a) h = owR34_rD4 a ha :=
  @owCr_orthRefl_neg (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 a ha h

theorem owR34_rD4_proof_irrel (a : Fin 4 → ZMod 3) (h1 h2 : owR34_QD4 a ≠ 0) :
    owR34_rD4 a h1 = owR34_rD4 a h2 :=
  congrArg (owR34_rD4 a) (Subsingleton.elim h1 h2)

theorem owR34_rD4_congr (x y : Fin 4 → ZMod 3) (hx : owR34_QD4 x ≠ 0) (hy : owR34_QD4 y ≠ 0)
    (h : x = y) : owR34_rD4 x hx = owR34_rD4 y hy := by
  subst h
  rfl

theorem owR34_sD4_eq_rD4 (i : Fin 4) :
    owR34_sD4 i = owR34_rD4 (owR34_aD4 i) (owR34_QD4_hD4_ne_zero i) := by
  ext v
  rw [owR34_hs_D4, owR34_rD4_apply, owR34_polarD4, owR34_alphaD4_apply]
  have hnorm : owR34_QD4 (owR34_aD4 i) = 1 := by
    rw [owR34_QD4]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    exact owR34_normD4 i
  rw [hnorm, inv_one, mul_one]
  ring_nf

theorem owR34_QD4_XD4 (k : Fin 12) : owR34_QD4 (owR34_XD4 k) = 1 := by
  rw [owR34_QD4]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  exact owR34_normXD4 k

theorem owR34_XD4_ne_zero (k : Fin 12) : owR34_QD4 (owR34_XD4 k) ≠ 0 := by
  rw [owR34_QD4_XD4 k]; decide

theorem owR34_sD4_isIsom (i : Fin 4) : ∀ v, owR34_QD4 (owR34_sD4 i v) = owR34_QD4 v :=
  (owR34_hs_mem_D4 i).2.1

theorem owR34_chain_sD4_0 : owR34_XD4 4 = owR34_sD4 1 (owR34_XD4 0) := by
  rw [owR34_chainD4_0]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_1 : owR34_XD4 5 = owR34_sD4 2 (owR34_XD4 1) := by
  rw [owR34_chainD4_1]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_2 : owR34_XD4 6 = owR34_sD4 3 (owR34_XD4 1) := by
  rw [owR34_chainD4_2]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_3 : owR34_XD4 7 = owR34_sD4 2 (owR34_XD4 4) := by
  rw [owR34_chainD4_3]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_4 : owR34_XD4 8 = owR34_sD4 3 (owR34_XD4 4) := by
  rw [owR34_chainD4_4]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_5 : owR34_XD4 9 = owR34_sD4 3 (owR34_XD4 5) := by
  rw [owR34_chainD4_5]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_6 : owR34_XD4 10 = owR34_sD4 3 (owR34_XD4 7) := by
  rw [owR34_chainD4_6]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sD4_7 : owR34_XD4 11 = owR34_sD4 1 (owR34_XD4 10) := by
  rw [owR34_chainD4_7]
  ext k
  rw [owR34_hs_D4, owR34_alphaD4_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_rD4_step (i : Fin 4) (x : Fin 4 → ZMod 3) (hx : owR34_QD4 x ≠ 0)
    (hxmem : owR34_rD4 x hx ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4))
    (hx' : owR34_QD4 (owR34_sD4 i x) ≠ 0) :
    owR34_rD4 (owR34_sD4 i x) hx' ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
  rw [← owR34_rD4_conj (owR34_sD4 i) (owR34_sD4_isIsom i) x hx hx']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hxmem)
    (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩))

theorem owR34_rD4_aD4_mem (i : Fin 4) :
    owR34_rD4 (owR34_aD4 i) (owR34_QD4_hD4_ne_zero i) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
  rw [← owR34_sD4_eq_rD4 i]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem owR34_XD4_step (par : Fin 12) (gen : Fin 4) (k : Fin 12)
    (hk : owR34_XD4 k = owR34_sD4 gen (owR34_XD4 par))
    (hpar : owR34_rD4 (owR34_XD4 par) (owR34_XD4_ne_zero par) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4)) :
    owR34_rD4 (owR34_XD4 k) (owR34_XD4_ne_zero k) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
  have h := owR34_rD4_step gen (owR34_XD4 par) (owR34_XD4_ne_zero par) hpar
    (by rw [← hk]; exact owR34_XD4_ne_zero k)
  rw [owR34_rD4_congr _ _ _ _ hk]
  exact h

theorem owR34_QD4_neg : ∀ x : Fin 4 → ZMod 3, owR34_QD4 (-x) = owR34_QD4 x := by
  decide +kernel

theorem owR34_rD4_neg_eq (k : Fin 12) :
    owR34_rD4 (-owR34_XD4 k) (by rw [owR34_QD4_neg]; exact owR34_XD4_ne_zero k)
      = owR34_rD4 (owR34_XD4 k) (owR34_XD4_ne_zero k) := by
  rw [owR34_rD4_neg]

theorem owR34_XD4_mem (k : Fin 12) :
    owR34_rD4 (owR34_XD4 k) (owR34_XD4_ne_zero k) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
  have h0 : owR34_rD4 (owR34_XD4 0) (owR34_XD4_ne_zero 0) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
    change owR34_rD4 (owR34_aD4 0) (owR34_XD4_ne_zero 0) ∈ _
    exact owR34_rD4_proof_irrel (owR34_aD4 0) (owR34_XD4_ne_zero 0)
      (owR34_QD4_hD4_ne_zero 0) ▸ owR34_rD4_aD4_mem 0
  have h1 : owR34_rD4 (owR34_XD4 1) (owR34_XD4_ne_zero 1) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
    change owR34_rD4 (owR34_aD4 1) (owR34_XD4_ne_zero 1) ∈ _
    exact owR34_rD4_proof_irrel (owR34_aD4 1) (owR34_XD4_ne_zero 1)
      (owR34_QD4_hD4_ne_zero 1) ▸ owR34_rD4_aD4_mem 1
  have h2 : owR34_rD4 (owR34_XD4 2) (owR34_XD4_ne_zero 2) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
    change owR34_rD4 (owR34_aD4 2) (owR34_XD4_ne_zero 2) ∈ _
    exact owR34_rD4_proof_irrel (owR34_aD4 2) (owR34_XD4_ne_zero 2)
      (owR34_QD4_hD4_ne_zero 2) ▸ owR34_rD4_aD4_mem 2
  have h3 : owR34_rD4 (owR34_XD4 3) (owR34_XD4_ne_zero 3) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) := by
    change owR34_rD4 (owR34_aD4 3) (owR34_XD4_ne_zero 3) ∈ _
    exact owR34_rD4_proof_irrel (owR34_aD4 3) (owR34_XD4_ne_zero 3)
      (owR34_QD4_hD4_ne_zero 3) ▸ owR34_rD4_aD4_mem 3
  have h4 : owR34_rD4 (owR34_XD4 4) (owR34_XD4_ne_zero 4) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 0 1 4 owR34_chain_sD4_0 h0
  have h5 : owR34_rD4 (owR34_XD4 5) (owR34_XD4_ne_zero 5) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 1 2 5 owR34_chain_sD4_1 h1
  have h6 : owR34_rD4 (owR34_XD4 6) (owR34_XD4_ne_zero 6) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 1 3 6 owR34_chain_sD4_2 h1
  have h7 : owR34_rD4 (owR34_XD4 7) (owR34_XD4_ne_zero 7) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 4 2 7 owR34_chain_sD4_3 h4
  have h8 : owR34_rD4 (owR34_XD4 8) (owR34_XD4_ne_zero 8) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 4 3 8 owR34_chain_sD4_4 h4
  have h9 : owR34_rD4 (owR34_XD4 9) (owR34_XD4_ne_zero 9) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 5 3 9 owR34_chain_sD4_5 h5
  have h10 : owR34_rD4 (owR34_XD4 10) (owR34_XD4_ne_zero 10) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 7 3 10 owR34_chain_sD4_6 h7
  have h11 : owR34_rD4 (owR34_XD4 11) (owR34_XD4_ne_zero 11) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) :=
    owR34_XD4_step 10 1 11 owR34_chain_sD4_7 h10
  fin_cases k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11

theorem owR34_hgen_D4 :
    @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sD4) = owR34_AD4 := by
  apply le_antisymm
  · rw [owR34_AD4]
    exact Subgroup.closure_mono (fun x hx => by
      rcases hx with ⟨i, rfl⟩
      exact owR34_hs_mem_D4 i)
  · rw [owR34_AD4]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ht
    rw [owR34_classReflD4] at ht
    have ht' := (wit_coord_classRefl_iff (p := 3) (hp := by norm_num) (hp2 := by decide)
      (d := 4) (w := owR34_wD4) (c := 1) (hc := by decide) t).mp ht
    obtain ⟨a, ha, hform⟩ := ht'
    have hnorm : owR34_QD4 a = 1 := by
      rw [owR34_QD4]
      simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
      exact ha
    have hQa : owR34_QD4 a ≠ 0 := by rw [hnorm]; decide
    have ht_eq : t = owR34_rD4 a hQa := by
      ext v
      rw [hform v, owR34_rD4_apply, owR34_polarD4, hnorm, div_one]
      ring_nf
    rw [ht_eq]
    rcases owR34_coverD4 a ha with ⟨k, hk | hk⟩
    · rw [owR34_rD4_congr _ _ _ _ hk]
      exact owR34_XD4_mem k
    · rw [owR34_rD4_congr _ _ _ _ hk]
      exact (owR34_rD4_neg_eq k) ▸ owR34_XD4_mem k

theorem owR34_D4_linWeyl :
    @LinWeyl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_AD4 :=
  @owTD4_linWeyl_of_typeD4 (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QD4 1 owR34_AD4
    owR34_aD4 owR34_alphaD4 owR34_hP_D4 owR34_sD4 owR34_hs_D4 owR34_hs_mem_D4 owR34_hgen_D4

end CFSG.StandardType.ZS

end
