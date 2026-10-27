module

public import CFSG.LocalAnalysis.StandardType.GGWitOrthClassR34Data
public import CFSG.LocalAnalysis.StandardType.GGWitOrthTypeA
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCrAux
public import CFSG.LocalAnalysis.StandardType.GGWitOrthCoord
public import CFSG.LocalAnalysis.StandardType.GGWitOrthPolar

public section

namespace CFSG.StandardType.ZS

open Subgroup

abbrev owR34_QA5 : QuadraticForm (ZMod 3) (Fin 4 → ZMod 3) :=
  @QuadraticMap.weightedSumSquares (ZMod 3) (ZMod 3) _ (Fin 4) _ _ _ _ owR34_wA5

theorem owR34_QA5_hA5_ne_zero (i : Fin 5) : owR34_QA5 (owR34_aA5 i) ≠ 0 := by
  rw [owR34_QA5]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  rw [owR34_normA5 i]
  decide

theorem owR34_polarA5 (x y : Fin 4 → ZMod 3) :
    QuadraticMap.polar owR34_QA5 x y = 2 * ∑ k, owR34_wA5 k * (x k * y k) :=
  owPo_polar_weightedSumSquares (K := ZMod 3) owR34_wA5 x y

def owR34_alphaA5 (i : Fin 5) : (Fin 4 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun v := (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wA5 k * (v k * (owR34_aA5 i) k)
  map_add' x y := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem owR34_alphaA5_apply (i : Fin 5) (v : Fin 4 → ZMod 3) :
    owR34_alphaA5 i v = (2 * (1 : ZMod 3)⁻¹) * ∑ k, owR34_wA5 k * (v k * (owR34_aA5 i) k) := by
  simp only [owR34_alphaA5]
  rfl

theorem owR34_alphaA5_self (i : Fin 5) : owR34_alphaA5 i (owR34_aA5 i) = 2 := by
  rw [owR34_alphaA5_apply]
  have h := owR34_cartanA5 i i
  rw [h]
  simp [CartanMatrix.A]

noncomputable def owR34_sA5 (i : Fin 5) :
    (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @Module.reflection (ZMod 3) (Fin 4 → ZMod 3) (ZMod.commRing 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) (owR34_aA5 i) (owR34_alphaA5 i)
    (owR34_alphaA5_self i)

theorem owR34_hs_A5 : ∀ i v, owR34_sA5 i v = v - owR34_alphaA5 i v • owR34_aA5 i := by
  intro i v
  simp only [owR34_sA5, Module.reflection_apply]
  rfl

theorem owR34_hP_A5 : ∀ i j : Fin 5,
    owR34_alphaA5 i (owR34_aA5 j) = (CartanMatrix.A 5 i j : ZMod 3) := by
  intro i j
  rw [owR34_alphaA5_apply]
  exact owR34_cartanA5 i j

@[expose] def owR34_classReflA5 : Set ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  @ClassRefl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 1

@[expose] def owR34_AA5 : Subgroup ((Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3)) :=
  @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) owR34_classReflA5

theorem owR34_hs_mem_A5 : ∀ i, owR34_sA5 i ∈ owR34_classReflA5 := by
  intro i
  unfold owR34_classReflA5 owR34_QA5
  refine (wit_coord_classRefl_iff (p := 3) (hp := by norm_num) (hp2 := by decide)
    (d := 4) (w := owR34_wA5) (c := 1) (hc := by decide) (owR34_sA5 i)).mpr ?_
  exact ⟨owR34_aA5 i, owR34_normA5 i,
    fun v => by rw [owR34_hs_A5 i v, owR34_alphaA5_apply]⟩

noncomputable def owR34_rA5 (a : Fin 4 → ZMod 3) (ha : owR34_QA5 a ≠ 0) :
    (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3) :=
  @owCr_orthRefl (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 a ha

theorem owR34_rA5_apply (a : Fin 4 → ZMod 3) (ha : owR34_QA5 a ≠ 0) (v : Fin 4 → ZMod 3) :
    owR34_rA5 a ha v = v - (QuadraticMap.polar owR34_QA5 v a / owR34_QA5 a) • a := by
  rw [owR34_rA5]
  exact @owCr_orthRefl_apply (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 a ha v

theorem owR34_rA5_conj (g : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] (Fin 4 → ZMod 3))
    (hg : ∀ v, owR34_QA5 (g v) = owR34_QA5 v) (a : Fin 4 → ZMod 3) (ha : owR34_QA5 a ≠ 0)
    (hga : owR34_QA5 (g a) ≠ 0) :
    g * owR34_rA5 a ha * g⁻¹ = owR34_rA5 (g a) hga :=
  @owCr_orthRefl_conj (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 g hg a ha hga

theorem owR34_rA5_neg (a : Fin 4 → ZMod 3) (ha : owR34_QA5 a ≠ 0) (h : owR34_QA5 (-a) ≠ 0) :
    owR34_rA5 (-a) h = owR34_rA5 a ha :=
  @owCr_orthRefl_neg (ZMod 3) (@ZMod.instField 3 ⟨by norm_num⟩) (Fin 4 → ZMod 3)
    (Pi.addCommGroup) (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 a ha h

theorem owR34_rA5_proof_irrel (a : Fin 4 → ZMod 3) (h1 h2 : owR34_QA5 a ≠ 0) :
    owR34_rA5 a h1 = owR34_rA5 a h2 :=
  congrArg (owR34_rA5 a) (Subsingleton.elim h1 h2)

theorem owR34_rA5_congr (x y : Fin 4 → ZMod 3) (hx : owR34_QA5 x ≠ 0) (hy : owR34_QA5 y ≠ 0)
    (h : x = y) : owR34_rA5 x hx = owR34_rA5 y hy := by
  subst h
  rfl

theorem owR34_sA5_eq_rA5 (i : Fin 5) :
    owR34_sA5 i = owR34_rA5 (owR34_aA5 i) (owR34_QA5_hA5_ne_zero i) := by
  ext v
  rw [owR34_hs_A5, owR34_rA5_apply, owR34_polarA5, owR34_alphaA5_apply]
  have hnorm : owR34_QA5 (owR34_aA5 i) = 1 := by
    rw [owR34_QA5]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    exact owR34_normA5 i
  rw [hnorm, inv_one, mul_one]
  ring_nf

theorem owR34_QA5_XA5 (k : Fin 15) : owR34_QA5 (owR34_XA5 k) = 1 := by
  rw [owR34_QA5]
  simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
  exact owR34_normXA5 k

theorem owR34_XA5_ne_zero (k : Fin 15) : owR34_QA5 (owR34_XA5 k) ≠ 0 := by
  rw [owR34_QA5_XA5 k]; decide

theorem owR34_sA5_isIsom (i : Fin 5) : ∀ v, owR34_QA5 (owR34_sA5 i v) = owR34_QA5 v :=
  (owR34_hs_mem_A5 i).2.1

theorem owR34_chain_sA5_0 : owR34_XA5 5 = owR34_sA5 1 (owR34_XA5 0) := by
  rw [owR34_chainA5_0]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_1 : owR34_XA5 6 = owR34_sA5 2 (owR34_XA5 1) := by
  rw [owR34_chainA5_1]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_2 : owR34_XA5 7 = owR34_sA5 3 (owR34_XA5 2) := by
  rw [owR34_chainA5_2]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_3 : owR34_XA5 8 = owR34_sA5 4 (owR34_XA5 3) := by
  rw [owR34_chainA5_3]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_4 : owR34_XA5 9 = owR34_sA5 2 (owR34_XA5 5) := by
  rw [owR34_chainA5_4]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_5 : owR34_XA5 10 = owR34_sA5 3 (owR34_XA5 6) := by
  rw [owR34_chainA5_5]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_6 : owR34_XA5 11 = owR34_sA5 4 (owR34_XA5 7) := by
  rw [owR34_chainA5_6]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_7 : owR34_XA5 12 = owR34_sA5 3 (owR34_XA5 9) := by
  rw [owR34_chainA5_7]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_8 : owR34_XA5 13 = owR34_sA5 4 (owR34_XA5 10) := by
  rw [owR34_chainA5_8]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_chain_sA5_9 : owR34_XA5 14 = owR34_sA5 4 (owR34_XA5 12) := by
  rw [owR34_chainA5_9]
  ext k
  rw [owR34_hs_A5, owR34_alphaA5_apply]
  simp only [owR34_reflect]
  rfl

theorem owR34_rA5_step (i : Fin 5) (x : Fin 4 → ZMod 3) (hx : owR34_QA5 x ≠ 0)
    (hxmem : owR34_rA5 x hx ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5))
    (hx' : owR34_QA5 (owR34_sA5 i x) ≠ 0) :
    owR34_rA5 (owR34_sA5 i x) hx' ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
  rw [← owR34_rA5_conj (owR34_sA5 i) (owR34_sA5_isIsom i) x hx hx']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) hxmem)
    (Subgroup.inv_mem _ (Subgroup.subset_closure ⟨i, rfl⟩))

theorem owR34_rA5_aA5_mem (i : Fin 5) :
    owR34_rA5 (owR34_aA5 i) (owR34_QA5_hA5_ne_zero i) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
  rw [← owR34_sA5_eq_rA5 i]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem owR34_XA5_step (par : Fin 15) (gen : Fin 5) (k : Fin 15)
    (hk : owR34_XA5 k = owR34_sA5 gen (owR34_XA5 par))
    (hpar : owR34_rA5 (owR34_XA5 par) (owR34_XA5_ne_zero par) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5)) :
    owR34_rA5 (owR34_XA5 k) (owR34_XA5_ne_zero k) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
  have h := owR34_rA5_step gen (owR34_XA5 par) (owR34_XA5_ne_zero par) hpar
    (by rw [← hk]; exact owR34_XA5_ne_zero k)
  rw [owR34_rA5_congr _ _ _ _ hk]
  exact h

theorem owR34_QA5_neg : ∀ x : Fin 4 → ZMod 3, owR34_QA5 (-x) = owR34_QA5 x := by
  decide +kernel

theorem owR34_rA5_neg_eq (k : Fin 15) :
    owR34_rA5 (-owR34_XA5 k) (by rw [owR34_QA5_neg]; exact owR34_XA5_ne_zero k)
      = owR34_rA5 (owR34_XA5 k) (owR34_XA5_ne_zero k) := by
  rw [owR34_rA5_neg]

theorem owR34_XA5_mem (k : Fin 15) :
    owR34_rA5 (owR34_XA5 k) (owR34_XA5_ne_zero k) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
  have h0 : owR34_rA5 (owR34_XA5 0) (owR34_XA5_ne_zero 0) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
    change owR34_rA5 (owR34_aA5 0) (owR34_XA5_ne_zero 0) ∈ _
    exact owR34_rA5_proof_irrel (owR34_aA5 0) (owR34_XA5_ne_zero 0)
      (owR34_QA5_hA5_ne_zero 0) ▸ owR34_rA5_aA5_mem 0
  have h1 : owR34_rA5 (owR34_XA5 1) (owR34_XA5_ne_zero 1) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
    change owR34_rA5 (owR34_aA5 1) (owR34_XA5_ne_zero 1) ∈ _
    exact owR34_rA5_proof_irrel (owR34_aA5 1) (owR34_XA5_ne_zero 1)
      (owR34_QA5_hA5_ne_zero 1) ▸ owR34_rA5_aA5_mem 1
  have h2 : owR34_rA5 (owR34_XA5 2) (owR34_XA5_ne_zero 2) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
    change owR34_rA5 (owR34_aA5 2) (owR34_XA5_ne_zero 2) ∈ _
    exact owR34_rA5_proof_irrel (owR34_aA5 2) (owR34_XA5_ne_zero 2)
      (owR34_QA5_hA5_ne_zero 2) ▸ owR34_rA5_aA5_mem 2
  have h3 : owR34_rA5 (owR34_XA5 3) (owR34_XA5_ne_zero 3) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
    change owR34_rA5 (owR34_aA5 3) (owR34_XA5_ne_zero 3) ∈ _
    exact owR34_rA5_proof_irrel (owR34_aA5 3) (owR34_XA5_ne_zero 3)
      (owR34_QA5_hA5_ne_zero 3) ▸ owR34_rA5_aA5_mem 3
  have h4 : owR34_rA5 (owR34_XA5 4) (owR34_XA5_ne_zero 4) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) := by
    change owR34_rA5 (owR34_aA5 4) (owR34_XA5_ne_zero 4) ∈ _
    exact owR34_rA5_proof_irrel (owR34_aA5 4) (owR34_XA5_ne_zero 4)
      (owR34_QA5_hA5_ne_zero 4) ▸ owR34_rA5_aA5_mem 4
  have h5 : owR34_rA5 (owR34_XA5 5) (owR34_XA5_ne_zero 5) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 0 1 5 owR34_chain_sA5_0 h0
  have h6 : owR34_rA5 (owR34_XA5 6) (owR34_XA5_ne_zero 6) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 1 2 6 owR34_chain_sA5_1 h1
  have h7 : owR34_rA5 (owR34_XA5 7) (owR34_XA5_ne_zero 7) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 2 3 7 owR34_chain_sA5_2 h2
  have h8 : owR34_rA5 (owR34_XA5 8) (owR34_XA5_ne_zero 8) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 3 4 8 owR34_chain_sA5_3 h3
  have h9 : owR34_rA5 (owR34_XA5 9) (owR34_XA5_ne_zero 9) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 5 2 9 owR34_chain_sA5_4 h5
  have h10 : owR34_rA5 (owR34_XA5 10) (owR34_XA5_ne_zero 10) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 6 3 10 owR34_chain_sA5_5 h6
  have h11 : owR34_rA5 (owR34_XA5 11) (owR34_XA5_ne_zero 11) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 7 4 11 owR34_chain_sA5_6 h7
  have h12 : owR34_rA5 (owR34_XA5 12) (owR34_XA5_ne_zero 12) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 9 3 12 owR34_chain_sA5_7 h9
  have h13 : owR34_rA5 (owR34_XA5 13) (owR34_XA5_ne_zero 13) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 10 4 13 owR34_chain_sA5_8 h10
  have h14 : owR34_rA5 (owR34_XA5 14) (owR34_XA5_ne_zero 14) ∈
      @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
        (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) :=
    owR34_XA5_step 12 4 14 owR34_chain_sA5_9 h12
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
  · exact h12
  · exact h13
  · exact h14

theorem owR34_hgen_A5 :
    @Subgroup.closure _ (@LinearEquiv.automorphismGroup (ZMod 3) (Fin 4 → ZMod 3) _ _
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3))) (Set.range owR34_sA5) = owR34_AA5 := by
  apply le_antisymm
  · rw [owR34_AA5]
    exact Subgroup.closure_mono (fun x hx => by
      rcases hx with ⟨i, rfl⟩
      exact owR34_hs_mem_A5 i)
  · rw [owR34_AA5]
    refine (Subgroup.closure_le _).mpr ?_
    rintro t ht
    rw [owR34_classReflA5] at ht
    have ht' := (wit_coord_classRefl_iff (p := 3) (hp := by norm_num) (hp2 := by decide)
      (d := 4) (w := owR34_wA5) (c := 1) (hc := by decide) t).mp ht
    obtain ⟨a, ha, hform⟩ := ht'
    have hnorm : owR34_QA5 a = 1 := by
      rw [owR34_QA5]
      simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
      exact ha
    have hQa : owR34_QA5 a ≠ 0 := by rw [hnorm]; decide
    have ht_eq : t = owR34_rA5 a hQa := by
      ext v
      rw [hform v, owR34_rA5_apply, owR34_polarA5, hnorm, div_one]
      ring_nf
    rw [ht_eq]
    rcases owR34_coverA5 a ha with ⟨k, hk | hk⟩
    · rw [owR34_rA5_congr _ _ _ _ hk]
      exact owR34_XA5_mem k
    · rw [owR34_rA5_congr _ _ _ _ hk]
      exact (owR34_rA5_neg_eq k) ▸ owR34_XA5_mem k

theorem owR34_A5_linWeyl :
    @LinWeyl 3 (Fin 4 → ZMod 3) (Pi.addCommGroup)
      (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_AA5 :=
  @owTA_linWeyl_of_typeA 3 (by norm_num) (by decide) (Fin 4 → ZMod 3) (Pi.addCommGroup)
    (Pi.Function.module (Fin 4) (ZMod 3) (ZMod 3)) owR34_QA5 1 owR34_AA5 5 (by norm_num)
    owR34_aA5 owR34_alphaA5 owR34_hP_A5 owR34_sA5 owR34_hs_A5 owR34_hs_mem_A5 owR34_hgen_A5

end CFSG.StandardType.ZS

end
