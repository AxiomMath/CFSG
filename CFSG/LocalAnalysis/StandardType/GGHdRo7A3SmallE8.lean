module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallBasic
import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
  {θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V} {z : V}

private def hdRo7A9E8Aux_H (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V) : Fin 8 → V :=
  ![θ (a9E 0 1), -(θ a9T + z), θ (a9E 1 2), θ (a9E 2 3), θ (a9E 3 4),
    θ (a9E 4 5), θ (a9E 5 6), θ (a9E 6 7)]

private def hdRo7A9E8Aux_A (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : Fin 8 → Module.Dual (ZMod 3) V :=
  ![ψ 0, -φ, ψ 1, ψ 2, ψ 3, ψ 4, ψ 5, ψ 6]

private lemma hdRo7A9E8Aux_H_zero : hdRo7A9E8Aux_H θ z 0 = θ (a9E 0 1) := rfl
private lemma hdRo7A9E8Aux_H_one : hdRo7A9E8Aux_H θ z 1 = -(θ a9T + z) := rfl
private lemma hdRo7A9E8Aux_H_two : hdRo7A9E8Aux_H θ z 2 = θ (a9E 1 2) := rfl
private lemma hdRo7A9E8Aux_H_three : hdRo7A9E8Aux_H θ z 3 = θ (a9E 2 3) := rfl
private lemma hdRo7A9E8Aux_H_four : hdRo7A9E8Aux_H θ z 4 = θ (a9E 3 4) := rfl
private lemma hdRo7A9E8Aux_H_five : hdRo7A9E8Aux_H θ z 5 = θ (a9E 4 5) := rfl
private lemma hdRo7A9E8Aux_H_six : hdRo7A9E8Aux_H θ z 6 = θ (a9E 5 6) := rfl
private lemma hdRo7A9E8Aux_H_seven : hdRo7A9E8Aux_H θ z 7 = θ (a9E 6 7) := rfl

private lemma hdRo7A9E8Aux_A_zero (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 0 = ψ 0 := rfl
private lemma hdRo7A9E8Aux_A_one (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 1 = -φ := rfl
private lemma hdRo7A9E8Aux_A_two (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 2 = ψ 1 := rfl
private lemma hdRo7A9E8Aux_A_three (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 3 = ψ 2 := rfl
private lemma hdRo7A9E8Aux_A_four (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 4 = ψ 3 := rfl
private lemma hdRo7A9E8Aux_A_five (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 5 = ψ 4 := rfl
private lemma hdRo7A9E8Aux_A_six (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 6 = ψ 5 := rfl
private lemma hdRo7A9E8Aux_A_seven (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V) : hdRo7A9E8Aux_A φ ψ 7 = ψ 6 := rfl

private lemma hdRo7A9E8Aux_a9T_mem : a9T ∈ a3Aug 3 9 := by
  rw [mem_a3Aug]
  decide

private lemma hdRo7A9E8Aux_psi_E (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ)
    (k : Fin 8) (i j : Fin 9) :
    ψ k (θ (a9E i j)) = a9E i j k.castSucc - a9E i j k.succ :=
  hψu k _ (a9E_mem i j)

private lemma hdRo7A9E8Aux_psi_T (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ) (k : Fin 8) :
    ψ k (θ a9T) = a9T k.castSucc - a9T k.succ :=
  hψu k _ hdRo7A9E8Aux_a9T_mem

private lemma hdRo7A9E8Aux_psi_neg (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ)
    (hψz : ∀ k, ψ k z = 0) (k : Fin 8) :
    ψ k (-(θ a9T + z)) = -(a9T k.castSucc - a9T k.succ) := by
  rw [map_neg, map_add, hdRo7A9E8Aux_psi_T ψ hψu k, hψz k, add_zero]

private lemma hdRo7A9E8Aux_phi_E (φ : Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2) (i j : Fin 9) :
    φ (θ (a9E i j)) = ∑ k, a9T k * a9E i j k := by
  have h := hφ (a9E i j) (a9E_mem i j) 0
  simpa using h

private lemma hdRo7A9E8Aux_phi_neg_E (φ : Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2) (i j : Fin 9) :
    (-φ) (θ (a9E i j)) = -(∑ k, a9T k * a9E i j k) := by
  rw [LinearMap.neg_apply, hdRo7A9E8Aux_phi_E φ hφ]

private lemma hdRo7A9E8Aux_phi_T' (φ : Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2) :
    φ (θ a9T + z) = 2 := by
  have h := hφ a9T hdRo7A9E8Aux_a9T_mem 1
  have h2 : (∑ i, a9T i * a9T i) + (1 : ZMod 3) * 2 = 2 := by decide
  simpa only [one_smul, one_mul] using h.trans h2

private lemma hdRo7A9E8Aux_phi_neg_T (φ : Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2) :
    (-φ) (-(θ a9T + z)) = 2 := by
  rw [LinearMap.neg_apply, map_neg, neg_neg, hdRo7A9E8Aux_phi_T' φ hφ]

private lemma hdRo7A9E8Aux_hα (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ) (i : Fin 8) :
    hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z i) = 2 := by
  have hi : ∀ i : Fin 8, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    decide
  rcases hi i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [hdRo7A9E8Aux_A_zero, hdRo7A9E8Aux_A_one, hdRo7A9E8Aux_A_two,
      hdRo7A9E8Aux_A_three, hdRo7A9E8Aux_A_four, hdRo7A9E8Aux_A_five,
      hdRo7A9E8Aux_A_six, hdRo7A9E8Aux_A_seven, hdRo7A9E8Aux_H_zero,
      hdRo7A9E8Aux_H_one, hdRo7A9E8Aux_H_two, hdRo7A9E8Aux_H_three,
      hdRo7A9E8Aux_H_four, hdRo7A9E8Aux_H_five, hdRo7A9E8Aux_H_six,
      hdRo7A9E8Aux_H_seven] <;>
    first
      | (rw [hdRo7A9E8Aux_psi_E ψ hψu]; decide)
      | rw [hdRo7A9E8Aux_phi_neg_T φ hφ]

private lemma hdRo7A9E8Aux_hP (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ)
    (hψz : ∀ k, ψ k z = 0) (i j : Fin 8) :
    hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
  have hi : ∀ i : Fin 8, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
    decide
  rcases hi i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hi j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [hdRo7A9E8Aux_A_zero, hdRo7A9E8Aux_A_one, hdRo7A9E8Aux_A_two,
      hdRo7A9E8Aux_A_three, hdRo7A9E8Aux_A_four, hdRo7A9E8Aux_A_five,
      hdRo7A9E8Aux_A_six, hdRo7A9E8Aux_A_seven, hdRo7A9E8Aux_H_zero,
      hdRo7A9E8Aux_H_one, hdRo7A9E8Aux_H_two, hdRo7A9E8Aux_H_three,
      hdRo7A9E8Aux_H_four, hdRo7A9E8Aux_H_five, hdRo7A9E8Aux_H_six,
      hdRo7A9E8Aux_H_seven] <;>
    first
      | (rw [hdRo7A9E8Aux_psi_E ψ hψu]; rw [CartanMatrix.E_eight_eq]; decide)
      | (rw [hdRo7A9E8Aux_psi_neg ψ hψu hψz]; rw [CartanMatrix.E_eight_eq]; decide)
      | (rw [hdRo7A9E8Aux_phi_neg_E φ hφ]; rw [CartanMatrix.E_eight_eq]; decide)
      | (rw [hdRo7A9E8Aux_phi_neg_T φ hφ]; rw [CartanMatrix.E_eight_eq]; decide)


private def hdRo7A9E8Aux_C : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  (CartanMatrix.E 8).map (Int.castRingHom (ZMod 3))

private def hdRo7A9E8Aux_Cinv : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  ![![1, 2, 1, 1, 2, 0, 1, 2],
    ![2, 2, 1, 0, 0, 0, 0, 0],
    ![1, 1, 2, 2, 1, 0, 2, 1],
    ![1, 0, 2, 0, 0, 0, 0, 0],
    ![2, 0, 1, 0, 2, 0, 1, 2],
    ![0, 0, 0, 0, 0, 0, 2, 1],
    ![1, 0, 2, 0, 1, 2, 0, 0],
    ![2, 0, 1, 0, 2, 1, 0, 2]]

private lemma hdRo7A9E8Aux_Cinv_mul : hdRo7A9E8Aux_Cinv * hdRo7A9E8Aux_C = 1 := by decide

private lemma hdRo7A9E8Aux_linIndep (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hP : ∀ i j, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) :
    LinearIndependent (ZMod 3) (hdRo7A9E8Aux_H θ z) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hC : hdRo7A9E8Aux_C.mulVec g = 0 := by
    ext i
    have h := congrArg (hdRo7A9E8Aux_A φ ψ i) hg
    rw [map_sum, map_zero] at h
    have h' : ∑ j, g j * hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) = 0 := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    have h'' : ∑ j, g j * ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) = 0 := by
      rw [← h']
      apply Finset.sum_congr rfl
      intro j _
      rw [hP]
    rw [Matrix.mulVec_apply, dotProduct]
    simpa [hdRo7A9E8Aux_C, Matrix.map_apply, mul_comm] using h''
  have h1 : hdRo7A9E8Aux_Cinv.mulVec (hdRo7A9E8Aux_C.mulVec g) = 0 := by
    rw [hC, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, hdRo7A9E8Aux_Cinv_mul, Matrix.one_mulVec] at h1
  exact congrFun h1 i

private noncomputable def hdRo7A9E8Aux_L (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hα : ∀ i, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z i) = 2)
    (hP : ∀ i j, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) :
    CoxeterMatrix.E₈.Group →* (V ≃ₗ[ZMod 3] V) :=
  CoxeterMatrix.E₈.toCoxeterSystem.lift
    ⟨fun i => Module.reflection (hα i),
      isLiftable_reflection_of_intCartan ggIntCartan_E₈ (hdRo7A9E8Aux_H θ z)
        (hdRo7A9E8Aux_A φ ψ) hα hP⟩

private lemma hdRo7A9E8Aux_L_simple (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hα : ∀ i, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z i) = 2)
    (hP : ∀ i j, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) (i : Fin 8) :
    hdRo7A9E8Aux_L φ ψ hα hP (CoxeterMatrix.E₈.simple i) = Module.reflection (hα i) := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple, hdRo7A9E8Aux_L, CoxeterSystem.lift_apply_simple]

private lemma hdRo7A9E8Aux_L_range (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hα : ∀ i, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z i) = 2)
    (hP : ∀ i j, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) :
    (hdRo7A9E8Aux_L φ ψ hα hP).range =
      Subgroup.closure (Set.range fun i => Module.reflection (hα i)) := by
  rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₈.toCoxeterSystem.subgroup_closure_range_simple,
    MonoidHom.map_closure, ← Set.range_comp]
  congr 1

private lemma hdRo7A9E8Aux_L_inj (φ : Module.Dual (ZMod 3) V)
    (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (hα : ∀ i, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z i) = 2)
    (hP : ∀ i j, hdRo7A9E8Aux_A φ ψ i (hdRo7A9E8Aux_H θ z j) =
      ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) :
    Function.Injective (hdRo7A9E8Aux_L φ ψ hα hP) := by
  have hFT : TauCeti.IsFiniteType (CartanMatrix.E 8) := by
    have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
    rwa [TauCeti.DynkinType.cartanMatrix_E8] at h
  exact ggCartanFaithful_of_isFiniteType (p := 3) (hα := hα) (hP := hP) (by decide) hFT
    ggIntCartan_E₈ (hdRo7A9E8Aux_linIndep φ ψ hP)


private def hdRo7A9E8Aux_letters : List (Fin 8) :=
  [6, 5, 4, 3, 2, 7, 1, 2, 3, 0, 1, 2, 7, 4, 5, 3, 4, 2, 3, 1, 2, 7, 6, 5, 4, 3, 2, 1]

private def hdRo7A9E8Aux_word : List (Fin 8) :=
  hdRo7A9E8Aux_letters ++ [0] ++ hdRo7A9E8Aux_letters.reverse

private lemma hdRo7A9E8Aux_word_eq :
    hdRo7A9E8Aux_word =
      [6, 5, 4, 3, 2, 7, 1, 2, 3, 0, 1, 2, 7, 4, 5, 3, 4, 2, 3, 1, 2, 7, 6, 5, 4, 3, 2, 1,
       0, 1, 2, 3, 4, 5, 6, 7, 2, 1, 3, 2, 4, 3, 5, 4, 7, 2, 1, 0, 3, 2, 1, 7, 2, 3, 4, 5, 6] :=
  rfl

private def hdRo7A9E8Aux_letterMap (i : Fin 8) :
    (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3 :=
  if i.val < 7 then a9Perm (Equiv.swap i.castSucc i.succ) else a9Act a9T a9T 2

private def hdRo7A9E8Aux_compMap (l : List (Fin 8)) :
    (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3 :=
  l.foldr (fun i acc => hdRo7A9E8Aux_letterMap i ∘ acc) id

private noncomputable def hdRo7A9E8Aux_gen (t : Fin 8 → V ≃ₗ[ZMod 3] V)
    (r : V ≃ₗ[ZMod 3] V) (i : Fin 8) : V ≃ₗ[ZMod 3] V :=
  if i.val < 7 then t i else r

private noncomputable def hdRo7A9E8Aux_elt (t : Fin 8 → V ≃ₗ[ZMod 3] V)
    (r : V ≃ₗ[ZMod 3] V) (l : List (Fin 8)) : V ≃ₗ[ZMod 3] V :=
  (l.map (hdRo7A9E8Aux_gen t r)).prod

private lemma hdRo7A9E8Aux_letterMap_mem (i : Fin 8)
    {v : (Fin 9 → ZMod 3) × ZMod 3} (hv : v.1 ∈ a3Aug 3 9) :
    (hdRo7A9E8Aux_letterMap i v).1 ∈ a3Aug 3 9 := by
  unfold hdRo7A9E8Aux_letterMap
  split_ifs with h
  · exact a9Perm_mem _ hv
  · exact a9Act_mem (hh := a9T) (f := a9T) (d := 2) hdRo7A9E8Aux_a9T_mem hv

private lemma hdRo7A9E8Aux_compMap_mem (l : List (Fin 8))
    {v : (Fin 9 → ZMod 3) × ZMod 3} (hv : v.1 ∈ a3Aug 3 9) :
    (hdRo7A9E8Aux_compMap l v).1 ∈ a3Aug 3 9 := by
  induction l with
  | nil => simpa [hdRo7A9E8Aux_compMap] using hv
  | cons a l ih =>
      simp only [hdRo7A9E8Aux_compMap, List.foldr_cons, Function.comp_apply]
      exact hdRo7A9E8Aux_letterMap_mem a ih

private lemma hdRo7A9E8Aux_gen_lift (t : Fin 8 → V ≃ₗ[ZMod 3] V)
    (ht : ∀ k, ∀ u ∈ a3Aug 3 9,
      t k (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i)))
    (htz : ∀ k, t k z = z) (r : V ≃ₗ[ZMod 3] V) (hr : A9Real θ z a9T a9T 2 r)
    (i : Fin 8) :
    A9Lift θ z (hdRo7A9E8Aux_gen t r i) (hdRo7A9E8Aux_letterMap i) := by
  by_cases h : i.val < 7
  · rw [show hdRo7A9E8Aux_gen t r i = t i from by
        unfold hdRo7A9E8Aux_gen; rw [if_pos h],
      show hdRo7A9E8Aux_letterMap i = a9Perm (Equiv.swap i.castSucc i.succ) from by
        unfold hdRo7A9E8Aux_letterMap; rw [if_pos h]]
    exact a9Lift_perm (ht i) (htz i)
  · rw [show hdRo7A9E8Aux_gen t r i = r from by
        unfold hdRo7A9E8Aux_gen; rw [if_neg h],
      show hdRo7A9E8Aux_letterMap i = a9Act a9T a9T 2 from by
        unfold hdRo7A9E8Aux_letterMap; rw [if_neg h]]
    exact hr

private lemma hdRo7A9E8Aux_lift_elt (t : Fin 8 → V ≃ₗ[ZMod 3] V)
    (ht : ∀ k, ∀ u ∈ a3Aug 3 9,
      t k (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i)))
    (htz : ∀ k, t k z = z) (r : V ≃ₗ[ZMod 3] V) (hr : A9Real θ z a9T a9T 2 r)
    (l : List (Fin 8)) :
    A9Lift θ z (hdRo7A9E8Aux_elt t r l) (hdRo7A9E8Aux_compMap l) := by
  induction l with
  | nil =>
      intro u hu c
      simp [hdRo7A9E8Aux_elt, hdRo7A9E8Aux_compMap]
  | cons a l ih =>
      simp only [hdRo7A9E8Aux_elt, List.map_cons, List.prod_cons, hdRo7A9E8Aux_compMap,
        List.foldr_cons]
      exact a9Lift_mul (hdRo7A9E8Aux_gen_lift t ht htz r hr a) ih
        (fun u hu c => hdRo7A9E8Aux_compMap_mem l hu)

private lemma hdRo7A9E8Aux_word_check :
    (∀ i : Fin 9,
      (hdRo7A9E8Aux_compMap hdRo7A9E8Aux_word (a9E i 8, 0)).2 =
          (a9Perm (Equiv.swap 7 8) (a9E i 8, 0)).2 ∧
        a9Const ((hdRo7A9E8Aux_compMap hdRo7A9E8Aux_word (a9E i 8, 0)).1 -
          (a9Perm (Equiv.swap 7 8) (a9E i 8, 0)).1)) ∧
      (hdRo7A9E8Aux_compMap hdRo7A9E8Aux_word (0, 1)).2 =
          (a9Perm (Equiv.swap 7 8) (0, 1)).2 ∧
        a9Const ((hdRo7A9E8Aux_compMap hdRo7A9E8Aux_word (0, 1)).1 -
          (a9Perm (Equiv.swap 7 8) (0, 1)).1) := by
  rw [hdRo7A9E8Aux_word_eq]
  decide +kernel

private lemma hdRo7A9E8Aux_eq_word (hfr : A3Frame 3 9 θ z)
    (hM : θ (fun _ => 1) = 0) (t : Fin 8 → V ≃ₗ[ZMod 3] V)
    (ht : ∀ k, ∀ u ∈ a3Aug 3 9,
      t k (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i)))
    (htz : ∀ k, t k z = z) (r : V ≃ₗ[ZMod 3] V) (hr : A9Real θ z a9T a9T 2 r)
    {a : V ≃ₗ[ZMod 3] V}
    (ha : ∀ u ∈ a3Aug 3 9, a (θ u) = θ (fun i => u ((Equiv.swap (7 : Fin 9) 8).symm i)))
    (haz : a z = z) :
    a = hdRo7A9E8Aux_elt t r hdRo7A9E8Aux_word := by
  refine (a9_eq_of_lift hfr hM (hdRo7A9E8Aux_lift_elt t ht htz r hr hdRo7A9E8Aux_word)
    (a9Lift_perm ha haz) ?_ ?_).symm
  · intro i
    exact (hdRo7A9E8Aux_word_check.1 i)
  · exact hdRo7A9E8Aux_word_check.2

private theorem hdRo7A9E8Aux_linWeyl (hfr : A3Frame 3 9 θ z)
    (hM : θ (fun _ => 1) = 0) (φ : Module.Dual (ZMod 3) V)
    (hφ : ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3,
      φ (θ u + c • z) = ∑ i, a9T i * u i + c * 2)
    (t : Fin 8 → V ≃ₗ[ZMod 3] V) (ψ : Fin 8 → Module.Dual (ZMod 3) V)
    (ht : ∀ k, ∀ u ∈ a3Aug 3 9,
      t k (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i)))
    (htz : ∀ k, t k z = z)
    (hψu : ∀ k, ∀ u ∈ a3Aug 3 9, ψ k (θ u) = u k.castSucc - u k.succ)
    (hψz : ∀ k, ψ k z = 0)
    (htform : ∀ k, ∀ v, t k v = v - ψ k v • θ (a9E k.castSucc k.succ))
    (r : V ≃ₗ[ZMod 3] V) (hr : A9Real θ z a9T a9T 2 r)
    (hrform : ∀ v, r v = v - φ v • (θ a9T + z)) :
    ZS.LinWeyl 3 (Subgroup.closure ({a | A3P 3 9 θ z a} ∪ {r})) := by
  have hα := hdRo7A9E8Aux_hα φ ψ hφ hψu
  have hP := hdRo7A9E8Aux_hP φ ψ hφ hψu hψz
  let Phi : Fin 8 → V ≃ₗ[ZMod 3] V := fun i => Module.reflection (hα i)
  have hPhi_apply : ∀ i v,
      Phi i v = v - hdRo7A9E8Aux_A φ ψ i v • hdRo7A9E8Aux_H θ z i := by
    intro i v
    dsimp only [Phi]
    rw [Module.reflection_apply]
  have hPhi_zero : Phi 0 = t 0 := by
    ext v
    rw [hPhi_apply 0 v, htform 0 v, hdRo7A9E8Aux_A_zero, hdRo7A9E8Aux_H_zero]
    rfl
  have hPhi_one : Phi 1 = r := by
    ext v
    rw [hPhi_apply 1 v, hrform v, hdRo7A9E8Aux_A_one, hdRo7A9E8Aux_H_one]
    rw [LinearMap.neg_apply, neg_smul, smul_neg, neg_neg]
  have hPhi_two : Phi 2 = t 1 := by
    ext v
    rw [hPhi_apply 2 v, htform 1 v, hdRo7A9E8Aux_A_two, hdRo7A9E8Aux_H_two]
    rfl
  have hPhi_three : Phi 3 = t 2 := by
    ext v
    rw [hPhi_apply 3 v, htform 2 v, hdRo7A9E8Aux_A_three, hdRo7A9E8Aux_H_three]
    rfl
  have hPhi_four : Phi 4 = t 3 := by
    ext v
    rw [hPhi_apply 4 v, htform 3 v, hdRo7A9E8Aux_A_four, hdRo7A9E8Aux_H_four]
    rfl
  have hPhi_five : Phi 5 = t 4 := by
    ext v
    rw [hPhi_apply 5 v, htform 4 v, hdRo7A9E8Aux_A_five, hdRo7A9E8Aux_H_five]
    rfl
  have hPhi_six : Phi 6 = t 5 := by
    ext v
    rw [hPhi_apply 6 v, htform 5 v, hdRo7A9E8Aux_A_six, hdRo7A9E8Aux_H_six]
    rfl
  have hPhi_seven : Phi 7 = t 6 := by
    ext v
    rw [hPhi_apply 7 v, htform 6 v, hdRo7A9E8Aux_A_seven, hdRo7A9E8Aux_H_seven]
    rfl
  let K := Subgroup.closure ({a | A3P 3 9 θ z a} ∪ {r})
  have hr_mem : r ∈ Subgroup.closure (Set.range Phi) :=
    Subgroup.subset_closure ⟨1, hPhi_one⟩
  have ht_mem : ∀ k : Fin 8, k.val < 7 → t k ∈ Subgroup.closure (Set.range Phi) := by
    intro k hk
    fin_cases k
    · exact Subgroup.subset_closure ⟨0, hPhi_zero⟩
    · exact Subgroup.subset_closure ⟨2, hPhi_two⟩
    · exact Subgroup.subset_closure ⟨3, hPhi_three⟩
    · exact Subgroup.subset_closure ⟨4, hPhi_four⟩
    · exact Subgroup.subset_closure ⟨5, hPhi_five⟩
    · exact Subgroup.subset_closure ⟨6, hPhi_six⟩
    · exact Subgroup.subset_closure ⟨7, hPhi_seven⟩
    · simp_all
  have hgen_mem : ∀ i : Fin 8,
      hdRo7A9E8Aux_gen t r i ∈ Subgroup.closure (Set.range Phi) := by
    intro i
    by_cases h : i.val < 7
    · rw [show hdRo7A9E8Aux_gen t r i = t i from by
        unfold hdRo7A9E8Aux_gen; rw [if_pos h]]
      exact ht_mem i h
    · rw [show hdRo7A9E8Aux_gen t r i = r from by
        unfold hdRo7A9E8Aux_gen; rw [if_neg h]]
      exact hr_mem
  have helt_mem : ∀ l : List (Fin 8),
      hdRo7A9E8Aux_elt t r l ∈ Subgroup.closure (Set.range Phi) := by
    intro l
    induction l with
    | nil => exact Subgroup.one_mem _
    | cons a l ih =>
        rw [show hdRo7A9E8Aux_elt t r (a :: l) =
            hdRo7A9E8Aux_gen t r a * hdRo7A9E8Aux_elt t r l from by
          simp [hdRo7A9E8Aux_elt]]
        exact Subgroup.mul_mem _ (hgen_mem a) ih
  have hPhi_in_K : ∀ i, Phi i ∈ K := by
    intro i
    fin_cases i
    · rw [hPhi_zero]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 0, htz 0⟩)
    · rw [hPhi_one]
      exact Subgroup.subset_closure (Or.inr rfl)
    · rw [hPhi_two]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 1, htz 1⟩)
    · rw [hPhi_three]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 2, htz 2⟩)
    · rw [hPhi_four]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 3, htz 3⟩)
    · rw [hPhi_five]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 4, htz 4⟩)
    · rw [hPhi_six]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 5, htz 5⟩)
    · rw [hPhi_seven]
      exact Subgroup.subset_closure (Or.inl ⟨_, ht 6, htz 6⟩)
  have hKgen : ∀ k : Fin 8, ∀ a : V ≃ₗ[ZMod 3] V,
      (∀ u ∈ a3Aug 3 9,
        a (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i))) →
      a z = z → a ∈ Subgroup.closure (Set.range Phi) := by
    intro k a ha haz
    by_cases hk : k.val < 7
    · rw [a3P_ext hfr ha haz (ht k) (htz k)]
      exact ht_mem k hk
    · have hk7 : k = 7 := by
        have h := k.isLt
        exact Fin.ext (by omega)
      subst hk7
      rw [hdRo7A9E8Aux_eq_word hfr hM t ht htz r hr (by simpa using ha) haz]
      exact helt_mem hdRo7A9E8Aux_word
  have hcl_eq : Subgroup.closure (Set.range Phi) = K := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hPhi_in_K i
    · rw [Subgroup.closure_le]
      rintro a (ha | ha)
      · exact a9_P_le hfr (Subgroup.closure (Set.range Phi)) hKgen a ha
      · rw [Set.mem_singleton_iff] at ha
        subst ha
        exact hr_mem
  let F : CoxeterMatrix.E₈.Group →* ↥K :=
    { toFun := fun x => ⟨hdRo7A9E8Aux_L φ ψ hα hP x, by
        rw [show K = (hdRo7A9E8Aux_L φ ψ hα hP).range from
          (hdRo7A9E8Aux_L_range φ ψ hα hP).trans hcl_eq |>.symm]
        exact ⟨x, rfl⟩⟩
      map_one' := by ext; simp [hdRo7A9E8Aux_L]
      map_mul' x y := by ext; simp [hdRo7A9E8Aux_L] }
  have hF_inj : Function.Injective F := by
    intro x y h
    exact hdRo7A9E8Aux_L_inj φ ψ hα hP (congrArg Subtype.val h)
  have hF_surj : Function.Surjective F := by
    intro a
    have ha : (a : V ≃ₗ[ZMod 3] V) ∈ (hdRo7A9E8Aux_L φ ψ hα hP).range := by
      rw [hdRo7A9E8Aux_L_range, hcl_eq]
      exact a.2
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨Fin 8, CoxeterMatrix.E₈,
    GGIsWeylMatrixE.isWeylMatrix
      (Or.inr (Or.inr ⟨Equiv.refl _, by ext i j; rfl⟩)), ?_⟩
  have hF_bij : Function.Bijective F := ⟨hF_inj, hF_surj⟩
  refine ⟨MulEquiv.ofBijective F hF_bij, ?_⟩
  intro i
  rw [MulEquiv.ofBijective_apply]
  have hcoe : ((F (CoxeterMatrix.E₈.simple i) : ↥K) : V ≃ₗ[ZMod 3] V) =
      Module.reflection (hα i) := by
    change hdRo7A9E8Aux_L φ ψ hα hP (CoxeterMatrix.E₈.simple i) = Module.reflection (hα i)
    exact hdRo7A9E8Aux_L_simple φ ψ hα hP i
  rw [hcoe]
  exact CFSG.StandardType.ZS.isRefl_reflection (p := 3) (by decide) (hα i)

theorem a9_e8_holds : A9E8Leaf := by
  intro V _ _ θ z hfr hM r hr
  obtain ⟨φ, hφ, hrform⟩ :=
    a9Real_fun hfr hM (f := a9T) (d := 2) (by decide) hr
  have htransp : ∀ k : Fin 8, ∃ (t : V ≃ₗ[ZMod 3] V) (ψ : Module.Dual (ZMod 3) V),
      (∀ u ∈ a3Aug 3 9,
        t (θ u) = θ (fun i => u ((Equiv.swap k.castSucc k.succ).symm i))) ∧
      t z = z ∧ (∀ u ∈ a3Aug 3 9, ψ (θ u) = u k.castSucc - u k.succ) ∧ ψ z = 0 ∧
      (∀ v, t v = v - ψ v • θ (a9E k.castSucc k.succ)) ∧ GGLinRefl t := by
    intro k
    exact a3_transp (p := 3) (m := 9) (V := V) rfl hfr (by decide) (by decide)
      (i := k.castSucc) (j := k.succ) (by
        intro h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega)
  choose t ψ ht htz hψu hψz htform htRefl using htransp
  exact hdRo7A9E8Aux_linWeyl hfr hM φ hφ t ψ ht htz hψu hψz htform r hr hrform

end CFSG.StandardType.HdRo7A3.Small
