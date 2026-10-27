module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.RankThree.PartOne.K159H.O3Basic

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module
open scoped MatrixGroups

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}

@[expose] def phiFun (a b : Fin r ⊕ Fin r) (g : Matrix (Fin 2) (Fin 2) K) (x : Fin r ⊕ Fin r → K) :
    Fin r ⊕ Fin r → K := fun c =>
  if c = a then g 0 0 * x a + g 0 1 * x b
  else if c = b then g 1 0 * x a + g 1 1 * x b
  else if c = a.swap then g 1 1 * x a.swap + g 1 0 * x b.swap
  else if c = b.swap then g 0 1 * x a.swap + g 0 0 * x b.swap
  else x c

@[expose] def phi (a b : Fin r ⊕ Fin r) (g : Matrix (Fin 2) (Fin 2) K) :
    ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun v := (phiFun a b g v.1, v.2)
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) rfl
    simp only [phiFun, Prod.fst_add, Pi.add_apply]
    split_ifs <;> ring
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) rfl
    simp only [phiFun, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem phi_fst (a b : Fin r ⊕ Fin r) (g : Matrix (Fin 2) (Fin 2) K) (v : (Fin r ⊕ Fin r → K) × A) :
    (phi a b g v).1 = phiFun a b g v.1 := rfl

theorem phi_snd (a b : Fin r ⊕ Fin r) (g : Matrix (Fin 2) (Fin 2) K) (v : (Fin r ⊕ Fin r → K) × A) :
    (phi a b g v).2 = v.2 := rfl

theorem phi_one (a b : Fin r ⊕ Fin r) : phi (A := A) a b (1 : Matrix (Fin 2) (Fin 2) K) = LinearMap.id := by
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  simp only [phi_fst, phiFun, LinearMap.id_apply]
  split_ifs with h1 h2 h3 h4
  · subst h1; simp
  · subst h2; simp
  · subst h3; simp
  · subst h4; simp
  · rfl

theorem swap_ne_self'' (c : Fin r ⊕ Fin r) : c.swap ≠ c := by
  rcases c with k | k <;> simp

section Distinct

variable {a b : Fin r ⊕ Fin r}

theorem ne_of_coordIdx' (h : coordIdx a ≠ coordIdx b) : a ≠ b := fun e => h (by rw [e])

theorem ne_swap_of_coordIdx' (h : coordIdx a ≠ coordIdx b) : a ≠ b.swap := fun e => h (by rw [e, coordIdx_swap])

end Distinct

theorem phi_mul {a b : Fin r ⊕ Fin r} (hab : coordIdx a ≠ coordIdx b) (g h : Matrix (Fin 2) (Fin 2) K) :
    phi (A := A) a b (g * h) = phi a b g ∘ₗ phi a b h := by
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h2 : a.swap ≠ a := swap_ne_self'' a
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h3' : b.swap ≠ a := h3.symm
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h4' : a.swap ≠ b := h4.symm
  have h5' : b ≠ b.swap := (swap_ne_self'' b).symm
  have h5 : b.swap ≠ b := swap_ne_self'' b
  have h6 : a.swap ≠ b.swap := fun e => h1 (by simpa using congrArg Sum.swap e)
  have h6' : b.swap ≠ a.swap := h6.symm
  refine LinearMap.ext fun v => Prod.ext (funext fun c => ?_) rfl
  simp only [LinearMap.comp_apply, phi_fst, phiFun, Matrix.mul_apply, Fin.sum_univ_two]
  by_cases ca : c = a
  · rw [ca]
    simp [*]
    ring
  by_cases cb : c = b
  · rw [cb]
    simp [*]
    ring
  by_cases cas : c = a.swap
  · rw [cas]
    simp [*]
    ring
  by_cases cbs : c = b.swap
  · rw [cbs]
    simp [*]
    ring
  simp [ca, cb, cas, cbs]


section Hom

variable [CharP K 2] {a b : Fin r ⊕ Fin r}

theorem rEl_eq_phi_upper (qA : QuadraticForm K A) (hab : coordIdx a ≠ coordIdx b) (t : K) :
    ((rEl qA t a b : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      phi a b !![1, t; 0, 1] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h2'' : a.swap ≠ a := swap_ne_self'' a
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h3' : b.swap ≠ a := h3.symm
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h4' : a.swap ≠ b := h4.symm
  have h5' : b ≠ b.swap := (swap_ne_self'' b).symm
  have h5 : b.swap ≠ b := swap_ne_self'' b
  have h6 : a.swap ≠ b.swap := fun e => h1 (by simpa using congrArg Sum.swap e)
  have h6' : b.swap ≠ a.swap := h6.symm
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, rEl_apply qA hab]
  refine Prod.ext (funext fun c => ?_) ?_
  · simp only [Prod.fst_sub, Prod.fst_add, Pi.sub_apply, Pi.add_apply, Prod.smul_fst, Pi.smul_apply, hypVec_fst,
      smul_eq_mul, phi_fst, phiFun]
    by_cases ca : c = a
    · rw [ca]; simp [*]; try ring
    by_cases cb : c = b
    · rw [cb]; simp [*]; try ring
    by_cases cas : c = a.swap
    · rw [cas]; simp [*]; try ring
    by_cases cbs : c = b.swap
    · rw [cbs]; simp [*]
      linear_combination (-(t * v.1 a.swap)) * h2
    simp [ca, cb, cas, cbs]
  · simp [hypVec_snd, phi_snd]

theorem rEl_eq_phi_lower (qA : QuadraticForm K A) (hab : coordIdx a ≠ coordIdx b) (t : K) :
    ((rEl qA t b a : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
      ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
      phi a b !![1, 0; t, 1] := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h2'' : a.swap ≠ a := swap_ne_self'' a
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h3' : b.swap ≠ a := h3.symm
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  have h4' : a.swap ≠ b := h4.symm
  have h5' : b ≠ b.swap := (swap_ne_self'' b).symm
  have h5 : b.swap ≠ b := swap_ne_self'' b
  have h6 : a.swap ≠ b.swap := fun e => h1 (by simpa using congrArg Sum.swap e)
  have h6' : b.swap ≠ a.swap := h6.symm
  refine LinearMap.ext fun v => ?_
  rw [LinearEquiv.coe_coe, rEl_apply qA hab.symm]
  refine Prod.ext (funext fun c => ?_) ?_
  · simp only [Prod.fst_sub, Prod.fst_add, Pi.sub_apply, Pi.add_apply, Prod.smul_fst, Pi.smul_apply, hypVec_fst,
      smul_eq_mul, phi_fst, phiFun]
    by_cases ca : c = a
    · rw [ca]; simp [*]; try ring
    by_cases cb : c = b
    · rw [cb]; simp [*]; try ring
    by_cases cas : c = a.swap
    · rw [cas]; simp [*]
      linear_combination (-(t * v.1 b.swap)) * h2
    by_cases cbs : c = b.swap
    · rw [cbs]; simp [*]
    simp [ca, cb, cas, cbs]
  · simp [hypVec_snd, phi_snd]


@[expose] def PhiE (hab : coordIdx a ≠ coordIdx b) (g : SL(2, K)) :
    ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) :=
  LinearEquiv.ofLinearMap (phi a b g.1) (phi a b (g⁻¹).1)
    (by
      rw [← phi_mul hab, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, phi_one])
    (by
      rw [← phi_mul hab, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, phi_one])

omit [CharP K 2] in
theorem PhiE_apply (hab : coordIdx a ≠ coordIdx b) (g : SL(2, K)) (v : (Fin r ⊕ Fin r → K) × A) :
    PhiE hab g v = phi a b g.1 v := rfl

@[expose] def PhiH (hab : coordIdx a ≠ coordIdx b) :
    SL(2, K) →* ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A) where
  toFun := PhiE hab
  map_one' := LinearEquiv.ext fun v => by
    rw [PhiE_apply, Matrix.SpecialLinearGroup.coe_one, phi_one]
    rfl
  map_mul' g h := LinearEquiv.ext fun v => by
    rw [PhiE_apply, Matrix.SpecialLinearGroup.coe_mul, phi_mul hab, LinearEquiv.mul_apply, PhiE_apply, PhiE_apply]
    rfl

theorem PhiH_apply (hab : coordIdx a ≠ coordIdx b) (g : SL(2, K)) (v : (Fin r ⊕ Fin r → K) × A) :
    PhiH hab g v = phi a b g.1 v := rfl

theorem PhiH_injective (hab : coordIdx a ≠ coordIdx b) : Function.Injective (PhiH (K := K) (A := A) hab) := by
  have h1 : a ≠ b := ne_of_coordIdx' hab
  have h1' : b ≠ a := h1.symm
  have h2' : a ≠ a.swap := (swap_ne_self'' a).symm
  have h3 : a ≠ b.swap := ne_swap_of_coordIdx' hab
  have h4 : b ≠ a.swap := ne_swap_of_coordIdx' (Ne.symm hab)
  rw [injective_iff_map_eq_one]
  intro g hg
  have hv : ∀ v, phi a b g.1 v = v := fun v => by
    have h := LinearEquiv.congr_fun hg v
    exact h
  have e00 : g.1 0 0 = 1 := by
    have := congrFun (congrArg Prod.fst (hv (hypVec K A a))) a
    simpa [phi_fst, phiFun, hypVec_fst, h1, h1', h2', h3, h4] using this
  have e10 : g.1 1 0 = 0 := by
    have := congrFun (congrArg Prod.fst (hv (hypVec K A a))) b
    simpa [phi_fst, phiFun, hypVec_fst, h1, h1', h2', h3, h4] using this
  have e01 : g.1 0 1 = 0 := by
    have := congrFun (congrArg Prod.fst (hv (hypVec K A b))) a
    simpa [phi_fst, phiFun, hypVec_fst, h1, h1', h2', h3, h4] using this
  have e11 : g.1 1 1 = 1 := by
    have := congrFun (congrArg Prod.fst (hv (hypVec K A b))) b
    simpa [phi_fst, phiFun, hypVec_fst, h1, h1', h2', h3, h4] using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e10, e01, e11]

end Hom

end CFSG.RankThree.PartOne.K159H
