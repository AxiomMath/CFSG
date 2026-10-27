module

public import CFSG.Monster.Lifts.PermLift

public noncomputable section

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Lifts

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem permWord_apply' (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) (i : Fin 24) :
    permWord p x i = x (p⁻¹ i) := rfl

theorem permWord_mul_apply (p : Equiv.Perm (Fin 24)) (x y : Fin 24 → ZMod 2) :
    permWord p (x * y) = permWord p x * permWord p y := rfl

theorem hammingNorm_permWord (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    hammingNorm (permWord p x) = hammingNorm x :=
  hammingNorm_comp_perm x p⁻¹

theorem P_permWord (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) : P (permWord p x) = P x := by
  unfold P
  rw [hammingNorm_permWord]

theorem K_permWord (p : Equiv.Perm (Fin 24)) (x y : Fin 24 → ZMod 2) :
    K (permWord p x) (permWord p y) = K x y := by
  rw [K_eq, K_eq, ← permWord_mul_apply, hammingNorm_permWord]

theorem A_permWord (p : Equiv.Perm (Fin 24)) (x y w : Fin 24 → ZMod 2) :
    A (permWord p x) (permWord p y) (permWord p w) = A x y w := by
  rw [A_eq_sum, A_eq_sum]
  exact Equiv.sum_comp p⁻¹ fun i => x i * y i * w i

theorem dotProduct_permWord (p : Equiv.Perm (Fin 24)) (x y : Fin 24 → ZMod 2) :
    permWord p x ⬝ᵥ permWord p y = x ⬝ᵥ y :=
  Equiv.sum_comp p⁻¹ fun i => x i * y i

theorem permWord_Ω (p : Equiv.Perm (Fin 24)) : permWord p Ω = Ω := rfl

theorem permC_ΩC (p : AutPerm) : permC p ΩC = ΩC := Subtype.ext (permWord_Ω p)

theorem permC_symm_apply (p : AutPerm) (u : C) : (permC p).symm u = permC p⁻¹ u := rfl

theorem betaP_add_left (p : AutPerm) (a a' b : C) :
    betaP p (a + a') b = betaP p a b + betaP p a' b := by
  unfold betaP
  rw [map_add, θ_add_left, θ_add_left, coe_permC, coe_permC, coe_permC, A_permWord]
  linear_combination (A a a' b) * two_eq_zero'

theorem betaP_add_right (p : AutPerm) (a b b' : C) :
    betaP p a (b + b') = betaP p a b + betaP p a b' := by
  unfold betaP
  rw [map_add, θ_add_right, θ_add_right]
  ring

theorem betaP_self (p : AutPerm) (a : C) : betaP p a a = 0 := by
  unfold betaP
  rw [θ_self, θ_self, coe_permC, P_permWord]
  linear_combination (P (a : Fin 24 → ZMod 2)) * two_eq_zero'

theorem betaP_comm (p : AutPerm) (a b : C) : betaP p a b = betaP p b a := by
  have h1 := θ_add_θ_swap (permC p a) (permC p b)
  have h2 := θ_add_θ_swap a b
  rw [coe_permC, coe_permC, K_permWord] at h1
  unfold betaP
  linear_combination h1 - h2 + (θ a b - θ (permC p b) (permC p a)) * two_eq_zero'

theorem betaP_smul_left (p : AutPerm) (c : ZMod 2) (a b : C) :
    betaP p (c • a) b = c * betaP p a b := by
  rcases zmod2_cases c with rfl | rfl
  · have h := betaP_add_left p 0 0 b
    rw [add_zero] at h
    rw [zero_smul, zero_mul]
    linear_combination h + (betaP p 0 b) * two_eq_zero'
  · rw [one_smul, one_mul]

theorem betaP_smul_right (p : AutPerm) (c : ZMod 2) (a b : C) :
    betaP p a (c • b) = c * betaP p a b := by
  rw [betaP_comm, betaP_smul_left, betaP_comm]

@[expose] def betaBilin (p : AutPerm) : LinearMap.BilinForm (ZMod 2) C :=
  LinearMap.mk₂ (ZMod 2) (betaP p) (betaP_add_left p) (fun c a b => betaP_smul_left p c a b)
    (betaP_add_right p) (fun c a b => betaP_smul_right p c a b)

theorem betaBilin_apply (p : AutPerm) (a b : C) : betaBilin p a b = betaP p a b := rfl

theorem betaBilin_isAlt (p : AutPerm) : (betaBilin p).IsAlt := betaP_self p

theorem betaP_ΩC (p : AutPerm) (a : C) : betaP p a ΩC = 0 := by
  unfold betaP
  rw [permC_ΩC, θ_ΩC_right, θ_ΩC_right, add_zero]

theorem betaP_eq_sum (p : AutPerm) (a b : C) :
    betaP p a b = ∑ i, ∑ j, basisC.repr a i * basisC.repr b j *
      betaP p (basisC i) (basisC j) := by
  have h : betaBilin p (∑ i, basisC.repr a i • basisC i) (∑ j, basisC.repr b j • basisC j) =
      betaBilin p a b := by
    rw [basisC.sum_repr, basisC.sum_repr]
  rw [← betaBilin_apply, ← h]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    betaBilin_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem kappaP_add (p : AutPerm) (a b : C) :
    kappaP p (a + b) + kappaP p a + kappaP p b = betaP p a b := by
  rw [betaP_eq_sum]
  unfold kappaP
  set α := basisC.repr a with hα
  set α' := basisC.repr b with hα'
  have hrepr : ∀ i, basisC.repr (a + b) i = α i + α' i := fun i => by
    rw [map_add, Finsupp.add_apply]
  simp only [hrepr]
  set B : Fin 12 → Fin 12 → ZMod 2 := fun i j => betaP p (basisC i) (basisC j) with hB
  have hsymm : ∀ i j, B i j = B j i := fun i j => betaP_comm p _ _
  have hdiag : ∀ i, B i i = 0 := fun i => betaP_self p _
  have hsplit : ∑ i, ∑ j, α i * α' j * B i j =
      ∑ i, ∑ j, ((if i < j then α i * α' j * B i j else 0) +
        (if j < i then α i * α' j * B i j else 0)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | rfl | h
    · rw [ite_eq_left h, ite_eq_right (not_lt_of_gt h), add_zero]
    · rw [ite_eq_right (lt_irrefl i), add_zero, hdiag, mul_zero]
    · rw [ite_eq_right (not_lt_of_gt h), ite_eq_left h, zero_add]
  have hswap : ∑ i, ∑ j, (if j < i then α i * α' j * B i j else 0) =
      ∑ i, ∑ j, (if i < j then α' i * α j * B i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : i < j
    · rw [ite_eq_left h, ite_eq_left h, hsymm]
      ring
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hsplit, Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
    hswap, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j
  · simp only [h, ↓reduceIte]
    linear_combination (α i * α j * B i j + α' i * α' j * B i j) * two_eq_zero'
  · simp only [h, ↓reduceIte, add_zero]

theorem kappaP_add_ΩC (p : AutPerm) (c : C) :
    kappaP p (c + ΩC) = kappaP p c + kappaP p ΩC := by
  have h := kappaP_add p c ΩC
  rw [betaP_ΩC] at h
  linear_combination h - (kappaP p c + kappaP p ΩC) * two_eq_zero'

@[expose] def permWordLin (p : Equiv.Perm (Fin 24)) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) ⇑p⁻¹

theorem permWordLin_apply (p : Equiv.Perm (Fin 24)) (x : Fin 24 → ZMod 2) :
    permWordLin p x = permWord p x := rfl

@[expose] def permD (p : AutPerm) : Cocode →ₗ[ZMod 2] Cocode :=
  C.mapQ C (permWordLin p) fun _ hx => permWord_mem_of_mem_AutPerm p.2 hx

theorem permD_mk (p : AutPerm) (x : Fin 24 → ZMod 2) :
    permD p (Submodule.Quotient.mk x) = Submodule.Quotient.mk (permWord p x) := rfl

theorem pair_permC_permD (p : AutPerm) (a : C) (δ : Cocode) :
    pair (permC p a) (permD p δ) = pair a δ := by
  induction δ using Submodule.Quotient.induction_on with
  | H x => rw [permD_mk, pair_mk, pair_mk, coe_permC, dotProduct_permWord]

end CFSG.Monster.Visible
