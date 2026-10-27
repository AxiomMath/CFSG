module

public import CFSG.RankThree.CentralCover.SteinbergBNChevalleySplitTorus

public section

namespace CFSG.RankThree.CentralCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Exp

variable {p : ℕ} {d : ℕ}

@[expose] def subTorusExp {τ : Tag} (e : Fin d → Fin τ.rank) (a : Fin d → ZMod p) :
    Fin τ.rank → ZMod p :=
  fun j => ∑ i, if e i = j then a i else 0

theorem subTorusExp_apply {τ : Tag} (e : Fin d → Fin τ.rank) (a : Fin d → ZMod p)
    (j : Fin τ.rank) : subTorusExp e a j = ∑ i, if e i = j then a i else 0 :=
  rfl

@[expose] def subTorusLinearMap {τ : Tag} (e : Fin d → Fin τ.rank) :
    (Fin d → ZMod p) →ₗ[ZMod p] (Fin τ.rank → ZMod p) where
  toFun := subTorusExp e
  map_add' a b := by
    funext j
    rw [subTorusExp_apply, Pi.add_apply, subTorusExp_apply, subTorusExp_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : e i = j <;> simp [h]
  map_smul' c a := by
    funext j
    rw [subTorusExp_apply, Pi.smul_apply, subTorusExp_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : e i = j <;> simp [h]

theorem subTorusExp_sub {τ : Tag} (e : Fin d → Fin τ.rank) (a b : Fin d → ZMod p) :
    subTorusExp e (a - b) = subTorusExp e a - subTorusExp e b :=
  (subTorusLinearMap e).map_sub a b

theorem subTorusExp_smul {τ : Tag} (e : Fin d → Fin τ.rank) (c : ZMod p) (a : Fin d → ZMod p) :
    subTorusExp e (c • a) = c • subTorusExp e a :=
  (subTorusLinearMap e).map_smul c a

theorem subTorusExp_single {τ : Tag} (e : Fin d → Fin τ.rank) (he : Function.Injective e)
    (i : Fin d) : subTorusExp e (Pi.single i (1 : ZMod p)) = Pi.single (e i) (1 : ZMod p) := by
  classical
  funext j
  rw [subTorusExp_apply]
  by_cases hj : e i = j
  · subst hj
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      rw [if_neg (fun h => hk (he h))]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Finset.sum_eq_zero, Pi.single_eq_of_ne (Ne.symm hj)]
    intro k _
    by_cases hk : e k = j
    · rw [if_pos hk, Pi.single_eq_of_ne (fun hki => hj (by rw [← hki, hk]))]
    · rw [if_neg hk]

theorem sum_mul_subTorusExp {τ : Tag} (e : Fin d → Fin τ.rank) (c : Fin τ.rank → ZMod p)
    (a : Fin d → ZMod p) :
    ∑ i : Fin τ.rank, c i * subTorusExp e a i = ∑ i : Fin d, c (e i) * a i := by
  classical
  simp only [subTorusExp_apply]
  calc ∑ i, c i * ∑ k, (if e k = i then a k else 0)
      = ∑ i, ∑ k, c i * (if e k = i then a k else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, ∑ i, c i * (if e k = i then a k else 0) := Finset.sum_comm
    _ = ∑ k, c (e k) * a k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_eq_single (e k)]
        · simp
        · intro i _ hik
          rw [if_neg (fun h => hik h.symm), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ (e k)) h

end Exp

section Torus

variable {τ : Tag} {K : Type} [Field K] {p : ℕ} [NeZero p] {d : ℕ}

@[expose] noncomputable def chevSubTorus (e : Fin d → Fin τ.rank) (ζ : Kˣ) (hζ : ζ ^ p = 1) :
    Multiplicative (Fin d → ZMod p) →* adjointGroup τ K :=
  (chevTorus τ ζ hζ).comp
    (AddMonoidHom.toMultiplicative (subTorusLinearMap e).toAddMonoidHom)

theorem chevSubTorus_apply
    (e : Fin d → Fin τ.rank) (ζ : Kˣ) (hζ : ζ ^ p = 1) (a : Fin d → ZMod p) :
    chevSubTorus e ζ hζ (.ofAdd a) = chevTorus τ ζ hζ (.ofAdd (subTorusExp e a)) :=
  rfl

theorem chevSubTorus_injective
    (e : Fin d → Fin τ.rank) (he : Function.Injective e) {ζ : Kˣ} (hζo : orderOf ζ = p)
    (hζ : ζ ^ p = 1) (hdet : IsUnit (((τ.cartan.submatrix e e).det : ℤ) : ZMod p)) :
    Function.Injective (chevSubTorus e ζ hζ) := by
  classical
  rw [injective_iff_map_eq_one]
  intro a ha
  have ht : torusCoordHom τ K
      (chevTorusExp τ ζ hζ (.ofAdd (subTorusExp e (Multiplicative.toAdd a)))) = 1 := by
    have := congrArg Subtype.val ha
    exact Subtype.ext this
  have hj : ∀ j : Fin d,
      ∑ i : Fin d, ((τ.cartan.submatrix e e) i j : ZMod p) * Multiplicative.toAdd a i = 0 := by
    intro j
    have h := torusCoordHom_apply_rootVec_single (R := K)
      (chevTorusExp τ ζ hζ (.ofAdd (subTorusExp e (Multiplicative.toAdd a)))) (e j)
    rw [ht, OneMemClass.coe_one, Units.val_one, Module.End.one_apply,
      rootVec_eq_single_of_isRoot (isRoot_single τ (e j))] at h
    have h' := congrArg (fun v : RootModule τ K =>
      v (Sum.inr ⟨Pi.single (e j) 1, isRoot_single τ (e j)⟩)) h
    simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h'
    have h1 : ∏ i, chevTorusExp τ ζ hζ
        (.ofAdd (subTorusExp e (Multiplicative.toAdd a))) i ^ τ.cartan i (e j) = 1 :=
      Units.ext (by rw [Units.val_one, ← h'])
    have h2 : zmodPowHom ζ hζ (.ofAdd (∑ i,
        (τ.cartan i (e j) : ZMod p) * subTorusExp e (Multiplicative.toAdd a) i)) = 1 := by
      rw [← h1, ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [chevTorusExp_apply, ← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul]
      simp
    have h3 := zmodPowHom_injective hζo hζ (h2.trans (map_one _).symm)
    have h4 := Multiplicative.ofAdd.injective h3
    rw [sum_mul_subTorusExp] at h4
    simpa only [Matrix.submatrix_apply] using h4
  have h0 := eq_zero_of_cartan_sum_eq_zero (A := τ.cartan.submatrix e e) hdet hj
  exact Multiplicative.toAdd.injective h0

theorem weylElt_conj_chevSubTorus
    (e : Fin d → Fin τ.rank) (he : Function.Injective e) (ζ : Kˣ) (hζ : ζ ^ p = 1)
    (i : Fin d) (a : Fin d → ZMod p) :
    (⟨weylElt τ K (e i) 1, weylElt_mem_adjointGroup (e i) 1⟩ : adjointGroup τ K) *
        chevSubTorus e ζ hζ (.ofAdd a) *
        (⟨weylElt τ K (e i) 1, weylElt_mem_adjointGroup (e i) 1⟩ : adjointGroup τ K)⁻¹ =
      chevSubTorus e ζ hζ (.ofAdd (a -
        (∑ j : Fin d, (τ.cartan (e j) (e i) : ZMod p) * a j) • Pi.single i 1)) := by
  have hb : subTorusExp e a -
      cartanFunctional τ p (e i) (subTorusExp e a) • Pi.single (e i) 1 =
      subTorusExp e (a - (∑ j : Fin d, (τ.cartan (e j) (e i) : ZMod p) * a j) •
        Pi.single i 1) := by
    rw [cartanFunctional_apply, sum_mul_subTorusExp, subTorusExp_sub, subTorusExp_smul,
      subTorusExp_single e he i]
  rw [chevSubTorus_apply, chevSubTorus_apply,
    weylElt_conj_chevTorus ζ hζ (e i) (subTorusExp e a), hb]

end Torus

end CFSG.RankThree.CentralCover
