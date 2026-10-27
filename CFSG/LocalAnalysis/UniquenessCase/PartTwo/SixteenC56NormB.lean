module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormTop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private def swapOmI : OmI → OmI
  | Sum.inl i => Sum.inr i
  | Sum.inr i => Sum.inl i

private theorem vec_prod' (s : Finset OmI) (f : OmI → W) :
    S.vec (∏ i ∈ s, f i) = ∑ i ∈ s, S.vec (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [S.vec_one]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, S.vec_mul, ih]

private theorem ofVec_eq_prod' (v : OmI → S.K) :
    S.ofVec v = ∏ i, S.smul (v i) (S.ofVec (Pi.single i 1)) := by
  apply S.vec_injective
  rw [S.vec_ofVec, vec_prod' S Finset.univ]
  have hterm : ∀ i : OmI,
      S.vec (S.smul (v i) (S.ofVec (Pi.single i 1))) = (v i) • Pi.single i 1 := by
    intro i
    rw [S.vec_smul, S.vec_ofVec]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  exact pi_eq_sum_univ' v

include S in
private theorem inv_eq_selfS (w : W) : w⁻¹ = w := by
  apply inv_eq_of_mul_eq_one_right
  apply S.vec_injective
  rw [S.vec_mul, S.vec_one]
  exact CharTwo.add_self_eq_zero (S.vec w)

private theorem exists_pol_eq_of_add_smul (f : W → S.K)
    (hf_add : ∀ x y : W, f (x * y) = f x + f y)
    (hf_smul : ∀ (c : S.K) (x : W), f (S.smul c x) = c * f x) :
    ∃ a : W, ∀ y : W, f y = S.pol a y := by
  classical
  have hf_one : f 1 = 0 := by
    have h : f 1 = f 1 + f 1 := by simpa using hf_add 1 1
    rwa [CharTwo.add_self_eq_zero] at h
  have hprod : ∀ (s : Finset OmI) (c : OmI → S.K),
      f (∏ i ∈ s, S.smul (c i) (S.ofVec (Pi.single i 1))) =
        ∑ i ∈ s, c i * f (S.ofVec (Pi.single i 1)) := by
    intro s c
    induction s using Finset.induction_on with
    | empty => simpa using hf_one
    | insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi, hf_add, ih, hf_smul]
  refine ⟨S.ofVec (fun i => f (S.ofVec (Pi.single (swapOmI i) 1))), fun y => ?_⟩
  conv_lhs => rw [← S.ofVec_vec y, ofVec_eq_prod' S]
  rw [hprod Finset.univ (S.vec y), S.pol_eq, S.vec_ofVec]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, swapOmI]
  ring

private theorem eq_of_pol_eq {a b : W} (h : ∀ y : W, S.pol a y = S.pol b y) : a = b := by
  have h' : ∀ y : W, S.pol (a * b⁻¹) y = 0 := by
    intro y
    rw [S.pol_mul_left, h y, inv_eq_selfS S b]
    exact CharTwo.add_self_eq_zero (S.pol b y)
  exact mul_inv_eq_one.mp (S.eq_one_of_pol_eq_zero h')

private theorem omega_pol {h : MulAut W} (hh : h ∈ S.omega) (x y : W) :
    S.pol (h x) (h y) = S.pol x y := by
  simp only [pol]
  rw [← map_mul h x y, S.omega_Q hh (x * y), S.omega_Q hh x, S.omega_Q hh y]

theorem exists_similitude_of_linear {g : MulAut W}
    (hg : g ∈ Subgroup.normalizer (S.omega : Set (MulAut W)))
    (hlin : ∀ (c : S.K) (w : W), g (S.smul c w) = S.smul c (g w)) :
    ∃ c : S.K, c ≠ 0 ∧ ∀ w : W, S.Q (g w) = c * S.Q w := by
  classical
  have hex : ∀ x : W, ∃ a : W, ∀ y : W, S.pol (g x) (g y) = S.pol a y := by
    intro x
    exact S.exists_pol_eq_of_add_smul (fun y => S.pol (g x) (g y))
      (fun y y' => by rw [map_mul, S.pol_mul_right])
      (fun c y => by rw [hlin c y, S.pol_smul_right])
  let A : W → W := fun x => Classical.choose (hex x)
  have hA : ∀ x y : W, S.pol (A x) y = S.pol (g x) (g y) :=
    fun x y => (Classical.choose_spec (hex x) y).symm
  have hA_mul : ∀ x x' : W, A (x * x') = A x * A x' := by
    intro x x'
    apply S.eq_of_pol_eq
    intro y
    rw [hA (x * x') y, map_mul, S.pol_mul_left, ← hA x y, ← hA x' y, S.pol_mul_left]
  let Ahom : W →* W := MonoidHom.mk' A hA_mul
  have hA_comm : ∀ h ∈ S.omega, ∀ x : W, A (h x) = h (A x) := by
    intro h hh x
    apply S.eq_of_pol_eq
    intro y
    have h1mem : g * h * g⁻¹ ∈ S.omega := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have hgh : g (h x) = (g * h * g⁻¹) (g x) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    have hgy : g y = (g * h * g⁻¹) (g (h⁻¹ y)) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, MulAut.apply_inv_self]
    rw [hA (h x) y, hgh, hgy, S.omega_pol h1mem (g x) (g (h⁻¹ y)),
      ← hA x (h⁻¹ y), ← S.omega_pol hh (A x) (h⁻¹ y), MulAut.apply_inv_self W h y]
  obtain ⟨c, hc⟩ := S.exists_smul_of_commute_omega0 Ahom
    (fun h hh w => by
      show A (h w) = h (A w)
      exact hA_comm h (S.omega0_le_omega hh) w)
  have hcA : ∀ w : W, A w = S.smul c w := fun w => hc w
  have hcB : ∀ x y : W, S.pol (g x) (g y) = c * S.pol x y := by
    intro x y
    rw [← hA x y, hcA x, S.pol_smul_left]
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    obtain ⟨w₀, hw₀⟩ := S.exists_Q_ne_zero
    have hw1 : w₀ ≠ 1 := fun h1 => hw₀ (by rw [h1, S.Q_one])
    have hgone : ∀ x : W, g x = 1 := by
      intro x
      apply S.eq_one_of_pol_eq_zero
      intro y
      rw [← MulAut.apply_inv_self W g y, hcB x (g⁻¹ y), hc0, zero_mul]
    exact hw1 (g.injective (by rw [hgone w₀, hgone 1]))
  · intro w
    let D : W → S.K := fun x => S.Q (g x) - c * S.Q x
    have hD_add : ∀ x y : W, D (x * y) = D x + D y := by
      intro x y
      dsimp only [D]
      rw [map_mul, S.Q_mul, S.Q_mul, hcB x y]
      ring
    have hD_one : D 1 = 0 := by
      show S.Q (g 1) - c * S.Q 1 = 0
      rw [map_one, S.Q_one]
      ring
    have hD_inv : ∀ x : W, D x⁻¹ = D x := by
      intro x
      have h := hD_add x x⁻¹
      rw [mul_inv_cancel, hD_one] at h
      have h3 : D x⁻¹ = - D x := by
        rw [eq_neg_iff_add_eq_zero]
        simpa [add_comm] using h.symm
      rwa [CharTwo.neg_eq] at h3
    have hD_omega : ∀ h ∈ S.omega, ∀ x : W, D (h x) = D x := by
      intro h hh x
      have h1mem : g * h * g⁻¹ ∈ S.omega := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
      have hgh : g (h x) = (g * h * g⁻¹) (g x) := by
        simp only [MulAut.mul_apply, MulAut.inv_apply_self]
      dsimp only [D]
      rw [hgh, S.omega_Q h1mem (g x), S.omega_Q hh x]
    have hD_comm : ∀ h ∈ S.omega, ∀ x : W, D (h x * x⁻¹) = 0 := by
      intro h hh x
      rw [hD_add, hD_inv, hD_omega h hh x, CharTwo.add_self_eq_zero]
    let Dhom : W →* Multiplicative S.K :=
      MonoidHom.mk' (fun x => Multiplicative.ofAdd (D x)) (fun x y => by
        rw [hD_add]
        rfl)
    have hker : commSub ⊤ S.omega ≤ Dhom.ker := by
      rw [commSub, Subgroup.closure_le]
      rintro d ⟨h, hh, x, -, rfl⟩
      show Multiplicative.ofAdd (D (h x * x⁻¹)) = 1
      rw [hD_comm h hh x]
      rfl
    have htop : (⊤ : Subgroup W) ≤ Dhom.ker := by
      rw [← S.commSub_top_omega]
      exact hker
    have hDzero : D w = 0 := by
      have hx1 : Dhom w = 1 := htop (Subgroup.mem_top w)
      have hx2 : Multiplicative.ofAdd (D w) = (1 : Multiplicative S.K) := hx1
      exact Multiplicative.ofAdd.injective hx2
    change S.Q (g w) - c * S.Q w = 0 at hDzero
    exact sub_eq_zero.mp hDzero

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
