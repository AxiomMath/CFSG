module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.RankThree.GF2n.Smith81.TiD3Model

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

namespace D3

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem act_smul (τ : F →+* F) (g : Mat2 F) (c : F) (x : Hyp F) :
    act τ g (c • x) = c • act τ g x := by
  funext i j k
  simp only [act, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem act_mem_kForm (τ : F →ₐ[K] F) (hτ : ∀ a, τ (τ (τ a)) = a) (g : Mat2 F) {x : Hyp F}
    (hx : x ∈ kForm τ) : act (τ : F →+* F) g x ∈ kForm τ := by
  intro i j k
  have hx' : ∀ i j k, τ (x i j k) = x k i j := fun i j k => (hx i j k).symm
  simp only [act, map_sum, map_add, map_mul, AlgHom.coe_toRingHom, hx', hτ, Fin.sum_univ_two]
  ring

theorem uElt_eq_uSL (t : F) : uElt t = D2.uSL t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uElt, D2.uSL]


@[expose] def hyp {R : Type*} (w : (Fin 3 → Fin 2) → R) : Hyp R := fun i j k => w ![i, j, k]

theorem sum_pi_fin3 {R : Type*} [AddCommMonoid R] (f : (Fin 3 → Fin 2) → R) :
    ∑ x, f x = ∑ i, ∑ j, ∑ k, f ![i, j, k] := by
  let e : (Fin 3 → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 :=
    { toFun := fun x => (x 0, x 1, x 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun x => by funext s; fin_cases s <;> rfl
      right_inv := fun p => rfl }
  rw [← Fintype.sum_equiv e.symm (fun p => f ![p.1, p.2.1, p.2.2]) f (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]


theorem hyp_tensorRep {E : Type*} [Field E] [Algebra F E] [CharP E 2] (e : Fin 3 → ℕ)
    (g : SL(2, F)) (w : (Fin 3 → Fin 2) → E) :
    hyp (tensorRep F E e g w) = fun i j k => ∑ i', ∑ j', ∑ k',
      twistMat E (e 0) g i i' * twistMat E (e 1) g j j' * twistMat E (e 2) g k k' *
        hyp w i' j' k' := by
  funext i j k
  simp only [hyp, tensorRep_apply, tmatE, sum_pi_fin3, Fin.prod_univ_three]
  simp

theorem hyp_tensorRep_act [CharP F 2] (a k : ℕ) (σ : F ≃+* F) (hσ : ∀ x, σ x = x ^ 2 ^ a)
    (τ : F →+* F)
    (hτ : ∀ x, τ x = x ^ 2 ^ k) (g : SL(2, F)) (w : (Fin 3 → Fin 2) → F) :
    hyp (tensorRep F F ![a, a + k, a + 2 * k] g w) =
      act τ ((D2.slMap σ g : SL(2, F)) : Mat2 F) (hyp w) := by
  rw [hyp_tensorRep]
  funext i j k'
  simp only [act, twistMat_apply, D2.coe_slMap, Algebra.algebraMap_self, RingHom.id_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hσ, hτ]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun k'' _ => ?_
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  have h2 : 2 ^ a * 2 ^ (k + k) = 2 ^ (a + 2 * k) := by
    rw [← pow_add]
    congr 1
    ring
  rw [h2]


theorem card_kForm_le {K F : Type*} [Field K] [Fintype K] [Field F] [Fintype F] [Algebra K F]
    (hF : Fintype.card F = Fintype.card K ^ 3) (τ : F →ₐ[K] F)
    (hτ : ∀ a, τ a = a ^ Fintype.card K) :
    Nat.card (kForm τ) ≤ Fintype.card K ^ 8 := by
  obtain ⟨p, hp⟩ : ∃ p : F → K,
      ∀ a : F, a ^ Fintype.card K = a → algebraMap K F (p a) = a := by
    refine ⟨Function.invFun (algebraMap K F), fun a ha => ?_⟩
    obtain ⟨c, hc⟩ := (pow_card_eq_self_iff (K := K) a).mp ha
    exact Function.invFun_eq ⟨c, hc⟩
  have hinj : Function.Injective
      (fun x : kForm τ => (p (x.1 0 0 0), x.1 0 0 1, x.1 0 1 1, p (x.1 1 1 1))) := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨h000, h001, h011, h111⟩ := hxy
    have hx' : ∀ i j k : Fin 2, x k i j = τ (x i j k) := hx
    have hy' : ∀ i j k : Fin 2, y k i j = τ (y i j k) := hy
    have ex000 : x 0 0 0 ^ Fintype.card K = x 0 0 0 :=
      (hτ (x 0 0 0)).symm.trans (hx' 0 0 0).symm
    have ey000 : y 0 0 0 ^ Fintype.card K = y 0 0 0 :=
      (hτ (y 0 0 0)).symm.trans (hy' 0 0 0).symm
    have ex111 : x 1 1 1 ^ Fintype.card K = x 1 1 1 :=
      (hτ (x 1 1 1)).symm.trans (hx' 1 1 1).symm
    have ey111 : y 1 1 1 ^ Fintype.card K = y 1 1 1 :=
      (hτ (y 1 1 1)).symm.trans (hy' 1 1 1).symm
    have e000 : x 0 0 0 = y 0 0 0 := by
      rw [← hp _ ex000, ← hp _ ey000, h000]
    have e111 : x 1 1 1 = y 1 1 1 := by
      rw [← hp _ ex111, ← hp _ ey111, h111]
    have e100 : x 1 0 0 = y 1 0 0 := by
      rw [hx' 0 0 1, hy' 0 0 1, h001]
    have e010 : x 0 1 0 = y 0 1 0 := by
      rw [hx' 1 0 0, hy' 1 0 0, e100]
    have e101 : x 1 0 1 = y 1 0 1 := by
      rw [hx' 0 1 1, hy' 0 1 1, h011]
    have e110 : x 1 1 0 = y 1 1 0 := by
      rw [hx' 1 0 1, hy' 1 0 1, e101]
    have key : ∀ i j k : Fin 2, x i j k = y i j k := by
      simp only [Fin.forall_fin_two]
      exact ⟨⟨⟨e000, h001⟩, ⟨e010, h011⟩⟩, ⟨⟨e100, e101⟩, ⟨e110, e111⟩⟩⟩
    exact Subtype.ext (funext fun i => funext fun j => funext fun k => key i j k)
  have hcard : Nat.card (K × F × F × K) = Fintype.card K ^ 8 := by
    rw [Nat.card_prod, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_eq_fintype_card, hF]
    ring
  calc Nat.card (kForm τ) ≤ Nat.card (K × F × F × K) := Nat.card_le_card_of_injective _ hinj
    _ = Fintype.card K ^ 8 := hcard

end D3

end CFSG.RankThree.GF2n.Smith81
