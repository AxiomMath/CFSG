module

public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly
public import TauCeti.GroupTheory.Coxeter.Geometric
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer
import CFSG.RankThree.CentralCover.AlternatingFourGroupWitness

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix
open Module

section Helpers

private lemma commute_of_sq_eq_one {E : Type*} [Group E] {a b : E} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) (h : (a * b) ^ 2 = 1) : a * b = b * a := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h)).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha', hb']

private lemma cross_eq_zero_of_commute {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {x y : V} {f g : Module.Dual K V} (hfx : f x = 2) (hgy : g y = 2)
    (hxy : LinearIndependent K ![x, y]) (h2 : (2 : K) ≠ 0)
    (hcomm : reflection hfx * reflection hgy = reflection hgy * reflection hfx) : f y = 0 := by
  have hy := congrArg (fun T : V ≃ₗ[K] V => T y) hcomm
  rw [reflection_mul_reflection_apply' hfx hgy,
    reflection_mul_reflection_apply' hgy hfx, hgy] at hy
  have key : (y - (2 : K) • y - (f y - f y * (2 : K)) • x) -
      (y - f y • x - ((2 : K) - g x * f y) • y)
      = (2 * f y) • x + (-(g x * f y)) • y := by module
  have h0 : (2 * f y) • x + (-(g x * f y)) • y = 0 := by
    rw [← key, sub_eq_zero]
    exact hy
  obtain ⟨h1, -⟩ := LinearIndependent.pair_iff.mp hxy (2 * f y) (-(g x * f y)) h0
  exact (mul_eq_zero.mp h1).resolve_left h2

private lemma ggCoxA_three {R : Type*} [CommRing R] (t : R) :
    ggCoxA R ((3 : ℕ) : ℤ) t = t + 1 := by
  rw [show ((3 : ℕ) : ℤ) = 2 * 1 + 1 by norm_num, ggCoxA_two_mul_add_one]
  norm_num

end Helpers

section DetTridiag

private noncomputable def diagScale {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) : Fin (n+1) → K :=
  Fin.induction (motive := fun _ => K) 1
    (fun i prev => -(A (Fin.castSucc i) i.succ) * prev)

private lemma diagScale_zero {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) : diagScale A 0 = 1 :=
  Fin.induction_zero ..

private lemma diagScale_succ {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K) (i : Fin n) :
    diagScale A i.succ = -(A (Fin.castSucc i) i.succ) * diagScale A (Fin.castSucc i) :=
  Fin.induction_succ ..

private lemma det_tridiag {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) K)
    (hdiag : ∀ i, A i i = 2)
    (hzero : ∀ i j, i ≠ j → ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) → A i j = 0)
    (hpair : ∀ i j, i.val + 1 = j.val → A i j * A j i = 1) :
    A.det = (n : K) + 2 := by
  have hd_ne : ∀ i : Fin (n+1), diagScale A i ≠ 0 := by
    intro i
    induction i using Fin.induction with
    | zero => rw [diagScale_zero]; exact one_ne_zero
    | succ k ih =>
        rw [diagScale_succ]
        refine mul_ne_zero (neg_ne_zero.mpr ?_) ih
        exact (mul_ne_zero_iff.mp (by rw [hpair (Fin.castSucc k) k.succ rfl]; exact one_ne_zero)).1
  have hconj : Matrix.diagonal (diagScale A) * A *
      Matrix.diagonal (fun i => (diagScale A i)⁻¹) =
      (CartanMatrix.A (n+1)).map (Int.castRingHom K) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : i = j
    · subst hij
      have hR : ((CartanMatrix.A (n+1)).map (Int.castRingHom K)) i i = 2 := by
        simp [CartanMatrix.A]
      rw [hR, hdiag i]
      calc diagScale A i * 2 * (diagScale A i)⁻¹
          = 2 * (diagScale A i * (diagScale A i)⁻¹) := by ring
        _ = 2 := by rw [mul_inv_cancel₀ (hd_ne i), mul_one]
    · by_cases hf : i.val + 1 = j.val
      · have hR : ((CartanMatrix.A (n+1)).map (Int.castRingHom K)) i j = -1 := by
          simp [CartanMatrix.A, hij, hf]
        rw [hR]
        have hdj : diagScale A j = -(A i j) * diagScale A i := by
          have h := diagScale_succ A (⟨i.val, by omega⟩ : Fin n)
          rw [show Fin.castSucc (⟨i.val, by omega⟩ : Fin n) = i from Fin.ext rfl,
            show (⟨i.val, by omega⟩ : Fin n).succ = j from Fin.ext (by simp [Fin.succ]; omega)] at h
          exact h
        have hnum : diagScale A i * A i j = -diagScale A j := by
          rw [hdj]; ring
        calc diagScale A i * A i j * (diagScale A j)⁻¹
            = (-diagScale A j) * (diagScale A j)⁻¹ := by rw [hnum]
          _ = -1 := by rw [neg_mul, mul_inv_cancel₀ (hd_ne j)]
      · by_cases hb : j.val + 1 = i.val
        · have hR : ((CartanMatrix.A (n+1)).map (Int.castRingHom K)) i j = -1 := by
            simp [CartanMatrix.A, hij, hb]
          rw [hR]
          have hdi : diagScale A i = -(A j i) * diagScale A j := by
            have h := diagScale_succ A (⟨j.val, by omega⟩ : Fin n)
            rw [show Fin.castSucc (⟨j.val, by omega⟩ : Fin n) = j from Fin.ext rfl,
              show (⟨j.val, by omega⟩ : Fin n).succ = i from
                Fin.ext (by simp [Fin.succ]; omega)] at h
            exact h
          calc diagScale A i * A i j * (diagScale A j)⁻¹
              = (-(A j i * A i j)) * (diagScale A j * (diagScale A j)⁻¹) := by
                rw [hdi]; ring
            _ = -1 := by rw [hpair j i hb, mul_inv_cancel₀ (hd_ne j)]; ring
        · have hz := hzero i j hij (by rintro (h1 | h1) <;> [exact hf h1; exact hb h1])
          have hR : ((CartanMatrix.A (n+1)).map (Int.castRingHom K)) i j = 0 := by
            simp [CartanMatrix.A, hij, hf, hb]
          rw [hR, hz, mul_zero, zero_mul]
  have hdetconj : (Matrix.diagonal (diagScale A) * A *
      Matrix.diagonal (fun i => (diagScale A i)⁻¹)).det = A.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
      Finset.prod_inv_distrib]
    have hprod : (∏ i : Fin (n+1), diagScale A i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => hd_ne i
    field_simp
  have hcast : ((CartanMatrix.A (n+1)).map (Int.castRingHom K)).det =
      (Int.castRingHom K) ((CartanMatrix.A (n+1)).det) :=
    (RingHom.map_det (Int.castRingHom K) (CartanMatrix.A (n+1))).symm
  rw [← hdetconj, hconj, hcast, CartanMatrix.A_det]
  simp only [map_add, map_one, map_natCast, map_ofNat]
  push_cast
  ring

end DetTridiag

section Toral

variable {G : Type} [Group G] [Finite G]

theorem pow_le_card_of_weylOfType_A {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs) {m : ℕ}
    (hW : GGWeylOfType p (CoxeterMatrix.A (m + 1)) A) (hpm : ¬ p ∣ m + 2) :
    p ^ (m + 1) ≤ Nat.card Bs := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  obtain ⟨e, he⟩ := hW
  let ψ : (CoxeterMatrix.A (m + 1)).Group →* MulAut ↥Bs :=
    (Subgroup.subtype A).comp e.toMonoidHom
  have hψinj : Function.Injective ψ := by
    intro a b h
    exact e.injective (Subtype.ext h)
  let φ : Fin (m + 1) → MulAut ↥Bs := fun i => ψ ((CoxeterMatrix.A (m + 1)).simple i)
  have hφmem : ∀ i, φ i ∈ ggInduced ⊤ Bs := fun i =>
    hA (e ((CoxeterMatrix.A (m + 1)).simple i))
      (e ((CoxeterMatrix.A (m + 1)).simple i)).2
  choose x f hfx hφx using fun i => exists_of_ggIsReflection (p := p) ι (he i)
  have hLφ : ∀ i, ggLin (p := p) ι (φ i) = reflection (hfx i) :=
    fun i => ggLin_eq_reflection ι (hfx i) (hφx i)
  have horder : ∀ i j, orderOf (φ i * φ j) = (CoxeterMatrix.A (m + 1)) i j := by
    intro i j
    have h2 : orderOf ((CoxeterMatrix.A (m + 1)).simple i *
        (CoxeterMatrix.A (m + 1)).simple j) = (CoxeterMatrix.A (m + 1)) i j := by
      simpa using CoxeterSystem.orderOf_simple_mul_simple
        (CoxeterMatrix.A (m + 1)).toCoxeterSystem i j
    change orderOf (ψ ((CoxeterMatrix.A (m + 1)).simple i) *
      ψ ((CoxeterMatrix.A (m + 1)).simple j)) = (CoxeterMatrix.A (m + 1)) i j
    rw [← map_mul, orderOf_injective ψ hψinj, h2]
  have hne : ∀ i j, i ≠ j → φ i ≠ φ j := by
    intro i j hij hφ
    have hsimple : (CoxeterMatrix.A (m + 1)).simple i = (CoxeterMatrix.A (m + 1)).simple j :=
      hψinj hφ
    exact hij (CoxeterSystem.simple_injective (CoxeterMatrix.A (m + 1)).toCoxeterSystem hsimple)
  have hzero : ∀ i j, i ≠ j → ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) → f i (x j) = 0 := by
    intro i j hij hnot
    have hM2 : (CoxeterMatrix.A (m + 1)) i j = 2 := by
      have hcond : ¬ ((j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j) := by
        rintro (h1 | h1)
        · exact hnot (Or.inr h1)
        · exact hnot (Or.inl h1)
      simp only [CoxeterMatrix.A, Matrix.of_apply, hij, if_false, hcond, if_false]
    have horder2 : orderOf (φ i * φ j) = 2 := by rw [horder i j, hM2]
    have hsqφ : (φ i * φ j) ^ 2 = 1 := by rw [← horder2]; exact pow_orderOf_eq_one _
    have hsqr : (reflection (hfx i) * reflection (hfx j)) ^ 2 = 1 := by
      have h := congrArg (ggLin (p := p) ι) hsqφ
      rwa [map_pow, map_mul, hLφ i, hLφ j, map_one] at h
    obtain ⟨hxy, -⟩ := ggReflection_linearIndependent_of_noTransvection hp2 hNT ι
      (hφmem i) (hφmem j) (hne i j hij) (hfx i) (hfx j) (hLφ i) (hLφ j)
    have hri : (reflection (hfx i)) ^ 2 = 1 := by
      rw [pow_two]
      have h := mul_inv_cancel (reflection (hfx i) : V ≃ₗ[ZMod p] V)
      rwa [reflection_inv (hfx i)] at h
    have hrj : (reflection (hfx j)) ^ 2 = 1 := by
      rw [pow_two]
      have h := mul_inv_cancel (reflection (hfx j) : V ≃ₗ[ZMod p] V)
      rwa [reflection_inv (hfx j)] at h
    exact cross_eq_zero_of_commute (hfx i) (hfx j) hxy (zmod_two_ne_zero hp2)
      (commute_of_sq_eq_one hri hrj hsqr)
  have hpair : ∀ i j, i.val + 1 = j.val → f i (x j) * f j (x i) = 1 := by
    intro i j hij
    have hij' : i ≠ j := by rintro rfl; omega
    have hM3 : (CoxeterMatrix.A (m + 1)) i j = 3 := by
      have hcond : (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j := Or.inr hij
      simp only [CoxeterMatrix.A, Matrix.of_apply, hij', if_false, hcond, if_true]
    have horder3 : orderOf (φ i * φ j) = 3 := by rw [horder i j, hM3]
    have h3φ : (φ i * φ j) ^ 3 = 1 := by rw [← horder3]; exact pow_orderOf_eq_one _
    have h3r : (reflection (hfx i) * reflection (hfx j)) ^ 3 = 1 := by
      have h := congrArg (ggLin (p := p) ι) h3φ
      rwa [map_pow, map_mul, hLφ i, hLφ j, map_one] at h
    obtain ⟨hxy, hfg⟩ := ggReflection_linearIndependent_of_noTransvection hp2 hNT ι
      (hφmem i) (hφmem j) (hne i j hij') (hfx i) (hfx j) (hLφ i) (hLφ j)
    by_cases hu : f i (x j) = 0
    · have hv : f j (x i) = 0 :=
        ggCross_eq_zero_of_noTransvection hp2 hNT ι (hφmem i) (hφmem j) (hfx i) (hfx j)
          (hLφ i) (hLφ j) hu
      have h2r : (reflection (hfx i) * reflection (hfx j)) ^ 2 = 1 :=
        reflection_mul_reflection_pow_two (hfx i) (hfx j) hu hv
      have h2φ : (φ i * φ j) ^ 2 = 1 := by
        apply ggLin_injective (p := p) ι
        rw [map_pow, map_mul, hLφ i, hLφ j, h2r, map_one]
      have hdvd : orderOf (φ i * φ j) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2φ
      rw [horder3] at hdvd
      exact absurd hdvd (by norm_num)
    · by_cases hv : f j (x i) = 0
      · exact absurd (ggCross_eq_zero_of_noTransvection hp2 hNT ι (hφmem j) (hφmem i)
          (hfx j) (hfx i) (hLφ j) (hLφ i) hv) hu
      · have hcos := (reflection_mul_reflection_pow_eq_one_iff_of_ne_zero (hfx i) (hfx j)
          hxy hfg hu hv 3).mp h3r
        have hA' := hcos.1
        rw [ggCoxA_three] at hA'
        linear_combination hA'
  let Cm : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod p) := Matrix.of fun i j => f i (x j)
  have hdet : Cm.det = (m : ZMod p) + 2 :=
    det_tridiag Cm (fun i => hfx i) (fun i j => hzero i j) (fun i j => hpair i j)
  have hdet_ne : Cm.det ≠ 0 := by
    rw [hdet]
    have heq : ((m : ZMod p) + 2) = ((m + 2 : ℕ) : ZMod p) := by push_cast; ring
    rw [heq]
    exact fun h => hpm ((ZMod.natCast_eq_zero_iff (m + 2) p).mp h)
  have hLI : LinearIndependent (ZMod p) x := linearIndependent_of_det_ne_zero x f hdet_ne
  have hfin : m + 1 ≤ Module.finrank (ZMod p) V := by
    have := LinearIndependent.fintype_card_le_finrank hLI
    simpa using this
  calc p ^ (m + 1) ≤ p ^ Module.finrank (ZMod p) V :=
        Nat.pow_le_pow_right (Nat.Prime.pos hp) hfin
    _ = Nat.card V := FiniteField.pow_finrank_eq_natCard p V
    _ = Nat.card Bs := (card_eq_of_ggLin ι).symm

end Toral

end CFSG.StandardType

end
