module

public import CFSG.RankThree.PartOne.SLB4A.Unip
public import CFSG.LieType.BorelTits.OrthogonalEichler

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

section Even

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

def evI (k : Fin 5) : Fin 4 := ![0, 0, 0, 1, 1] k

def evJ (k : Fin 5) : Fin 4 := ![1, 2, 3, 2, 3] k

def oX (px py : Fin 4 → ι) (k : Fin 5) : Matrix ι ι K :=
  Matrix.single (px (evJ k)) (py (evI k)) 1 + Matrix.single (px (evI k)) (py (evJ k)) 1

theorem single_mul_single_zero {a b c d : ι} (h : b ≠ c) :
    (Matrix.single a b (1 : K)) * Matrix.single c d 1 = 0 := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases h1 : a = r ∧ b = x
  · have : ¬ (c = x ∧ d = s) := fun ⟨h2, _⟩ => h (h1.2.trans h2.symm)
    simp [this]
  · simp [h1]

theorem oX_mul (px py : Fin 4 → ι) (hd : ∀ i j, py i ≠ px j) (k l : Fin 5) :
    oX (K := K) px py k * oX px py l = 0 := by
  simp only [oX, add_mul, mul_add]
  rw [single_mul_single_zero (hd _ _), single_mul_single_zero (hd _ _),
    single_mul_single_zero (hd _ _), single_mul_single_zero (hd _ _)]
  simp

theorem Xsum_oX_ind [CharP K 2] (px py : Fin 4 → ι) (hpx : Function.Injective px)
    (hpy : Function.Injective py) (hd : ∀ i j, py i ≠ px j) (v : V2 5)
    (h : ∃ c : K, Xsum (oX (K := K) px py) v = Matrix.scalar ι c) : v = 1 := by
  obtain ⟨c, hc⟩ := h
  have key : ∀ a b : Fin 4, (Xsum (oX (K := K) px py) v : Matrix ι ι K) (px a) (py b) = 0 :=
    fun a b => by
      rw [hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (hd b a).symm]
  have e0 := key 0 1
  have e1 := key 0 2
  have e2 := key 0 3
  have e3 := key 1 2
  have e4 := key 1 3
  simp [Xsum, Matrix.sum_apply, Fin.sum_univ_five, oX, evI, evJ, Matrix.single_apply, hpx.eq_iff,
    hpy.eq_iff] at e0 e1 e2 e3 e4
  have one_ne : (1 : K) ≠ 0 := one_ne_zero
  funext k
  fin_cases k
  · exact cC2_eq_zero _ e0 one_ne
  · exact cC2_eq_zero _ e1 one_ne
  · exact cC2_eq_zero _ e2 one_ne
  · exact cC2_eq_zero _ e3 one_ne
  · exact cC2_eq_zero _ e4 one_ne

theorem exists_two_pow_five_orth_even [CharP K 2] (Φ : QuadForm K (ι → K)) (px py : Fin 4 → ι)
    (hpx : Function.Injective px) (hpy : Function.Injective py) (hd : ∀ i j, py i ≠ px j)
    (hQ : ∀ i, Φ.Q (Pi.single (px i) 1) = 0)
    (hβ : ∀ i v, Φ.polar.β (Pi.single (px i) 1) v = v (py i)) (hι : 5 ≤ Fintype.card ι) :
    ∃ U : Subgroup (StatedProj (StatedOmega Φ.Q)), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  have hX := oX_mul (K := K) px py hd
  refine exists_two_pow_five_unip hX (fun v h => Xsum_oX_ind px py hpx hpy hd v h) _ ?_
  intro k
  have hxy : Φ.polar.β (Pi.single (px (evI k)) 1) (Pi.single (px (evJ k)) 1) = 0 := by
    rw [hβ]
    simp [hd]
  obtain ⟨A, hA, hAv⟩ := exists_mem_statedOmega_eichler' Φ hι (hQ (evI k)) hxy
  have hAeq : (uniMat hX (Pi.mulSingle k c2gen) : GL ι K) = A := by
    refine Units.ext ?_
    rw [coe_uniMat, Xsum_mulSingle]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply]
    rw [hAv, Φ.eichler_apply, hQ, hβ, hβ]
    simp only [oX, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq, zero_smul,
      sub_zero, one_mul]
    rw [sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq]
    abel
  rw [hAeq]
  exact hA

end Even

end CFSG.RankThree.PartOne.SLB4A
