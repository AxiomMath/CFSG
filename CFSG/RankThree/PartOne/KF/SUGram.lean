module

public import CFSG.RankThree.PartOne.KF.GramMat
public import CFSG.RankThree.PartOne.KF.D8Matrix

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

variable {p : ℕ} {K : Type} [Field K] {n : ℕ} [NeZero n]

@[expose] def d8EvU (c : Fin 5) (a b : Kˣ) : Kˣ :=
  match c with
  | 0 => a
  | 1 => b
  | 2 => b⁻¹
  | 3 => a⁻¹
  | 4 => 1

@[expose] def dvecN (n : ℕ) [NeZero n] (a b : Kˣ) : Fin n → Kˣ := fun i => d8EvU (d8Cls n i) a b

theorem d8Vec_eq_dvecN (v : D8Mod p K) :
    d8Vec n v = dvecN n ((v.1 : rootsOfUnity p K) : Kˣ) ((v.2 : rootsOfUnity p K) : Kˣ) := by
  funext i
  simp only [d8Vec, dvecN]
  generalize d8Cls n i = c
  fin_cases c <;> rfl

@[expose] def dvecNHom (n : ℕ) [NeZero n] : Kˣ × Kˣ →* (Fin n → Kˣ) where
  toFun x := dvecN n x.1 x.2
  map_one' := by
    funext i
    simp only [dvecN]
    generalize d8Cls n i = c
    fin_cases c <;> simp [d8EvU]
  map_mul' x y := by
    funext i
    simp only [dvecN, Pi.mul_apply]
    generalize d8Cls n i = c
    fin_cases c <;> simp [d8EvU, mul_comm]

theorem prod_dvecN (hn : n = 4 ∨ n = 5) (a b : Kˣ) : ∏ i, dvecN n a b i = 1 := by
  rcases hn with rfl | rfl
  · simp [Fin.prod_univ_four, dvecN, d8Cls, d8EvU]
  · simp [Fin.prod_univ_five, dvecN, d8Cls, d8EvU]

theorem dvecN_gram (hc : D8Comb n) (σ : K ≃+* K) {a b : Kˣ} (ha : σ (a : K) = a)
    (hb : σ (b : K) = b) (i : Fin n) :
    σ (dvecN n a b i : K) * (dvecN n a b (Fin.rev i) : K) = 1 := by
  have h1 : ∀ c : Fin 5, σ (d8EvU c a b : K) = (d8EvU c a b : K) := by
    intro c
    fin_cases c <;> simp [d8EvU, ha, hb, map_inv₀]
  have h2 : ∀ c : Fin 5, (d8EvU c a b : Kˣ) * d8EvU (d8Rho c) a b = 1 := by
    intro c
    fin_cases c <;> simp [d8EvU, d8Rho]
  simp only [dvecN]
  rw [h1, hc.cls_rev]
  rw [← Units.val_mul, h2, Units.val_one]

theorem diagU_dvecN_mem_SU (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K) {a b : Kˣ}
    (ha : σ (a : K) = a) (hb : σ (b : K) = b) :
    (diagU (dvecN n a b) : GL (Fin n) K) ∈ SU σ n := by
  refine mem_SU.mpr ⟨?_, diagU_gram σ (dvecN_gram hc σ ha hb)⟩
  rw [det_diagU, ← Units.coe_prod, prod_dvecN hn, Units.val_one]

omit [NeZero n] in
theorem permGL_mem_SU [CharP K 2] (σ : K ≃+* K) (τ : Equiv.Perm (Fin n))
    (h : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) : (permGL τ : GL (Fin n) K) ∈ SU σ n :=
  mem_SU.mpr ⟨det_permGL τ, permGL_gram σ τ h⟩

theorem d8Vec_mem_SU (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (σ : K ≃+* K)
    (hσ : ∀ u : rootsOfUnity p K, σ ((u : Kˣ) : K) = (u : Kˣ)) (v : D8Mod p K) :
    (diagU (d8Vec n v) : GL (Fin n) K) ∈ SU σ n := by
  rw [d8Vec_eq_dvecN]
  exact diagU_dvecN_mem_SU hn hc σ (hσ v.1) (hσ v.2)

end CFSG.RankThree.PartOne.KFU
