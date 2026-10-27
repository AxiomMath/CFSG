module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Census.CommonUnipotent
import CFSG.RankThree.PartTwo.Census.QuotientWitness

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census Matrix

variable {K : Type} [Field K] {n : ℕ}

theorem two_ne_zero_of_charP {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h0
  have := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h0)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem le_localRank_PSL_of_unipotent [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (s : Fin n → K) (hs : ∀ i, s i * s i = 1) (hdet : (diagonal s).det = 1) {i₀ j₀ : Fin n}
    (hij : s i₀ ≠ s j₀) {W : Type} [AddCommGroup W] (X : W →+ Matrix (Fin n) (Fin n) K)
    (hXi : Function.Injective X) (hXX : ∀ a b, X a * X b = 0) (hXd : ∀ a i, X a i i = 0)
    (hXs : ∀ a i j, X a i j ≠ 0 → s i = s j) {k : ℕ} (hW : Nat.card W = p ^ k) :
    k ≤ localRank p (ProjectiveSpecialLinearGroup (Fin n) K) := by
  have hp : p.Prime := Fact.out
  set t : SpecialLinearGroup (Fin n) K := ⟨diagonal s, hdet⟩ with ht
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    refine Subtype.ext ?_
    change diagonal s * diagonal s = 1
    rw [diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hs)
  have htN : t ∉ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    intro h
    have hsc := SpecialLinearGroup.scalar_eq_self_of_mem_center h i₀
    have h' := congrArg (fun M : Matrix (Fin n) (Fin n) K => M j₀ j₀) hsc
    change scalar (Fin n) (diagonal s i₀ i₀) j₀ j₀ = diagonal s j₀ j₀ at h'
    simp only [diagonal_apply_eq, scalar_apply] at h'
    exact hij h'
  set φ := unipotentSL X hXX (fun a => det_one_add_of_mul_self_eq_zero p (hXX a a))
  have hφ : Function.Injective φ := unipotentSL_injective _ _ hXi
  have hWp : ∀ w : W, p • w = 0 := fun w => hXi (by
    rw [map_nsmul, map_zero, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero K p, zero_smul])
  refine le_localRank_quotient_of_commute _ hp (isElemAbelian_range_of_nsmul hWp φ)
    (by rw [card_range_of_injective hφ, hW]) ?_ htN (by rw [ht2]; exact Subgroup.one_mem _) ?_
  · rw [eq_bot_iff]
    rintro x hx
    obtain ⟨⟨a, rfl⟩, hxc⟩ := Subgroup.mem_inf.mp hx
    have hsc := SpecialLinearGroup.scalar_eq_self_of_mem_center hxc i₀
    have h0 : X a.toAdd = 0 := eq_zero_of_one_add_eq_scalar (fun i => hXd _ i) i₀ hsc.symm
    have ha : a = 1 := Multiplicative.toAdd.injective (hXi (h0.trans (map_zero _).symm))
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · rintro _ ⟨a, rfl⟩
    refine Subtype.ext ?_
    change (1 + X a.toAdd) * diagonal s = diagonal s * (1 + X a.toAdd)
    exact one_add_mul_diagonal_comm (hXs _)

theorem le_localRank_PSL_three [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : f ≤ localRank p (ProjectiveSpecialLinearGroup (Fin 3) K) := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  refine le_localRank_PSL_of_unipotent (s := ![-1, -1, 1]) (i₀ := 0) (j₀ := 2)
    (fun i => by fin_cases i <;> simp) (by simp [det_diagonal, Fin.prod_univ_three])
    (by simpa using hne) (singleAddMonoidHom (0 : Fin 3) (1 : Fin 3)) ?_ ?_ ?_ ?_ hK
  · intro a b h
    simpa using congrFun (congrFun h 0) 1
  · intro a b
    simp
  · intro a i
    fin_cases i <;> simp
  · intro a i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[expose] def pairRootMap (K : Type) [Field K] : K × K →+ Matrix (Fin 4) (Fin 4) K :=
  (singleAddMonoidHom (0 : Fin 4) (1 : Fin 4)).coprod (singleAddMonoidHom (2 : Fin 4) (3 : Fin 4))

theorem pairRootMap_apply (a : K × K) :
    pairRootMap K a = single 0 1 a.1 + single 2 3 a.2 :=
  rfl

theorem le_localRank_PSL_four [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) : 2 * f ≤ localRank p (ProjectiveSpecialLinearGroup (Fin 4) K) := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by linear_combination -h)
  refine le_localRank_PSL_of_unipotent (s := ![-1, -1, 1, 1]) (i₀ := 0) (j₀ := 2)
    (fun i => by fin_cases i <;> simp) (by simp [det_diagonal, Fin.prod_univ_four])
    (by simpa using hne) (pairRootMap K) ?_ ?_ ?_ ?_ (by rw [Nat.card_prod, hK, two_mul, pow_add])
  · intro a b h
    have h1 := congrFun (congrFun h 0) 1
    have h2' := congrFun (congrFun h 2) 3
    simp [pairRootMap_apply] at h1 h2'
    exact Prod.ext h1 h2'
  · intro a b
    simp [pairRootMap_apply, add_mul, mul_add]
  · intro a i
    fin_cases i <;> simp [pairRootMap_apply]
  · intro a i j h
    fin_cases i <;> fin_cases j <;> simp_all [pairRootMap_apply]

end CFSG.RankThree.PartOne.Census3
