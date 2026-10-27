module

public import CFSG.RankThree.PartOne.KE.CTCasesE6Glue
public import CFSG.RankThree.PartOne.KE.CTCasesCyclo
public import CFSG.RankThree.Chevalley.SteinbergBNExceptionalCyclotomicExhaustion

public section

namespace CFSG.RankThree.PartOne.KE.CTCyclo

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module
open CFSG.RankThree.Chevalley (exhaustionPhi exhaustionMinusFactors
  pow_sub_one_eq_prod_exhaustionPhi exists_dvd_exhaustionPhi_of_dvd_prod)

theorem exhaustionPhi_eq_cyclotomic {e : ℕ} (he : e ∈ cycloIdx) :
    exhaustionPhi e = cyclotomic e ℤ := by
  simp only [cycloIdx, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  · rw [cyclotomic_int_1]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_2]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_3]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_4]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_5]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_6]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_7]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_8]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_10]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_12]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_14]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_15]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_20]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_24]
    simp only [exhaustionPhi]
  · rw [cyclotomic_int_30]
    simp only [exhaustionPhi]

theorem key_data {p m q : ℕ} (hp : p.Prime) (hp7 : 7 < p) (hm : m ∈ cycloIdx)
    (h : (p : ℤ) ∣ (exhaustionPhi m).eval (q : ℤ)) :
    orderOf (q : ZMod p) = m ∧
      ∀ e ∈ cycloIdx, e ≠ m → ¬ (p : ℤ) ∣ (exhaustionPhi e).eval (q : ℤ) := by
  have hord : ∀ e ∈ cycloIdx, (p : ℤ) ∣ (exhaustionPhi e).eval (q : ℤ) →
      orderOf (q : ZMod p) = e := fun e he hd =>
    orderOf_eq_of_dvd_cyclotomic hp (not_dvd_of_mem_cycloIdx hp hp7 he)
      (by rwa [← exhaustionPhi_eq_cyclotomic he])
  exact ⟨hord m hm h, fun e he hne hd => hne ((hord e he hd).symm.trans (hord m hm h))⟩

theorem exists_cofactor {p m d q : ℕ} (hp : p.Prime) (hq : 1 ≤ q)
    (hm : m ∈ exhaustionMinusFactors d)
    (hd : d ∈ ([2, 5, 6, 8, 9, 10, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hnd : (exhaustionMinusFactors d).Nodup) (hsub : ∀ e ∈ exhaustionMinusFactors d, e ∈ cycloIdx)
    (hne : ∀ e ∈ cycloIdx, e ≠ m → ¬ (p : ℤ) ∣ (exhaustionPhi e).eval (q : ℤ)) :
    ∃ R : ℤ, ((q ^ d - 1 : ℕ) : ℤ) = (exhaustionPhi m).eval (q : ℤ) * R ∧ ¬ (p : ℤ) ∣ R := by
  have hcast : ((q ^ d - 1 : ℕ) : ℤ) = (q : ℤ) ^ d - 1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one]
  refine ⟨(((exhaustionMinusFactors d).erase m).map fun e => (exhaustionPhi e).eval (q : ℤ)).prod,
    ?_, ?_⟩
  · rw [hcast, pow_sub_one_eq_prod_exhaustionPhi _ hd]
    exact (List.prod_map_erase (fun e => (exhaustionPhi e).eval (q : ℤ)) hm).symm
  · intro hdvd
    obtain ⟨e, he, hpe⟩ := exists_dvd_exhaustionPhi_of_dvd_prod hp hdvd
    rw [hnd.mem_erase_iff] at he
    exact hne e (hsub e he.2) he.1 hpe

theorem exists_annihilator_of_span {n k : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (α : Fin n → ℤ)
    {p : ℕ} (x : ℤ)
    (h : ¬ (p : ℤ) ∣ ((Submodule.span ℤ (Set.range fun j : Fin k =>
      (M ^ (j : ℕ)) *ᵥ α)).toAddSubgroup.index : ℤ)) :
    ∃ A : ℤ[X], (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval x := by
  have hle : Submodule.span ℤ (Set.range fun j : Fin k => (M ^ (j : ℕ)) *ᵥ α) ≤
      orbitLattice M α := by
    refine Submodule.span_mono ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨(j : ℕ), rfl⟩
  obtain ⟨A, hA, hpA⟩ := exists_annihilator_of_index M
    (Submodule.span ℤ (Set.range fun j : Fin k => (M ^ (j : ℕ)) *ᵥ α)) x h
  exact ⟨A, fun β => hle (hA β), hpA⟩

end CFSG.RankThree.PartOne.KE.CTCyclo

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  Polynomial Matrix Module

theorem ordProj_card_adjointGroup_E8 {K : Type} [Field K] [Finite K] {p m d₀ n₀ : ℕ} {R : ℤ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₀ : d₀ ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ))
    (hrest : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), d ≠ d₀ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac : ((Nat.card K ^ d₀ - 1 : ℕ) : ℤ) = n₀ * R) (hR : ¬ (p : ℤ) ∣ R) :
    ordProj[p] (Nat.card (adjointGroup .E8 K)) = ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd₀pos : 0 < d₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₀
    omega
  have hN : Nat.card K ^ d₀ - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ d₀ := Nat.one_lt_pow hd₀pos.ne' (by omega)
    omega
  rw [(CFSG.RankThree.OrdinaryECrossPrime.ordinary_E_exact_cross_prime_order_parts hp hp3 hpq).2.2,
    CTE6.prod_map_ordProj_eq_single (by omega) hord (by decide) hd₀ hrest]
  exact CTE6.ordProj_eq_of_int_factor hn₀ hN hfac hR

theorem ordProj_card_adjointGroup_F4 {K : Type} [Field K] [Finite K] {p m d₀ n₀ : ℕ} {R : ℤ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K)
    (hcard : Nat.card (adjointGroup .F4 K) = Nat.card K ^ 24 * (Nat.card K ^ 2 - 1) *
      (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) * (Nat.card K ^ 12 - 1))
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = m)
    (hd₀ : d₀ ∈ ([2, 6, 8, 12] : List ℕ))
    (hrest : ∀ d ∈ ([2, 6, 8, 12] : List ℕ), d ≠ d₀ → ¬ m ∣ d)
    (hn₀ : n₀ ≠ 0) (hfac : ((Nat.card K ^ d₀ - 1 : ℕ) : ℤ) = n₀ * R) (hR : ¬ (p : ℤ) ∣ R) :
    ordProj[p] (Nat.card (adjointGroup .F4 K)) = ordProj[p] n₀ := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hd₀pos : 0 < d₀ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd₀
    omega
  have hN : Nat.card K ^ d₀ - 1 ≠ 0 := by
    have : 1 < Nat.card K ^ d₀ := Nat.one_lt_pow hd₀pos.ne' (by omega)
    omega
  have hcard' : Nat.card (adjointGroup .F4 K) = Nat.card K ^ 24 *
      (([2, 6, 8, 12] : List ℕ).map fun d => Nat.card K ^ d - 1).prod := by
    rw [hcard]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [hcard', CFSG.RankThree.OrdinaryECrossPrime.ordProj_pow_mul_prod hp hpq hq 24
    ([2, 6, 8, 12] : List ℕ) (by decide),
    CTE6.prod_map_ordProj_eq_single (by omega) hord (by decide) hd₀ hrest]
  exact CTE6.ordProj_eq_of_int_factor hn₀ hN hfac hR

theorem cyclic_sylow_of_inputs_F4 (hmain : CyclicTorusTheoremF4)
    {M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} (hM : IsWeylMatrix .F4 M)
    {v : Fin Tag.F4.rank → ℤ}
    (hv1 : LinearIndependent ℤ (fun j : Fin Tag.F4.rank => (M ^ (j : ℕ)) *ᵥ v))
    (hv2 : Submodule.span ℤ (Set.range fun j : Fin Tag.F4.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (hc0 : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {n₀ : ℕ} (hn₀ : n₀ ≠ 0)
    (hev : M.charpoly.eval (Nat.card K : ℤ) = (n₀ : ℤ))
    (hann : ∀ α : Fin Tag.F4.rank → ℤ, IsRoot .F4 α → ∃ A : ℤ[X],
      (∀ β, (aeval M A) *ᵥ β ∈ orbitLattice M α) ∧ ¬ (p : ℤ) ∣ A.eval (Nat.card K : ℤ))
    (hpart : ordProj[p] (Nat.card (adjointGroup .F4 K)) = ordProj[p] n₀) :
    CyclicSylowConclusion .F4 K p n₀ 1 := by
  have hnat : (M.charpoly.eval (Nat.card K : ℤ)).natAbs = n₀ := by
    rw [hev, Int.natAbs_natCast]
  have hne : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hev]
    exact_mod_cast hn₀
  have key := hmain M hM v hv1 hv2 hc0 K p hp hp3 hpq hne hann (by rw [hnat]; exact hpart)
  rwa [hnat] at key

end CFSG.RankThree.PartOne.KE
