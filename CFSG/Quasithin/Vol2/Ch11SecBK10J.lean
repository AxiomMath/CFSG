module

public import CFSG.Quasithin.Vol2.Ch11SecBK10H
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.Quasithin.Vol2.Ch11SecBK10A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L2

open Matrix CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

@[expose] def jSL : SL(2, K) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

omit [Finite K] in
theorem two_dvd_card_psl2 : 2 ∣ Nat.card (PSL2 K) := by
  set x := psl2QuotientMap K jSL with hx
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow, psl2QuotientMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by simp, ?_⟩
    ext i j
    rw [sq, Matrix.SpecialLinearGroup.coe_mul]
    fin_cases i <;> fin_cases j <;> simp [jSL, Matrix.mul_apply, Fin.sum_univ_two]
  have hx1 : x ≠ 1 := by
    rw [hx, psl2QuotientMap, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    rintro ⟨r, -, hr⟩
    have h1 := congrFun (congrFun hr 0) 1
    simp [jSL] at h1
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  rw [← hord]
  exact orderOf_dvd_natCard x

omit [Finite K] in
theorem pglAction_sq_mem_inner (G : GL (Fin 2) K) :
    pglAction K (ProjGenLinGroup.mk G) ^ 2 ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) := by
  set d := GeneralLinearGroup.det G with hd
  set G' : GL (Fin 2) K := G ^ 2 * GeneralLinearGroup.scalar (Fin 2) d⁻¹ with hG'
  have hdet : (G' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have h1 : GeneralLinearGroup.det G' = 1 := by
      rw [hG', map_mul, map_pow]
      have h2 : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) d⁻¹) = d⁻¹ ^ 2 := by
        ext
        simp [GeneralLinearGroup.scalar]
      rw [h2, inv_pow, ← hd, mul_inv_cancel]
    have := congrArg (fun u : Kˣ => (u : K)) h1
    simpa using this
  set A : SL(2, K) := ⟨G', hdet⟩ with hA
  have hmk : ProjGenLinGroup.mk G' = ProjGenLinGroup.mk G ^ 2 := by
    rw [hG', map_mul, map_pow, ProjGenLinGroup.mk_scalar, mul_one]
  have h1 : pglAction K (ProjGenLinGroup.mk G) ^ 2 =
      MulAut.conj (psl2QuotientMap K A) := by
    rw [← map_pow, ← hmk, ← pglAction_toPGL]
    congr 1
    change ProjGenLinGroup.mk G' = ProjGenLinGroup.mk (SpecialLinearGroup.toGL A)
    congr 1
    ext
    rfl
  rw [h1]
  exact ⟨_, rfl⟩

theorem eq_one_of_isCoprimePrimeAut_small {p f : ℕ} (hp : p.Prime) (hf : f ≤ 2)
    (hK : Nat.card K = p ^ f) {β : MulAut (PSL2 K)} (hβ : IsCoprimePrimeAut β) : β = 1 := by
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hr2 : r ≠ 2 := fun h => hrX (h ▸ two_dvd_card_psl2)
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h | h
    · subst h
      rw [pow_zero] at hK
      exact absurd hK (Finite.one_lt_card (α := K)).ne'
    · exact h
  obtain ⟨G, hG⟩ := exists_rep β
  set τ := galPart β with hτ
  have hτr : τ ^ r = 1 := by rw [hτ, ← map_pow, hβr, map_one]
  have hτ1 : τ = 1 := by
    obtain ⟨hcard, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK
    have : Finite (RingAut K) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have h1 : orderOf τ ∣ f := by
      rw [← hcard]
      exact orderOf_dvd_natCard τ
    have h2 : orderOf τ ∣ r := orderOf_dvd_of_pow_eq_one hτr
    rcases (Nat.dvd_prime hr).mp h2 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exfalso
      rw [h] at h1
      have h3 := Nat.le_of_dvd hf0 h1
      have h4 := hr.two_le
      omega
  rw [hτ1, map_one, mul_one] at hG
  obtain ⟨m, hm⟩ := hr.odd_of_ne_two hr2
  have hβin : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSL2 K) := by
    have h1 : β = (β ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = r + 1 by omega, pow_succ, hβr, one_mul]
    rw [h1]
    refine Subgroup.pow_mem _ ?_ _
    rw [hG]
    exact pglAction_sq_mem_inner G
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ hβin

theorem torusRigid_psl2_small {p f : ℕ} (hp : p.Prime) (hf : f ≤ 2)
    (hK : Nat.card K = p ^ f) : TorusRigid (PSL2 K) :=
  torusRigid_of_forall_eq_one fun _ hβ => eq_one_of_isCoprimePrimeAut_small hp hf hK hβ

end BK10.L2

end CFSG.Quasithin.Vol2.Ch11.SecD
