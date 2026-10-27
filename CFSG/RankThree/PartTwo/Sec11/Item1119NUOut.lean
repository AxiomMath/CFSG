module

public import CFSG.RankThree.PartTwo.KFacts.K72FieldKind
public import CFSG.Dihedral.GorensteinWalter.PGL2SquareRange
public import CFSG.GH74.GLS.IVK.L2.Fixed

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NU

open CFSG.GorensteinWalter (PSL2 PGL2 pgl2_mem_psl2Range_of_pow_odd)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  (pglAction semilinearAction semilinearAction_inl pglAction_toPGL semilinearAction_surjective)

theorem aux_ringAut_pow_eq_one {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ n) (σ : K ≃+* K) : σ ^ n = 1 := by
  have h0 := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  have hm : orderOf σ ≠ 0 := by
    intro h00
    rw [h00, pow_zero] at h0
    exact absurd h0 (ne_of_lt Finite.one_lt_card)
  have hdvd : Nat.card (CFSG.GH74.GLS.IVK.fixedField σ) ∣ p ^ n := by
    have hd := dvd_pow_self (Nat.card (CFSG.GH74.GLS.IVK.fixedField σ)) hm
    rwa [h0, hK] at hd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have h2 : (p ^ j) ^ orderOf σ = p ^ n := by
    rw [← hj, h0, hK]
  rw [← pow_mul] at h2
  have h3 : j * orderOf σ = n := Nat.pow_right_injective hp.two_le h2
  exact orderOf_dvd_iff_pow_eq_one.mp (Dvd.intro_left j h3)

theorem isInnerAut_pow_of_pow_three {K : Type} [Field K] [Finite K] {p n : ℕ} [CharP K p]
    (hp : p.Prime) (hK : Nat.card K = p ^ n) {ω : MulAut (PSL2 K)} {k : ℕ}
    (hω : ω ^ 3 ^ k = 1) : KFacts.IsInnerAut (ω ^ n) := by
  obtain ⟨x, rfl⟩ := semilinearAction_surjective K ω
  have hr : (x ^ n).right = x.right ^ n := map_pow SemidirectProduct.rightHom x n
  have hright : (x ^ n).right = 1 := by
    rw [hr]
    exact aux_ringAut_pow_eq_one hp hK x.right
  obtain ⟨g, hg⟩ : ∃ g : PGL2 K, x ^ n = SemidirectProduct.inl g := by
    have h := SemidirectProduct.inl_left_mul_inr_right (x ^ n)
    rw [hright, map_one, mul_one] at h
    exact ⟨_, h.symm⟩
  have hpg : semilinearAction K (x ^ n) = pglAction K g := by
    rw [hg, semilinearAction_inl]
  have hωn : semilinearAction K x ^ n = pglAction K g :=
    (map_pow (semilinearAction K) x n).symm.trans hpg
  have hpow : (semilinearAction K x ^ n) ^ 3 ^ k = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hω, one_pow]
  have hg3 : g ^ 3 ^ k = 1 := by
    apply KFacts.pglAction_injective
    rw [map_pow, map_one, ← hωn]
    exact hpow
  have h3 : Odd (3 : ℕ) := by decide
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp
    (pgl2_mem_psl2Range_of_pow_odd (h3.pow) hg3)
  unfold KFacts.IsInnerAut
  refine MonoidHom.mem_range.mpr ⟨y, ?_⟩
  rw [hωn, ← hy, pglAction_toPGL]

end CFSG.RankThree.PartTwo.Sec11.Item1119NU

end
