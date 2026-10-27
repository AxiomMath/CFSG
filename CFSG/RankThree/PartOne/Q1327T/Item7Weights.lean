module

public import CFSG.RankThree.PartOne.N143X.WeylMatrix

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne.N143X

theorem card_centralizer_involution_dvd_eight {S : Type} [Fintype S] [DecidableEq S]
    (ν : Equiv.Perm S) (h2 : ν ^ 2 = 1) (hfix : ∀ x y, ν x = x → ν y = y → x = y)
    (hS : Fintype.card S ≤ 5) : Nat.card (Subgroup.centralizer {ν}) ∣ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (σ := ν) (p := 2) h2
  obtain ⟨m, hm⟩ : ∃ m, ν.cycleType = Multiset.replicate m 2 := ⟨_, hct⟩
  have hsum : ν.support.card = 2 * m := by
    rw [← Equiv.Perm.sum_cycleType, hm, Multiset.sum_replicate]
    simp [mul_comm]
  have hfixcard : (Finset.univ.filter fun x => ν x = x).card ≤ 1 :=
    Finset.card_le_one.2 fun x hx y hy => hfix x y (by simpa using hx) (by simpa using hy)
  have hcomp : ν.support.card + (Finset.univ.filter fun x => ν x = x).card = Fintype.card S := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S))
      (fun x => ν x ≠ x)
    simpa [Equiv.Perm.support, add_comm] using this
  have hm2 : m ≤ 2 := by
    have := Finset.card_le_univ ν.support
    omega
  have hfact : (Fintype.card S - ν.cycleType.sum).factorial = 1 := by
    rw [Nat.factorial_eq_one, Equiv.Perm.sum_cycleType]
    omega
  rw [Equiv.Perm.nat_card_centralizer, hfact, hm, Multiset.prod_replicate, one_mul]
  interval_cases m <;> simp

theorem FaithfulSmallSym.card_dvd_eight {H : Type} [Group H] {d : ℕ} (h : FaithfulSmallSym H d)
    (hd : d ≤ 5) : Nat.card H ∣ 8 := by
  obtain ⟨S, hS, φ, hdS, hφ, ν, hν2, hνfix, hcomm⟩ := h
  have : Fintype S := Fintype.ofFinite S
  classical
  let φ' : H →* Subgroup.centralizer {ν} := φ.codRestrict _ fun x =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm x)
  have hφ' : Function.Injective φ' := fun a b hab => hφ (congrArg Subtype.val hab)
  have h1 := Subgroup.card_dvd_of_injective φ' hφ'
  have h2 := card_centralizer_involution_dvd_eight ν hν2 hνfix (by
    rw [← Nat.card_eq_fintype_card]
    omega)
  exact h1.trans h2

section Matrices

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (E : Subgroup (GL ι K))

theorem card_normalizer_range_dvd_eight {p : ℕ} (hp : (p : K) ≠ 0) (hp2 : p % 2 = 1)
    [IsElementaryAbelian p E] (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hEJ : ∀ e ∈ E, ((e : GL ι K) : Matrix ι ι K)ᵀ * J * ((e : GL ι K) : Matrix ι ι K) = J)
    (hd : Fintype.card ι ≤ 5) : Nat.card E.normalizerMonoidHom.range ∣ 8 :=
  FaithfulSmallSym.card_dvd_eight (faithfulSmallSym_normalizer_range E hp hp2 J hJ hEJ) hd

end Matrices

theorem card_dvd_eight_of_matrix_model {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) {T : Type} [Group T]
    (e : T ≃* CFSG.Assembly.LowTwoRank.StatedProj M) {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1)
    (hpK : (p : K) ≠ 0) {d : ℕ}
    (hd : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ M → c ^ d = 1) (hpd : ¬ p ∣ d)
    (J : Matrix ι ι K) (hJ : J.det ≠ 0)
    (hMJ : ∀ g ∈ M, ((g : GL ι K) : Matrix ι ι K)ᵀ * J * ((g : GL ι K) : Matrix ι ι K) = J)
    {E : Subgroup T} (hE : IsElementaryAbelian p E) (hcard : Fintype.card ι ≤ 5) :
    Nat.card E.normalizerMonoidHom.range ∣ 8 := by
  obtain ⟨F, hF, hFM, -, hdvd⟩ := exists_cover_of_matrix_model M e hp hd hpd hE
  exact hdvd.trans (card_normalizer_range_dvd_eight F hpK hp2 J hJ
    (fun g hg => hMJ g (hFM hg)) hcard)

end CFSG.RankThree.PartOne.Q1327T
