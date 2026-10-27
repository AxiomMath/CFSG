module

public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField

public section

namespace CFSG.StandardType.ExcFieldAutCentRankF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

private theorem arith_aux {p f k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (h1 : 2 * f ∣ p * k) (h2 : ¬ 2 * f ∣ k) :
    ∃ e m : ℕ, 1 ≤ e ∧ f = p * e ∧ k = 2 * e * m ∧ ¬ p ∣ m := by
  have hpf : p ∣ 2 * f := by
    by_contra h
    exact h2 (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm h1)
  have hpf' : p ∣ f := by
    rcases (Nat.Prime.dvd_mul hp).1 hpf with h | h
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h) hp2
    · exact h
  obtain ⟨e, rfl⟩ := hpf'
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h
      simp at hf
    · exact h
  have h3 : 2 * e ∣ k := by
    have h4 : p * (2 * e) ∣ p * k := by
      have h5 : 2 * (p * e) = p * (2 * e) := by ring
      rwa [h5] at h1
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos h4
  obtain ⟨m, rfl⟩ := h3
  refine ⟨e, m, he, rfl, by ring, ?_⟩
  rintro ⟨m', rfl⟩
  apply h2
  exact ⟨m', by ring⟩

section Form


private theorem form_aux {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (adjointGroup ReeTag.F4.tag K)}
    (hα : α ^ p = 1) (hnin : ∀ h : adjointGroup ReeTag.F4.tag K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (g : adjointGroup ReeTag.F4.tag K), σ ≠ 1 ∧ σ ^ p = 1 ∧
      α = MulAut.conj g * entrywiseAdjointAut ReeTag.F4.tag σ := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K ReeTag.F4.prime
  have hK : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]; rfl
  have hf : 1 ≤ (n : ℕ) := n.pos
  obtain ⟨hord, hNF, ⟨Θ, hΘ, -, hΘker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hNF α
  have hΘα := hΘ α g k hgk
  have h2f : 2 * (n : ℕ) ∣ p * (k : ℕ) := by
    have h1 : Θ (α ^ p) = 1 := by rw [hα]; exact map_one Θ
    rw [map_pow, hΘα] at h1
    have h2 : ((p * (k : ℕ) : ℕ) : ZMod (2 * (n : ℕ))) = 0 := by
      have := congrArg Multiplicative.toAdd h1
      simpa using this
    exact (ZMod.natCast_eq_zero_iff _ _).1 h2
  have h2k : ¬ 2 * (n : ℕ) ∣ (k : ℕ) := by
    intro h
    have h0 : ((k : ℕ) : ZMod (2 * (n : ℕ))) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
    have : Θ α = 1 := by rw [hΘα, h0]; rfl
    have hmem : α ∈ Θ.ker := this
    rw [hΘker] at hmem
    obtain ⟨h', hh'⟩ := hmem
    exact hnin h' hh'.symm
  obtain ⟨e, m, he, hfe, hkm, hpm⟩ := arith_aux hp hp2 hf h2f h2k
  obtain ⟨fr, hfr, hordfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have hσc : ∀ c, (fr ^ (e * m)) c = c ^ ReeTag.F4.prime ^ (e * m) :=
    ringAut_pow_apply_of_frobenius hfr (e * m)
  refine ⟨fr ^ (e * m), g, ?_, ?_, ?_⟩
  · intro h1
    have hd : orderOf fr ∣ e * m := orderOf_dvd_of_pow_eq_one h1
    rw [hordfr, hfe] at hd
    exact hpm (Nat.dvd_of_mul_dvd_mul_right he (by simpa [mul_comm] using hd))
  · rw [← pow_mul, show e * m * p = (n : ℕ) * m by rw [hfe]; ring, pow_mul, ← hordfr,
      pow_orderOf_eq_one, one_pow]
  · rw [hgk]
    congr 1
    rw [hkm, show 2 * e * m = 2 * (e * m) by ring, finiteExceptionalAut_pow_two_mul]
    exact (entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hσc).symm

theorem exists_field_form {K : Type} [Field K] [Finite K]
    [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α : MulAut (adjointGroup .F4 K)}
    (hα : α ^ p = 1) (hnin : ∀ h : adjointGroup .F4 K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (g : adjointGroup .F4 K), σ ≠ 1 ∧ σ ^ p = 1 ∧
      α = MulAut.conj g * entrywiseAdjointAut .F4 σ := by
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  exact form_aux hp hp2 hα hnin

end Form

end CFSG.StandardType.ExcFieldAutCentRankF4
