module

public import CFSG.RankThree.PartOne.SEITZ5.URank
public import CFSG.RankThree.PartOne.SEITZ5.UCenterEx

public section

namespace CFSG.RankThree.PartOne.SEITZ5

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.RankThree.PartOne.SEITZ2

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Subfield K} {σ : K ≃+* K} {σ₀ : k ≃+* k}

omit [CharP K 2] in
theorem omega_facts (hk4 : Nat.card k = 4) {ω : K} (hωk : ω ∈ k) (hω1 : ω ≠ 1)
    (hωn : σ ω * ω = 1) : ω ^ 2 + ω + 1 = 0 ∧ σ ω = ω ^ 2 := by
  have hω0 : ω ≠ 0 := fun h => by rw [h, mul_zero] at hωn; exact zero_ne_one hωn
  have : Fintype k := Fintype.ofFinite k
  have hcard : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card]; exact hk4
  have h3 : (⟨ω, hωk⟩ : k) ^ (Fintype.card k - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (fun h => hω0 (congrArg Subtype.val h))
  have hω3 : ω ^ 3 = 1 := by
    have := congrArg (fun z : k => (z : K)) h3
    simp only [hcard, SubmonoidClass.coe_pow, Subfield.coe_one] at this
    exact this
  have hω2 : ω ^ 2 + ω + 1 = 0 := by
    have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω1)
  exact ⟨hω2, by linear_combination (-(σ ω)) * hω3 + ω ^ 2 * hωn⟩

theorem exists_hfull {N : ℕ} (hN : 4 ≤ N) (hσi : ∀ c, σ (σ c) = c)
    (hσ₀ : IsUnitaryInvolution σ₀) (hσk : ∀ c : k, σ (c : K) = ((σ₀ c : k) : K)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card (fixSub σ) = Nat.card (ratFix σ k) ^ p)
    (hr2 : Nat.card (ratFix σ k) = 2) (hk4 : Nat.card k = 4) {ω : K} (hωk : ω ∈ k)
    (hω1 : ω ≠ 1) (hωn : σ ω * ω = 1) (A : GL (Fin N) K)
    (hA : conjTr σ (A : Matrix (Fin N) (Fin N) K) * (A : Matrix (Fin N) (Fin N) K) = 1)
    (hne : (phiN hσk).range.map (conjU A hA) ≠ (phiN hσk).range) :
    ∃ e : Fin N → K, IsRat k e ∧ e ≠ 0 ∧ herm σ e e = 0 ∧
      ∀ b : fixSub σ, ∃ t ∈ (phiN hσk).range ⊔ (phiN hσk).range.map (conjU A hA),
        IsTv σ t e (b : K) := by
  classical
  obtain ⟨hω2, hσω⟩ := omega_facts hk4 hωk hω1 hωn
  obtain ⟨y, hy0, hyiso, hTy, hirr⟩ := exists_center hN hσi hσ₀ hσk A hA hne
  set R := (phiN hσk).range with hR
  set M := R ⊔ R.map (conjU A hA) with hM
  have hRM : R ≤ M := le_sup_left
  have hM_rat : ∀ a : Fin N → K, IsRat k a → herm σ a a = 0 → ∀ c : K, c ∈ k → σ c = c →
      ∃ t ∈ M, IsTv σ t a c := by
    intro a ha' hiso c hc hσc
    obtain ⟨t, htR, ht⟩ := exists_phiN_isTv hσ₀.invol hσk ha' hiso hc hσc
    exact ⟨t, hRM htR, ht⟩
  have hM_trans : ∀ x x' : Fin N → K, IsRat k x → IsRat k x' → x ≠ 0 → x' ≠ 0 →
      herm σ x x = 0 → herm σ x' x' = 0 → ∃ r ∈ M, r • x = x' := by
    intro x x' hx hx' hx0 hx'0 hxi hx'i
    obtain ⟨r, hrR, hr⟩ := exists_phiN_smul_eq (by omega) hσ₀ hσk hx hx' hx0 hx'0 hxi hx'i
    exact ⟨r, hRM hrR, hr⟩
  by_cases hrank1 : ∃ i₀ : Fin N, y i₀ ≠ 0 ∧ ∀ j, ∃ c ∈ k, y j = c * y i₀
  · obtain ⟨i₀, hi₀, hc⟩ := hrank1
    choose c hck hyc using hc
    obtain ⟨lam, hlam⟩ : ∃ lam : K, lam = y i₀ := ⟨_, rfl⟩
    have hlam0 : lam ≠ 0 := hlam ▸ hi₀
    have hyeq : y = lam • c := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hlam]
      exact hyc j
    have hw₀ : IsRat k c := fun j => hck j
    have hNlam : σ lam * lam ∉ k := fun h => hirr ⟨lam, hlam0, h, c, hw₀, hyeq⟩
    have hNne : σ lam * lam ≠ 0 := mul_ne_zero ((map_ne_zero σ).2 hlam0) hlam0
    have hw₀0 : c ≠ 0 := by
      intro h
      apply hy0
      rw [hyeq, h, smul_zero]
    have hw₀iso : herm σ c c = 0 := by
      have h3 : herm σ y y = (σ lam * lam) * herm σ c c := by
        rw [hyeq, herm_smul_left, herm_smul_right]
        ring
      rw [hyiso] at h3
      exact (mul_eq_zero.1 h3.symm).resolve_left hNne
    exact hfull_rank_one hN hσi hp hp2 hK hr2 hωk hω1 hωn hM_rat hM_trans hNlam hw₀ hw₀0 hw₀iso
      (by rw [← hyeq]; exact hTy)
  · push Not at hrank1
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hy0 (funext hcon)
    obtain ⟨j, hj⟩ := hrank1 i hi
    exact hfull_rank_two hN hσi hp hp2 hK hr2 hk4 hωk hω1 hωn hσω hω2 hM_rat hyiso hTy hi hj

end CFSG.RankThree.PartOne.SEITZ5
