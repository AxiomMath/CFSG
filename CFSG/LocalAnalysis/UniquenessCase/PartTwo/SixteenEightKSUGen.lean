module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSUGenA
public import CFSG.Open.StatedDefs
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits

theorem s16k_fixNc_statedSU_of_elem {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    {n : ℕ} (hn : 4 ≤ n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)} (hEΓ : E ≤ StatedSU n 2 K)
    (hE : ∀ x ∈ E, x ^ p = 1) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : p ^ 3 ≤ Nat.card E) : FixNc (StatedSU n 2 K) p := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard2 : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI : CharP K 2 := charP_of_card_sq (p := 2) (f := 1) hcard2
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hcard2
  have hSU : SUid σ n = StatedSU n 2 K := SUid_eq_statedSU (p := 2) (f := 1) hcard2 n
  have hfixnorm : ∀ x : K, σ x = x → x = 0 ∨ x = 1 := by
    intro x hx
    have hx2 : x ^ 2 = x := by
      have h := hx
      rwa [show σ = unitaryInvolution K 2 1 from rfl, unitaryInvolution_apply, pow_one] at h
    have h : x * (x - 1) = 0 := by linear_combination hx2
    rcases mul_eq_zero.mp h with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  have hnorm : ∀ v : Fin n → K, herm σ v v = 0 ∨ herm σ v v = 1 :=
    fun v => s16k_herm_self_eq_zero_or_one hσ hfixnorm v
  have hpK : ¬ p ∣ Nat.card K := by
    intro hdvd
    rw [hK] at hdvd
    have hle : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  obtain ⟨B, U, g, hBE, hBcard, hgE, hUne, hUinv, hBfix, hgnofix⟩ :=
    s16g_exists_fixing_space (ι := Fin n) hp hpK E hE hc hcard
  have hgpow : g ^ p = 1 := hE g hgE
  have hdim : 2 ≤ Module.finrank K U :=
    s16k_finrank_two_of_nofix hK hp hp5 g hgpow U hUne (fun u hu => hUinv g hgE u hu) hgnofix
  obtain ⟨u, huU, hu0, hu⟩ := s16k_exists_herm_eq_zero_of_two_le_finrank hσ hnorm U hdim
  have hEΓ' : E ≤ SUid σ n := by rw [hSU]; exact hEΓ
  have hpK' : (p : K) ≠ 0 := by
    intro h
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp h
    have hpeq : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2
    omega
  have hBinv : (Nat.card ↥B : K) ≠ 0 := by
    rw [hBcard, Nat.cast_pow]
    exact pow_ne_zero _ hpK'
  obtain ⟨w, hww, hwfix⟩ := s16k_exists_herm_ne_zero_of_fixed hσ B
    (fun b hb => hEΓ' (hBE hb)) hBinv U hUne hBfix
  obtain ⟨l, hl⟩ := exists_smul_norm_one hσ hww
  let w1 : Fin n → K := l • w
  have hw1 : herm σ w1 w1 = 1 := hl
  have hw1fix : ∀ b ∈ B, (b : Matrix (Fin n) (Fin n) K) *ᵥ w1 = w1 := by
    intro b hb
    rw [show w1 = l • w from rfl, Matrix.mulVec_smul, hwfix b hb]
  let wfam : Bool → Fin n → K := fun k => if k then w1 else u
  have hwfam_fix : ∀ k, ∀ b ∈ B, (b : Matrix (Fin n) (Fin n) K) *ᵥ wfam k = wfam k := by
    intro k b hb
    cases k
    · show (b : Matrix (Fin n) (Fin n) K) *ᵥ u = u
      exact hBfix b hb u huU
    · show (b : Matrix (Fin n) (Fin n) K) *ᵥ w1 = w1
      exact hw1fix b hb
  have hn3 : 3 ≤ n := by omega
  have hconj : ∀ a : Fin n → K, a ≠ 0 →
      ∃ k, ∃ A ∈ StatedSU n 2 K, (A : Matrix (Fin n) (Fin n) K) *ᵥ wfam k = a := by
    intro a ha
    rcases hnorm a with ha0 | ha1
    · obtain ⟨t, _htT, ht⟩ := exists_mem_T_smul_eq_of_iso hσ hn3 hu0 hu ha ha0
      refine ⟨false, (t : Matrix.GeneralLinearGroup (Fin n) K), ?_, ?_⟩
      · rw [← hSU]; exact t.2
      · rw [show wfam false = u from rfl]
        simpa only [smul_def] using ht
    · obtain ⟨t, _htT, ht⟩ := exists_mem_T_smul_eq_of_norm_one hσ (Or.inl hn) hw1 ha1
      refine ⟨true, (t : Matrix.GeneralLinearGroup (Fin n) K), ?_, ?_⟩
      · rw [← hSU]; exact t.2
      · rw [show wfam true = w1 from rfl]
        simpa only [smul_def] using ht
  exact s16g_fixNc_of_conj (StatedSU n 2 K) hp B (hBE.trans hEΓ) hBcard
    (fun x hx => hE x (hBE hx)) wfam hwfam_fix hconj

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
