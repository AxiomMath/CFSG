module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaPi
public import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.LocalAnalysis.UniquenessCase.UC6K332OmegaList
import CFSG.LocalAnalysis.UniquenessCase.UC6K332WreathFrame
import CFSG.LocalAnalysis.UniquenessCase.UC6K332FamSp6
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLiePOmegaFrameData
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open CFSG.Blueprint CFSG.GroupTheory.WeirSylow Module QuadraticMap
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
open CFSG.LieType.Universal.Spin (quadOdd quadMinus coe_quadOdd coe_quadMinus)

theorem omegaFrameData_aniso_even_of_lt {K : Type} [Field K] [Fintype K] {p : ℕ}
    [Fact p.Prime] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hpK : ¬ p ∣ Fintype.card K) {f : ℕ} (hf : weirE p K = 2 * f)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) {n : ℕ}
    (hdim : finrank K V = 2 * n) {r : ℕ} (hrn : f * r < n) :
    OmegaFrameData Q p (weirA p K) r (Fintype.card K : ℤ) := by
  obtain ⟨S₀, ρ, J₀, φ₀, hS₀, hdim₀, hρ, hJ, hφ⟩ := exists_aniso_block (K := K) (p := p) hpK hf
  obtain ⟨QS, hSF, hQS⟩ := isQuadSpace_pi (fun _ : Fin r => S₀) (fun _ => hS₀)
  have hSdim : finrank K (FormSpace.pi fun _ : Fin r => S₀).V = 2 * (f * r) := by
    rw [FormSpace.finrank_pi]
    simp only [hdim₀, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    ring
  obtain ⟨ψ, hψ, hψD⟩ := exists_orthogonal_embedding_dickson
    (FormSpace.pi fun _ : Fin r => S₀) hSF hQS hSdim (MonoidHom.id _) Function.injective_id hQ hT
    hdim hrn.le (fun h => absurd h hrn.ne)
  exact omegaFrameData_of_embedding S₀ hS₀ (d := f) hdim₀ ρ hρ J₀ φ₀ hJ hφ ψ hψ
    fun h2 g hev => hψD h2 g hev

theorem weirA_mul_add_padicValNat_three {K : Type} [Fintype K] [Fact (Nat.Prime 3)]
    (he : weirE 3 K = 1 ∨ weirE 3 K = 2) :
    weirA 3 K * ((if Even (weirE 3 K) then 2 * 3 else 3) / weirE 3 K) +
        padicValNat 3 ((if Even (weirE 3 K) then 2 * 3 else 3) / weirE 3 K).factorial =
      3 * weirA 3 K + 1 := by
  have hr : (if Even (weirE 3 K) then 2 * 3 else 3) / weirE 3 K = 3 := by
    rcases he with h | h <;> rw [h] <;> decide
  rw [hr, ← Nat.factorization_def _ Nat.prime_three, Wreath.factorization_factorial_three]
  ring

theorem listRow_statedProj_omegaOdd_three {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (hK3 : ¬ 3 ∣ Nat.card K) : ListRow (StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hpK : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hc2 : ringChar K ≠ 2 := fun h => h2 (by
    have h0 := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at h0
    exact_mod_cast h0)
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadOdd (K := K) (n := 3) h2 le_rfl
  have hdim : finrank K (Fin 3 ⊕ Fin 3 ⊕ Unit → K) = 2 * 3 + 1 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  have he : weirE 3 K = 1 ∨ weirE 3 K = 2 := orderOf_natCast_mod_three hpK
  have hfr : OmegaFrameData (quadOdd 3 K) 3 (weirA 3 K) 3 (Fintype.card K : ℤ) := by
    rcases he with h | h
    · exact omegaFrameData_split_odd hpK hc2 hQ hdim (r := 3) (by omega)
    · exact omegaFrameData_aniso_odd hpK (f := 1) (by omega) hc2 hQ hdim (r := 3) le_rfl
  obtain ⟨B, -, -⟩ := hfr
  refine listRow_projOmega_of_blockFrame (coe_quadOdd 3 K) hQ hT (one_le_weirA hpK) B ?_
  rw [odd_dim_params (by decide) hpK hc2 hdim hQ, weirA_mul_add_padicValNat_three he]

theorem listRow_statedProj_omegaMinus_four {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK3 : ¬ 3 ∣ Nat.card K) :
    ListRow (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have hpK : ¬ 3 ∣ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨hQ, hT⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (K := K) (n := 4) le_rfl hirr
  have hdim : finrank K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) = 2 * 4 :=
    finrank_quadMinus_space (by omega)
  have hnp : ¬ IsPlusType (quadMinus 4 K b c) := not_isPlusType_quadMinus (by omega) hirr
  have he : weirE 3 K = 1 ∨ weirE 3 K = 2 := orderOf_natCast_mod_three hpK
  obtain ⟨k, hk3, hk4, hcard, hts, hta⟩ :=
    even_dim_params (by decide) hpK le_rfl hdim hQ (ε := -1) (Or.inr ⟨rfl, hnp⟩)
  obtain rfl : k = 3 := by
    by_contra hne
    obtain rfl : k = 4 := by omega
    rcases he with h | h
    · exact hnp (hts (by simp [h]) (by simp [h]))
    · exact hnp ((hta 1 (by simp [h]) (by norm_num)).2 ⟨2, rfl⟩)
  have hfr : OmegaFrameData (quadMinus 4 K b c) 3 (weirA 3 K) 3 (Fintype.card K : ℤ) := by
    rcases he with h | h
    · exact omegaFrameData_split_even hpK hQ hT hdim (r := 3) (by omega)
        fun h' => absurd h' (by omega)
    · exact omegaFrameData_aniso_even_of_lt hpK (f := 1) (by omega) hQ hT hdim (r := 3)
        (by norm_num)
  obtain ⟨B, -, -⟩ := hfr
  refine listRow_projOmega_of_blockFrame (coe_quadMinus 4 K b c) hQ hT (one_le_weirA hpK) B ?_
  rw [hcard, weirA_mul_add_padicValNat_three he]

theorem listRow_pomegaOdd7 (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .POmegaOdd 3 p f) (hp3 : p ≠ 3) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hK3 : ¬ 3 ∣ Nat.card K := hK ▸ (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (((Nat.coprime_primes Nat.prime_three hadm.1).2 hp3.symm).pow_right f)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_omegaOdd_three
      (CFSG.ClassicalInvolution.two_ne_zero_of_card_eq_prime_pow hadm.1 hadm.2.2.2 hK) hK3)

theorem listRow_pomegaMinus8 (S : Type) [Group S] [Finite S] (p f : ℕ)
    (h : LieModel S .POmegaMinus 4 p f) (hp3 : p ≠ 3) : ListRow S := by
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hK3 : ¬ 3 ∣ Nat.card K := hK ▸ (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (((Nat.coprime_primes Nat.prime_three hadm.1).2 hp3.symm).pow_right f)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.ListRow.of_mulEquiv e.symm
    (listRow_statedProj_omegaMinus_four hirr hK3)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
