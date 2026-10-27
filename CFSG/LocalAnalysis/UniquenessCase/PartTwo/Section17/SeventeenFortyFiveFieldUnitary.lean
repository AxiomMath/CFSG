module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFieldTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveFieldUnitaryCore
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)

section Unitary

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LieType.Chevalley (fixSubfield)

theorem false_of_fieldAut_five_psu {L : Type} [Group L] [Finite L]
    {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) (hL : LieModel L .PSU n p f)
    (hq5 : p ^ f % 5 = 2 ∨ p ^ f % 5 = 3)
    (θ : MulAut L) (hθ : orderOf θ = 5) (hout : θ ∉ (MulAut.conj : L →* MulAut L).range)
    (M : Subgroup L) (hM : M ≠ ⊤) (hfix : ∀ y : L, θ y = y → y ∈ M)
    (hcent : ∀ x ∈ M, orderOf x = 5 → ∀ g : L, Commute g x → g ∈ M) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨⟨-, hf, -, -⟩, K, _, _, hK, ⟨eX⟩⟩ := hL.statedClassicalModel (by decide)
  let h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let eP : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (p ^ f) K) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)).trans
      (unitaryPSUEquiv h (by omega))
  let e := eX.trans eP.symm
  have hθ' : orderOf (MulAut.congr e θ) = 5 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have hh := congrArg (fun α : MulAut (primeFormP h (idGram K n)) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using hh
  have hn3 : 3 ≤ n := by omega
  have hne : ¬ (n = 3 ∧ p ^ f = 2) := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hg5 : ¬ 5 ∣ Nat.gcd n (p ^ f + 1) := fun h5 => by
    have h5' := h5.trans (Nat.gcd_dvd_right _ _)
    generalize p ^ f = q at hq5 h5'
    omega
  have hθr : MulAut.congr e θ ^ 5 = 1 := hθ' ▸ pow_orderOf_eq_one _
  let σ := primeFormFieldFactor h hC hn3 hne (MulAut.congr e θ)
  have hσr : σ ^ 5 = 1 := by
    change primeFormFieldFactor h hC hn3 hne (MulAut.congr e θ) ^ 5 = 1
    rw [← map_pow, hθr, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hD : MulAut.congr e θ ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h hC hn3 hne]
      exact h1
    exact hout' (pElement_mem_inner_of_not_dvd_gcd h hn3 hne (by norm_num) hg5 hD hθr)
  have hσ : orderOf σ = 5 := orderOf_eq_prime hσr hσ1
  obtain ⟨h5f, -, -, -, -, Mu, hMu⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn3 hne
      (by norm_num : Nat.Prime 5) (by norm_num) (MulAut.congr e θ) hθ' σ rfl hσ
  let δ := primeFormConjHom h (idGram K n) Mu
  have hδ : MulAut.congr e θ = δ * primeFormFieldHom h hC σ * δ⁻¹ := by
    rw [← hMu]
    change MulAut.congr e θ = δ * (δ⁻¹ * MulAut.congr e θ * δ) * δ⁻¹
    group
  have h0 := fixSubfield_unitaryFieldData h (by norm_num : Nat.Prime 5) (by norm_num) hσ
  have hbar : ∀ c : fixSubfield σ, (h0.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h (by norm_num) (by norm_num) hσ
  let ψ : L ≃* primeFormP h (idGram K n) := e.trans (MulEquiv.symm δ)
  have hk : (subfieldPSU h h0 hbar n).range ≤ M.map ψ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    rw [Subgroup.mem_map_equiv]
    apply hfix
    apply e.injective
    have hfy : primeFormFieldHom h hC σ (subfieldPSU h h0 hbar n y) =
        subfieldPSU h h0 hbar n y :=
      (range_subfieldPSU_le h n h0 hbar) ⟨y, rfl⟩
    have h1 := congrArg (fun α : MulAut (primeFormP h (idGram K n)) =>
      α (δ (subfieldPSU h h0 hbar n y))) hδ
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hfy] at h1
    simpa [ψ, MulAut.congr_apply] using h1
  have hM' : M.map ψ.toMonoidHom ≠ ⊤ := by
    intro hT
    apply hM
    rw [eq_top_iff]
    intro y _
    have hy : ψ y ∈ M.map ψ.toMonoidHom := hT ▸ Subgroup.mem_top _
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hy
  have hf5 : f = 5 * (f / 5) := (Nat.mul_div_cancel' h5f).symm
  exact hM' (primeFormP_eq_top_of_subfield_le h hp2 _ h0 hbar hf5 hn hq5 _ hk
    (forall_commute_mem_map ψ hcent))

end Unitary

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
