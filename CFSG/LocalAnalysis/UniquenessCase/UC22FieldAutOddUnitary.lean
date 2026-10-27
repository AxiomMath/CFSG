module

import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
import CFSG.RankThree.PartOne.KC.UnitaryNoninnerPlaneGeneral
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.Classical
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LieType.Chevalley (fixSubfield)

theorem fieldAutOdd_primeForm_subfield {p f n r : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hr : r.Prime) (hr2 : r ≠ 2) (hcop : ¬ r ∣ Nat.gcd n (p ^ f + 1))
    (θ : MulAut (primeFormP h (idGram K n))) (hθ : orderOf θ = r)
    (hout : θ ∉ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range) :
    r ∣ f ∧ ∃ Y : Subgroup (primeFormP h (idGram K n)),
      Y ≤ signalizerFixedSubgroup θ ∧ LieModel Y .PSU n p (f / r) := by
  classical
  have := h.finite
  have : Fact r.Prime := ⟨hr⟩
  have hp3 : 3 ≤ p := by have := h.prime.two_le; omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow (by have := h.one_le; omega) p)
  have hne : ¬ (n = 3 ∧ p ^ f = 2) := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  let σ := primeFormFieldFactor h hC hn hne θ
  have hθr : θ ^ r = 1 := hθ ▸ pow_orderOf_eq_one θ
  have hσr : σ ^ r = 1 := by
    change primeFormFieldFactor h hC hn hne θ ^ r = 1
    rw [← map_pow, hθr, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hD : θ ∈ primeFormD h (idGram K n) := by
      rw [← ker_primeFormFieldFactor h hC hn hne]
      exact h1
    exact hout (pElement_mem_inner_of_not_dvd_gcd h hn hne hr hcop hD hθr)
  have hσ : orderOf σ = r := orderOf_eq_prime hσr hσ1
  obtain ⟨hrf, -, -, -, -, M, hM⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn hne hr hr2
      θ hθ σ rfl hσ
  let δ := primeFormConjHom h (idGram K n) M
  have hδ : θ = δ * primeFormFieldHom h hC σ * δ⁻¹ := by
    rw [← hM]
    change θ = δ * (δ⁻¹ * θ * δ) * δ⁻¹
    group
  let k := fixSubfield σ
  let h0 : UnitaryFieldData p (f / r) k := fixSubfield_unitaryFieldData h hr hr2 hσ
  have hbar : ∀ c : k, (h0.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hr hr2 hσ
  let ι0 := subfieldPSU h h0 hbar n
  let ι := δ.toMonoidHom.comp ι0
  have hι : Function.Injective ι := δ.injective.comp
    (subfieldPSU_injective h h0 hbar n (by omega))
  have hfix : ∀ y, θ (ι y) = ι y := by
    intro y
    change θ (δ (ι0 y)) = δ (ι0 y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    apply congrArg δ
    exact (range_subfieldPSU_le h n h0 hbar) ⟨y, rfl⟩
  have hcard : Nat.card k = (p ^ (f / r)) ^ 2 := by
    rw [h0.card, mul_comm 2 (f / r), pow_mul]
  have hq03 : 3 ≤ p ^ (f / r) := hp3.trans
    (Nat.le_self_pow (by have := h0.one_le; omega) p)
  let e0 : primeFormP h0 (idGram k n) ≃* StatedProj (StatedSU n (p ^ (f / r)) k) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h0 isPrimeFormGram_one)).trans
      (unitaryPSUEquiv h0 (by omega))
  have hmodel : LieModel (primeFormP h0 (idGram k n)) .PSU n p (f / r) := by
    refine Or.inl ⟨by decide, ⟨h0.prime, h0.one_le, hn, ?_⟩, k,
      inferInstance, inferInstance, hcard, ⟨e0⟩⟩
    intro he
    have := congrArg Prod.snd he
    omega
  refine ⟨hrf, ι.range, ?_, hmodel.of_mulEquiv (MonoidHom.ofInjective hι)⟩
  rintro _ ⟨y, rfl⟩
  exact hfix y

theorem fieldAutOdd_psu_subfield {X : Type} [Group X] [Finite X] {n p f r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hX : LieModel X .PSU n p f)
    (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrg : ¬ r ∣ (CFSG.Blueprint.Multiplier.genericOrders .PSU n p f).1)
    (θ : MulAut X) (hθ : orderOf θ = r) (hout : θ ∉ (MulAut.conj : X →* MulAut X).range) :
    r ∣ f ∧ ∃ Y : Subgroup X, Y ≤ signalizerFixedSubgroup θ ∧
      LieModel Y .PSU n p (f / r) := by
  classical
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨eX⟩⟩ := hX.statedClassicalModel (by decide)
  let h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  let eP : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (p ^ f) K) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)).trans
      (unitaryPSUEquiv h (by omega))
  let e := eX.trans eP.symm
  have hθ' : orderOf (MulAut.congr e θ) = r :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective θ).trans hθ
  have hout' : MulAut.congr e θ ∉
      (MulAut.conj : primeFormP h (idGram K n) →* MulAut (primeFormP h (idGram K n))).range := by
    rintro ⟨x, hx⟩
    apply hout
    refine ⟨e.symm x, ?_⟩
    ext g
    have hh := congrArg (fun α : MulAut (primeFormP h (idGram K n)) => e.symm (α (e g))) hx
    simpa [MulAut.congr_apply, MulAut.conj_apply] using hh
  obtain ⟨hrf, Y, hY, hmodel⟩ := fieldAutOdd_primeForm_subfield h hp2 hn hr (by omega) hrg
    (MulAut.congr e θ) hθ' hout'
  refine ⟨hrf, Y.map e.symm.toMonoidHom, ?_,
    hmodel.of_mulEquiv (Y.equivMapOfInjective e.symm.toMonoidHom e.symm.injective)⟩
  rintro _ ⟨y, hy, rfl⟩
  change θ (e.symm y) = e.symm y
  apply e.injective
  have hh : (MulAut.congr e θ) y = y := hY hy
  simpa [MulAut.congr_apply] using hh

end CFSG.LocalAnalysis.UniquenessCase.UC22
