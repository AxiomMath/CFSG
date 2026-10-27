module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddFieldFixBase
import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55UDesc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.OddAutSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.Classical
open CFSG.Open CFSG.EvenSmallLie.CatalogOrders
open CFSG.LieType.Chevalley (fixSubfield)

private theorem card_primeFormP_eq_lieOrd {K : Type} [Field K] {r f n : ℕ}
    (h : UnitaryFieldData r f K) (hr2 : r ≠ 2) (hn : 3 ≤ n) :
    Nat.card (primeFormP h (idGram K n)) = lieOrd .PSU n (r ^ f) := by
  have := h.finite
  have hr3 : 3 ≤ r := by have := h.prime.two_le; omega
  have hr3f : 3 ≤ r ^ f := hr3.trans (Nat.le_self_pow (by have := h.one_le; omega) r)
  have hne : (n, r ^ f) ≠ (3, 2) := by
    intro he
    have h2 : r ^ f = 2 := congrArg Prod.snd he
    omega
  have hK : Nat.card K = (r ^ f) ^ 2 := by
    rw [h.card, mul_comm 2 f, pow_mul]
  let e : primeFormP h (idGram K n) ≃* StatedProj (StatedSU n (r ^ f) K) :=
    (Classical.choice (nonempty_primeFormP_mulEquiv h isPrimeFormGram_one)).trans
      (unitaryPSUEquiv h (by omega))
  have hmodel : StatedClassicalModel (primeFormP h (idGram K n)) .PSU n r f :=
    ⟨⟨h.prime, h.one_le, hn, hne⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  exact card_eq_lieOrd_of_classical hmodel

theorem fixesSylowOutside_primeFormP {K : Type} [Field K] {r f n : ℕ}
    (h : UnitaryFieldData r f K) (hr2 : r ≠ 2) (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    FixesSylowOutside (primeFormP h (idGram K n)) (primeFormD h (idGram K n)) p := by
  intro α hα hout
  have hα1 : α ≠ 1 := fun h1 => hout (h1 ▸ (primeFormD h (idGram K n)).one_mem)
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p := orderOf_eq_prime hα hα1
  have := h.finite
  have hr3 : 3 ≤ r := by have := h.prime.two_le; omega
  have hrf3 : 3 ≤ r ^ f := hr3.trans (Nat.le_self_pow (by have := h.one_le; omega) r)
  have hne : ¬(n = 3 ∧ r ^ f = 2) := by omega
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  let σ := primeFormFieldFactor h hC hn hne α
  have hσp : σ ^ p = 1 := by
    change primeFormFieldFactor h hC hn hne α ^ p = 1
    rw [← map_pow, hα, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply hout
    rw [← ker_primeFormFieldFactor h hC hn hne]
    exact h1
  have hσ : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hrf, -, -, -, -, M, hM⟩ :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.unitary_prime_descent_char h hn hne hp (by omega)
      α hαord σ rfl hσ
  let δ := primeFormConjHom h (idGram K n) M
  have hδ : α = δ * primeFormFieldHom h hC σ * δ⁻¹ := by
    rw [← hM]
    change α = δ * (δ⁻¹ * α * δ) * δ⁻¹
    group
  let k := fixSubfield σ
  let h0 : UnitaryFieldData r (f / p) k := fixSubfield_unitaryFieldData h hp (by omega) hσ
  have hbar : ∀ c : k, (h0.bar c : K) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp (by omega) hσ
  let ι0 := subfieldPSU h h0 hbar n
  let ι := δ.toMonoidHom.comp ι0
  have hι : Function.Injective ι := δ.injective.comp
    (subfieldPSU_injective h h0 hbar n (by omega))
  have hfix : ∀ y, α (ι y) = ι y := by
    intro y
    change α (δ (ι0 y)) = δ (ι0 y)
    simp only [hδ, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    apply congrArg δ
    exact (range_subfieldPSU_le h n h0 hbar) ⟨y, rfl⟩
  have hcardX : Nat.card (primeFormP h (idGram K n)) = lieOrd .PSU n (r ^ f) :=
    card_primeFormP_eq_lieOrd h hr2 hn
  have hcardH : Nat.card (primeFormP h0 (idGram k n)) = lieOrd .PSU n (r ^ (f / p)) :=
    card_primeFormP_eq_lieOrd h0 hr2 hn
  have hpow : r ^ f = (r ^ (f / p)) ^ p := by
    conv_lhs => rw [← Nat.div_mul_cancel hrf]
    rw [pow_mul]
  have hq : Odd (r ^ (f / p)) := (h.prime.odd_of_ne_two hr2).pow
  have hk : Odd p := hp.odd_of_ne_two (by omega)
  have hfac : (Nat.card (primeFormP h0 (idGram k n))).factorization 2 =
      (Nat.card (primeFormP h (idGram K n))).factorization 2 := by
    rw [hcardH, hcardX, hpow]
    exact (factorization_two_lieOrd_pow .PSU n hq hk).symm
  exact exists_isSylowOf_fixed_of_injective ι hι α hfix hfac

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
