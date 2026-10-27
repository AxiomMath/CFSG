module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldTransfer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalEvenUnitaryComponents
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryDescent
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGraphOrth

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.LocalAnalysis.ComponentInitial FourGroupEvenCanonical UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer

variable {f n : ℕ} {K : Type} [Field K]

theorem fixedSubgroup_primeFormFieldHom_equiv (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C ∧
      Nonempty (fixedSubgroup (primeFormFieldHom h hC σ) ≃*
        matrixIsometryGroup (Cl : Matrix (Fin n) (Fin n) h.fixedField)) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨Cl, hCl⟩ : ∃ Cl : GL (Fin n) h.fixedField,
      (Cl : Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
    rcases hcase with h1 | ⟨r, hr, hJ⟩
    · exact ⟨1, by rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), h1]⟩
    · refine ⟨blockSwapGL (K := h.fixedField) (r := r) (by omega), ?_⟩
      rw [coe_blockSwapGL, hJ]
      ext i j
      simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
      split_ifs <;> simp
  obtain ⟨hcent, -, hinjU, hNinn, hNC, -, -⟩ :=
    even_unitary_canonical_field_centralizer_transfer h hn hq hC hcase Cl hCl σ hσ
  have hcj := UnbalancingLocal.EvenUnitaryComponents.conj_injective_primeFormP h hC hn
  have heq : inner (primeFormP h (C : Matrix (Fin n) (Fin n) K)) ⊓
      centralizer {primeFormFieldHom h hC σ} =
        ((primeFormConjHom h (C : Matrix (Fin n) (Fin n) K)).comp
          (fixedIsometryHom h hCl)).range := by
    refine le_antisymm ?_ (le_inf hNinn hNC)
    rintro x ⟨hxI, hxC⟩
    obtain ⟨g, φ, rfl⟩ := (hcent x).mp hxC
    have h1 := primeFormFieldFactor_psi h hC hn hq ⟨fixedIsometryHom h hCl g, φ⟩
    obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ _).mp hxI
    have h2 := primeFormFieldFactor_apply h hC hn hq ⟨s, s.2.1⟩ 1
    rw [map_one, mul_one, ← hs, h1] at h2
    change φ = 1 at h2
    subst h2
    refine ⟨g, ?_⟩
    rw [primeFormPsi_apply, map_one, mul_one]
    rfl
  exact ⟨Cl, hCl, ⟨(CatLeafProof.fixedInnerEquiv hcj _).trans ((MulEquiv.subgroupCongr heq).trans
    (MonoidHom.ofInjective hinjU).symm)⟩⟩

theorem primeFormFieldHom_fixed_cases (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {C : GL (Fin n) K} (hC : IsPrimeFormGram C)
    (hcase : (C : Matrix (Fin n) (Fin n) K) = 1 ∨
      ∃ r, n = 2 * r ∧ (C : Matrix (Fin n) (Fin n) K) = blockSwapJ n r)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = h.bar x) :
    (∀ r, n = 2 * r → 2 ^ (f * r ^ 2) ∣ Nat.card (fixedSubgroup (primeFormFieldHom h hC σ))) ∧
      (∀ r, n = 2 * r + 1 →
        Nonempty (fixedSubgroup (primeFormFieldHom h hC σ) ≃* StatedSp r h.fixedField)) := by
  have : CharP K 2 := h.charP
  have : Finite K := h.finite
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨Cl, hCl, ⟨Φ⟩⟩ := fixedSubgroup_primeFormFieldHom_equiv h hn hq hC hcase σ hσ
  have hk : Nat.card h.fixedField = 2 ^ f := h.card_fixedField
  rcases canonical_case_of_map h hCl hcase with h1 | ⟨r, hr, hJ⟩
  · have hC1 : (Cl : Matrix (Fin n) (Fin n) h.fixedField) =
        ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField) := by
      rw [h1, Units.val_one]
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · rw [Nat.card_congr Φ.toEquiv, h1]
      have := LinearPilot.pow_dvd_card_matrixIsometryGroup_one (F := h.fixedField) hr
        (by omega)
      rwa [hk, ← pow_mul] at this
    · obtain ⟨e₂⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp _
        (OutcomeLocal.dotForm_restrict_isAlt (k := h.fixedField) (n := n))
        (OutcomeLocal.dotForm_restrict_nondegenerate hr) (OutcomeLocal.finrank_dotForm_ker hr)
      exact ⟨Φ.trans (((MulEquiv.subgroupCongr
        (congrArg matrixIsometryGroup hC1)).trans (OutcomeLocal.oneRestrictEquiv hr)).trans e₂)⟩
  · have eSp : fixedSubgroup (primeFormFieldHom h hC σ) ≃* StatedSp r h.fixedField :=
      Φ.trans ((MulEquiv.subgroupCongr (congrArg matrixIsometryGroup hJ)).trans
        (OutcomeLocal.blockSwapIsometryEquivStatedSp (by omega)))
    refine ⟨fun r' hr' => ?_, fun r' hr' => by omega⟩
    have hrr : r' = r := by omega
    subst hrr
    rw [Nat.card_congr eSp.toEquiv]
    have := LinearPilot.pow_dvd_card_statedSp (F := h.fixedField) r'
    rwa [hk, ← pow_mul] at this

theorem unitary_outer_fixed (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) (α : MulAut (unitaryPSU h n)) (hα : orderOf α = 2)
    (hαo : α ∉ (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range) :
    (∀ r, n = 2 * r → 2 ^ (f * r ^ 2) ∣ Nat.card (fixedSubgroup α)) ∧
      (∀ r, n = 2 * r + 1 → Nonempty (fixedSubgroup α ≃* StatedSp r h.fixedField)) := by
  have : Finite K := h.finite
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun h3 => hnq (by rw [h3.1, h3.2])
  set ψ : unitaryPSU h n ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
    (OutcomeLocal.primeFormOneEquiv h n).symm with hψ
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  have hβo : MulAut.congr ψ α ∉
      inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
    rw [FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  obtain ⟨hcases, -, -, hDinner⟩ := even_unitary_involution_matrix_lifts h hC hn hq _ hβ
  rcases hcases with hid | hbar
  · exfalso
    apply hβo
    refine hDinner _ ?_ hβ
    rw [← ker_primeFormFieldFactor h hC hn hq, MonoidHom.mem_ker]
    exact hid
  obtain ⟨-, -, C₀, hC₀, hcase₀, -, -, -, -, ⟨θ, -, hθβ⟩, -⟩ :=
    even_unitary_antiunitary_involution_descent h hC hn hq _ hβ hbar
  have hc : MulAut.congr θ (primeFormFieldHom h hC₀ (primeFormFieldFactor h hC hn hq
      (MulAut.congr ψ α))) = MulAut.congr ψ α := MulEquiv.ext fun x => (hθβ x).symm
  have eα : fixedSubgroup α ≃* fixedSubgroup (primeFormFieldHom h hC₀
      (primeFormFieldFactor h hC hn hq (MulAut.congr ψ α))) :=
    (fixedSubgroupCongrEquiv ψ α).trans
      ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
        (fixedSubgroupCongrEquiv θ _).symm)
  obtain ⟨hev, hodd⟩ := primeFormFieldHom_fixed_cases h hn hq hC₀ hcase₀ _ hbar
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · rw [Nat.card_congr eα.toEquiv]
    exact hev r hr
  · obtain ⟨e₂⟩ := hodd r hr
    exact ⟨eα.trans e₂⟩

end CFSG.SeitzReduction.UnitaryPilot
