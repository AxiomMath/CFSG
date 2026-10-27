module

public import CFSG.LocalAnalysis.SteinbergBTEvenSymplecticFixedNoSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBT

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open FourGroupEvenCanonical UnitaryHigher CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification CFSG.ComponentClassification.OutcomeLocal
open CFSG.ClassicalGroups.UnitaryFlag

theorem unitary_fixed_false {A : Type} [Group A] [Finite A] {W : Subgroup A} [W.Normal] {a : A}
    {L : Subgroup A} {e n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 e K) (hn : 4 ≤ n)
    (ha : orderOf a = 2) (hLCW : CFSG.Assembly.IsComponentOf L (W ⊓ centralizer {a}))
    (φ : W ≃* unitaryPSU h n) {ρ : A →* MulAut (unitaryPSU h n)} (hinj : Function.Injective ρ)
    (hρW : ∀ w : W, ρ w = MulAut.conj (φ w)) (h4 : ∀ x : L, orderOf x ≠ 4) : False := by
  classical
  have := fixedField_charP h
  have := fixedField_finite h
  have hn3 : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ e = 2) := fun h' => by omega
  obtain ⟨H₀, C, hC, hcase, -, θ, -, ρC, -, hρCinj, hρCW, σ, hσ, hρCa, -⟩ :=
    socle_descent h hn3 hq ha hLCW φ hinj hρW
  let eLC : L ≃* L.map ρC := L.equivMapOfInjective ρC hρCinj
  have hk : Nat.card h.fixedField = 2 ^ e := h.card_fixedField
  have hA6 : ∀ X : Subgroup (MulAut (primeFormP h (C : Matrix (Fin n) (Fin n) K))),
      L.map ρC = X → Nonempty (X ≃* alternatingGroup (Fin 6)) → False := by
    rintro X hX ⟨eA⟩
    obtain ⟨y, hy⟩ := exists_orderOf_eq_four_alternating_six
    exact h4 ((eLC.trans ((MulEquiv.subgroupCongr hX).trans eA)).symm y)
      (by rw [MulEquiv.orderOf_eq, hy])
  have hSp : ∀ {r : ℕ}, 2 ≤ r → Nonempty (L.map ρC ≃* StatedSp r h.fixedField) → False := by
    rintro r hr ⟨eX⟩
    obtain ⟨y, hy, -⟩ := SteinbergCD.exists_orderOf_eq_four_statedSp (k := h.fixedField)
      CharTwo.two_eq_zero hr
    exact h4 ((eLC.trans eX).symm y) (by rw [MulEquiv.orderOf_eq, hy])
  have : Finite (GL (Fin n) h.fixedField) := Finite.of_injective Units.val Units.val_injective
  rcases hcase with hC1 | ⟨r, hr, hCJ⟩
  ·
    have hCl : ((1 : GL (Fin n) h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField).map
        h.fixedField.subtype = C := by
      rw [hC1, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨-, -, hinjU, -, -, -, -, -, hLC⟩ :=
      socle_transfer h hn3 hq hLCW hC (Or.inl hC1) 1 hCl hσ hρCinj _ hρCW hρCa
    rcases Nat.even_or_odd n with hev | ⟨r, hr⟩
    ·
      exact (no_component_matrixIsometryGroup_one_of_even hev hn3 _)
        (SymmetricLocal.isComponent_comap_of_isComponentOf_range _ hinjU hLC).1
    ·
      have hdim := finrank_dotForm_ker (k := h.fixedField) hr
      have hBalt := dotForm_restrict_isAlt (k := h.fixedField) (n := n)
      have hBnd := dotForm_restrict_nondegenerate (k := h.fixedField) hr
      rcases symplectic_component_dichotomy hinjU hLC hk (by omega : 1 ≤ r) (by omega) _ hBalt
          hBnd hdim (oneRestrictEquiv hr) with
        ⟨-, -, -, -, hX⟩ | ⟨-, -, hXc, -, -, hX6⟩
      · exact hSp (by omega) hX
      · exact hA6 _ hXc hX6
  ·
    have hrr : r + r = n := by omega
    have hClJ := coe_blockSwapGL (K := h.fixedField) hrr
    have hCl : ((blockSwapGL (K := h.fixedField) hrr : GL (Fin n) h.fixedField) :
        Matrix (Fin n) (Fin n) h.fixedField).map h.fixedField.subtype = C := by
      rw [hClJ, hCJ]
      ext i j
      simp only [Matrix.map_apply, blockSwapJ, Matrix.of_apply]
      split_ifs <;> simp
    obtain ⟨-, -, hinjU, -, -, -, -, -, hLC⟩ :=
      socle_transfer h hn3 hq hLCW hC (Or.inr ⟨r, hr, hCJ⟩) _ hCl hσ hρCinj _ hρCW hρCa
    have hBalt : (Matrix.toBilin' ((blockSwapGL (K := h.fixedField) hrr : GL (Fin n)
        h.fixedField) : Matrix (Fin n) (Fin n) h.fixedField)).IsAlt := fun x => by
      rw [Matrix.toBilin'_apply', hClJ]
      exact dotProduct_mulVec_self_eq_zero blockSwapJ_transpose
        (fun i => blockSwapJ_apply_self (by omega) i) x
    have hBnd := CatalogueBLinearHigherB.matrixForm_nondegenerate
      (blockSwapGL (K := h.fixedField) hrr)
    have hdim : Module.finrank h.fixedField (Fin n → h.fixedField) = 2 * r := by
      rw [Module.finrank_fin_fun]
      exact hr
    rcases symplectic_component_dichotomy hinjU hLC hk (by omega : 1 ≤ r) (by omega) _ hBalt
        hBnd hdim (matrixIsometryGroupEquiv _) with
      ⟨-, -, -, -, hX⟩ | ⟨-, -, hXc, -, -, hX6⟩
    · exact hSp (by omega) hX
    · exact hA6 _ hXc hX6

end CFSG.LocalAnalysis.SteinbergBT
