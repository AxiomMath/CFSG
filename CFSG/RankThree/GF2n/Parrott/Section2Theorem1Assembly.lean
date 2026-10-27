module

public import CFSG.RankThree.GF2n.Parrott.Section1
public import CFSG.RankThree.GF2n.Parrott.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem eq_centralizer_sup_pPrimeCore_of_no_fusion_of_orderOf (hz2 : orderOf z = 2)
    (hnofusion : ∀ ⦃y : G⦄, orderOf y = 2 → y ∈ H z →
      (∃ g : G, g * z * g⁻¹ = y) → y = z) :
    H z ⊔ pPrimeCore 2 G = ⊤ := by
  have hiso : ∀ g : G, (g * z * g⁻¹) * z = z * (g * z * g⁻¹) → g * z * g⁻¹ = z := by
    intro g hcomm
    apply hnofusion ?_ ?_ ⟨g, rfl⟩
    · have hsemi : SemiconjBy g z (g * z * g⁻¹) := by
        unfold SemiconjBy
        group
      rw [← SemiconjBy.orderOf_eq g hsemi]
      exact hz2
    · rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
  exact prop2_eq_centralizer_mul_oddCore hz2 hiso

omit [Finite G] in
theorem no_fusion_of_involution_classes
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z →
      ∀ g : G, g * z * g⁻¹ ≠ j)
    (hOut : ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    ∀ ⦃y : G⦄, orderOf y = 2 → y ∈ H z → (∃ g : G, g * z * g⁻¹ = y) → y = z := by
  intro y hy2 hyH ⟨g, hg⟩
  by_contra hyz
  by_cases hyJ : y ∈ J z
  · exact hJ y hyJ hy2 hyz g hg
  · exact hOut y hyH hyJ hy2 g hg

theorem eq_centralizer_sup_pPrimeCore_of_classes_of_orderOf (hz2 : orderOf z = 2)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z →
      ∀ g : G, g * z * g⁻¹ ≠ j)
    (hOut : ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    H z ⊔ pPrimeCore 2 G = ⊤ :=
  eq_centralizer_sup_pPrimeCore_of_no_fusion_of_orderOf hz2
    (no_fusion_of_involution_classes hJ hOut)

theorem eq_centralizer_sup_pPrimeCore_of_classes (h : Tim79a.ParrottHyp z)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z →
      ∀ g : G, g * z * g⁻¹ ≠ j)
    (hOut : ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x) :
    H z ⊔ pPrimeCore 2 G = ⊤ :=
  eq_centralizer_sup_pPrimeCore_of_classes_of_orderOf h.1 hJ hOut

end CFSG.RankThree.GF2n.Parrott
