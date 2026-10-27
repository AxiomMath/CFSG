
module

public import CFSG.Quasithin.Recognition.L34AmalgamGenBase

public import CFSG.Quasithin.Recognition.L34AmalgamData
public meta import CFSG.Quasithin.Recognition.L34AmalgamData
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import CFSG.Sporadic.Schreier.M22Data
public meta import CFSG.Sporadic.Schreier.M22Data
public import CFSG.Quasithin.Recognition.L34AmalgamGenInputs
public import Certificates.Certificate7037
public import CFSG.Quasithin.Recognition.L34AmalgamDataInputs
public import CFSG.Quasithin.Recognition.M22WittData
public import CFSG.Certificates.CosetTablePresented
public import CFSG.Quasithin.Recognition.M22UniqueDataInputs
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Quasithin.Recognition.M22UniqueSystem
public import Certificates.Data.CFSGNative.Mathieu.M22

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem bWords_letters : ∀ s ∈ bWords, ∀ x ∈ word s, x.1.val < 3 :=
  Certificates.certificate7037.1

theorem count_B :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
    ¬ ∃ T ∈ bTabs, ∀ x : Fin 22, σ x = T.getD x.val 0) = 0 :=
  Certificates.certificate7037.2

theorem closure_c_le_B :
    Subgroup.closure (gen '' {0, 1, 2}) ≤ m22TwoStab ⊓ m22PtHexStab := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have h4 : j ≠ 4 := by rintro rfl; simp at hj
  have h3 : j ≠ 3 := by rintro rfl; simp at hj
  exact ⟨gen_mem_two j h4, gen_mem_ptHex j h3⟩

theorem mem_closure_of_mem_B {σ : M22}
    (h1 : σ ∈ m22TwoStab)
    (h2 : σ ∈ m22PtHexStab) :
    σ ∈ Subgroup.closure (gen '' {0, 1, 2}) := by
  obtain ⟨h0, h11⟩ := mem_m22TwoStab_iff.mp h1
  have hh := (M22Witt.mem_m22PtHexStab_iff.mp h2).2
  have hc := not_of_count_eq_zero _ count_B σ
  simp only [not_and, not_not] at hc
  obtain ⟨T, hT, hσT⟩ := hc h0 h11 hh
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  have hσ : σ = evalW gen (word s) := by
    apply Subtype.ext
    ext x
    rw [hσT x, tab_getD]
  rw [hσ]
  refine evalW_mem_closure gen _ _ fun x hx => ?_
  have := bWords_letters s hs x hx
  have hx3 : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 := by
    rcases x with ⟨⟨v, hv⟩, b⟩
    simp only at this ⊢
    interval_cases v <;> simp
  rcases hx3 with h | h | h <;> simp [h]

theorem closure_gen_P1 :
    Subgroup.closure (gen '' {0, 1, 2, 3}) = m22TwoStab := by
  have hle : Subgroup.closure (gen '' {0, 1, 2, 3}) ≤ m22TwoStab := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact gen_mem_two j (by rintro rfl; simp at hj)
  have hB : m22TwoStab ⊓ m22PtHexStab ≤ Subgroup.closure (gen '' {0, 1, 2, 3}) := by
    intro σ hσ
    exact Subgroup.closure_mono (Set.image_mono (by intro j hj; simp at hj ⊢; omega))
      (mem_closure_of_mem_B hσ.1 hσ.2)
  refine eq_of_card_eq_five_mul hB hle ?_ (x := bT1)
    (Subgroup.subset_closure ⟨3, by simp, gen_three⟩) (fun h => bT1_not_mem h.2)
  rw [card_m22TwoStab, card_B]

theorem closure_gen_P2 :
    Subgroup.closure (gen '' {0, 1, 2, 4}) = m22PtHexStab := by
  have hle : Subgroup.closure (gen '' {0, 1, 2, 4}) ≤ m22PtHexStab := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact gen_mem_ptHex j (by rintro rfl; simp at hj)
  have hB : m22TwoStab ⊓ m22PtHexStab ≤ Subgroup.closure (gen '' {0, 1, 2, 4}) := by
    intro σ hσ
    exact Subgroup.closure_mono (Set.image_mono (by intro j hj; simp at hj ⊢; omega))
      (mem_closure_of_mem_B hσ.1 hσ.2)
  refine eq_of_card_eq_five_mul hB hle ?_ (x := bT2)
    (Subgroup.subset_closure ⟨4, by simp, gen_four⟩) (fun h => bT2_not_mem h.1)
  rw [M22Witt.card_m22PtHexStab, card_B]

theorem closure_range_gen :
    Subgroup.closure (Set.range gen) = stabilizer M22 (0 : Fin 22) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = 4
    · rw [hj, gen_four]
      exact (Subgroup.mem_inf.mp bT2_mem_ptHex).1
    · exact (Subgroup.mem_inf.mp (gen_mem_two j hj)).1
  · rw [← sup_P1_P2, ← closure_gen_P1, ← closure_gen_P2]
    exact sup_le (Subgroup.closure_mono (Set.image_subset_range _ _))
      (Subgroup.closure_mono (Set.image_subset_range _ _))

end CFSG.Quasithin.L34Amalgam
