module

public import CFSG.Quasithin.Recognition.M22UniqueSystem
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import Certificates.Certificate2031
public import Certificates.Certificate2035
public import Certificates.Certificate2195
public import Certificates.Certificate7042
public import Certificates.Certificate7041
public import Certificates.Certificate3029
public import CFSG.Quasithin.Recognition.UniquenessSystemCriterion
public import CFSG.Quasithin.Recognition.UniquenessSystemPairs
public import CFSG.Quasithin.Recognition.UniquenessSystemRecognition

public section

namespace CFSG.Quasithin.M22Witt

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

theorem count_ptHex :
    m22Count (fun σ => σ 0 = 0 ∧ ∀ p ∈ m22HexadL, σ p ∈ m22HexadL) = 960 :=
  Certificates.certificate7042.1

theorem count_ptHex_trans : ∀ y : Fin 22, y ∉ m22HexadL →
    0 < m22Count (fun σ => σ 0 = 0 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧ σ 3 = y) :=
  Certificates.certificate7042.2

theorem mem_m22PtHexStab_iff {g : M22} : g ∈ m22PtHexStab ↔
    (g : Equiv.Perm (Fin 22)) 0 = 0 ∧ ∀ p ∈ m22HexadL, (g : Equiv.Perm (Fin 22)) p ∈ m22HexadL := by
  rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, mem_m22HexStab_iff, presHex_iff_mapsTo,
    smul_m22_def]

theorem card_m22PtHexStab :
    Nat.card m22PtHexStab = 960 := by
  rw [← count_ptHex, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_m22PtHexStab_iff)

theorem exists_ptHex_smul_three
    {y : Fin 22} (hy : y ∉ m22HexadF) :
    ∃ g ∈ m22PtHexStab, g • (3 : Fin 22) = y := by
  have hy' : y ∉ m22HexadL := fun h => hy ((mem_m22HexadL_iff y).mp h)
  obtain ⟨g, hg0, hgh, hg3⟩ := exists_m22_of_count _ (count_ptHex_trans y hy')
  exact ⟨g, mem_m22PtHexStab_iff.mpr ⟨hg0, hgh⟩, (smul_m22_def _ _).trans hg3⟩

theorem exists_ptHex_smul_eq
    {x y : Fin 22} (hx : x ∉ m22HexadF)
    (hy : y ∉ m22HexadF) :
    ∃ g ∈ m22PtHexStab, g • x = y := by
  obtain ⟨a, ha, hax⟩ := exists_ptHex_smul_three hx
  obtain ⟨b, hb, hby⟩ := exists_ptHex_smul_three hy
  refine ⟨b * a⁻¹, m22PtHexStab.mul_mem hb (m22PtHexStab.inv_mem ha), ?_⟩
  rw [mul_smul, ← hax, inv_smul_smul, hby]

theorem eq_m22HexadF_of_invariant
    {X : Finset (Fin 22)}
    (h0 : (0 : Fin 22) ∈ X)
    (hcard : X.card = 6) (hinv : ∀ g ∈ m22PtHexStab, ∀ x ∈ X, g • x ∈ X) : X = m22HexadF := by
  have hsub : X ⊆ m22HexadF := by
    intro x hx
    by_contra hxh
    have hall : ∀ y ∉ m22HexadF, y ∈ X := by
      intro y hy
      obtain ⟨g, hg, rfl⟩ := exists_ptHex_smul_eq hxh hy
      exact hinv g hg x hx
    have hle : insert (0 : Fin 22) (Finset.univ \ m22HexadF) ⊆ X := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact h0
      · exact hall y (Finset.mem_sdiff.mp hy).2
    have hc : (insert (0 : Fin 22) (Finset.univ \ m22HexadF)).card = 17 := by decide
    have := Finset.card_le_card hle
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)

theorem m22HexadF_mem_hexads : m22HexadF ∈ hexads := hexad0_mem

theorem eq_of_three_mem {X Y : Finset (Fin 22)} (hX : X ∈ hexads)
    (hY : Y ∈ hexads)
    {a b c : Fin 22} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (haX : a ∈ X) (hbX : b ∈ X)
    (hcX : c ∈ X) (haY : a ∈ Y) (hbY : b ∈ Y) (hcY : c ∈ Y) : X = Y := by
  have hT : ({a, b, c} : Finset (Fin 22)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  obtain ⟨B, -, hu⟩ := isSteinerTriple_hexads.2.2 {a, b, c} hT
  have sub : ∀ Z : Finset (Fin 22), a ∈ Z → b ∈ Z → c ∈ Z → ({a, b, c} : Finset (Fin 22)) ⊆ Z := by
    intro Z ha hb hc x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  exact (hu X ⟨hX, sub X haX hbX hcX⟩).trans (hu Y ⟨hY, sub Y haY hbY hcY⟩).symm

theorem exists_two_mem_ne {X : Finset (Fin 22)} (hX : X ∈ hexads)
    (x : Fin 22) :
    ∃ a ∈ X, ∃ b ∈ X, a ≠ x ∧ b ≠ x ∧ a ≠ b := by
  have hc : (X.erase x).card ≥ 5 := by
    have := Finset.pred_card_le_card_erase (s := X) (a := x)
    rw [card_of_mem_hexads hX] at this
    omega
  obtain ⟨a, ha⟩ : (X.erase x).Nonempty := Finset.card_pos.mp (by omega)
  have hc' : ((X.erase x).erase a).card ≥ 4 := by
    have := Finset.pred_card_le_card_erase (s := X.erase x) (a := a)
    omega
  obtain ⟨b, hb⟩ : ((X.erase x).erase a).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hba, hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨hbx, hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨hax, ha⟩ := Finset.mem_erase.mp ha
  exact ⟨a, ha, b, hb, hax, hbx, Ne.symm hba⟩

theorem exists_stabilizer_zero_smul_eq
    {X : Finset (Fin 22)}
    (hX : X ∈ hexads)
    (h0 : (0 : Fin 22) ∈ X) : ∃ g ∈ stabilizer M22 (0 : Fin 22), g • m22HexadF = X := by
  obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := exists_two_mem_ne hX 0
  obtain ⟨g, hg0, hg1, hg2⟩ := exists_smul_eq_triple (a := (0 : Fin 22)) (b := 1) (c := 2)
    (a' := 0) (b' := a) (c' := b) (by decide) (by decide) (by decide) (Ne.symm ha0)
    (Ne.symm hb0) hab
  refine ⟨g, MulAction.mem_stabilizer_iff.mpr hg0, ?_⟩
  have hmem : ∀ p ∈ m22HexadF, g • p ∈ g • m22HexadF := fun p hp => Finset.smul_mem_smul_finset hp
  refine eq_of_three_mem (smul_mem_hexads g m22HexadF_mem_hexads) hX (Ne.symm ha0) (Ne.symm hb0)
    hab ?_ ?_ ?_ h0 ha hb
  · rw [← hg0]; exact hmem 0 (by decide)
  · rw [← hg1]; exact hmem 1 (by decide)
  · rw [← hg2]; exact hmem 2 (by decide)

theorem exists_smul_flag
    {X : Finset (Fin 22)}
    (hX : X ∈ hexads) {x : Fin 22} (hx : x ∈ X)
    :
    ∃ g : M22, g • x = 0 ∧ g • X = m22HexadF := by
  obtain ⟨a, ha, b, hb, hax, hbx, hab⟩ := exists_two_mem_ne hX x
  obtain ⟨g, hg0, hg1, hg2⟩ := exists_smul_eq_triple (a := x) (b := a) (c := b)
    (a' := (0 : Fin 22)) (b' := 1) (c' := 2) (Ne.symm hax) (Ne.symm hbx) hab (by decide)
    (by decide) (by decide)
  refine ⟨g, hg0, ?_⟩
  have hmem : ∀ p ∈ X, g • p ∈ g • X := fun p hp => Finset.smul_mem_smul_finset hp
  refine eq_of_three_mem (a := 0) (b := 1) (c := 2) (smul_mem_hexads g hX) m22HexadF_mem_hexads
    (by decide) (by decide) (by decide) ?_ ?_ ?_ (by decide) (by decide) (by decide)
  · rw [← hg0]; exact hmem x hx
  · rw [← hg1]; exact hmem a ha
  · rw [← hg2]; exact hmem b hb

theorem stabilizer_m22HexadF : stabilizer M22 m22HexadF = m22HexStab := by
  ext g
  rw [mem_stabilizer_finset_iff, mem_m22HexStab_iff, presHex_iff_mapsTo]
  simp only [mem_m22HexadL_iff]

theorem exists_stabilizer_zero_not_mem_two :
    ∃ g ∈ stabilizer M22 (0 : Fin 22), g ∉ m22TwoStab := by
  obtain ⟨g, hg, hg1⟩ := exists_mem_stabilizer_smul_eq (0 : Fin 22) (x := 1) (y := 2)
    (by decide) (by decide)
  refine ⟨g, hg, fun h => ?_⟩
  have := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp h).2
  rw [hg1] at this
  exact absurd this (by decide)

end CFSG.Quasithin.M22Witt
