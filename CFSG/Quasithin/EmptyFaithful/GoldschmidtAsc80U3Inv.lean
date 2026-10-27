module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Elt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Syl

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F]

section Coordinates

variable {Y : Subgroup (SU3F p F)} {W : Submodule F (Fin 3 → F)}

theorem single_mem [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hB : leviU hF ≤ Y)
    (hW : ∀ g ∈ Y, ∀ w ∈ W, matU g *ᵥ w ∈ W) {w : Fin 3 → F} (hw : w ∈ W) (i : Fin 3) :
    (Pi.single i (w i) : Fin 3 → F) ∈ W := by
  have h2 := two_ne_zero_u hp2 hF
  have hd := hW _ (hB (dsU_mem_leviU hp2 hF i)) w hw
  have hmem := W.smul_mem (2 : F)⁻¹ (W.add_mem hw hd)
  convert hmem using 1
  funext j
  simp only [matU_dsU, dsMat, Matrix.mulVec_diagonal, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  by_cases hj : j = i
  · subst hj
    simp only [Pi.single_eq_same, ite_true]
    field_simp
    ring
  · simp only [Pi.single_eq_of_ne hj, hj, ite_false]
    field_simp
    ring

theorem single_one_mem [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hB : leviU hF ≤ Y)
    (hW : ∀ g ∈ Y, ∀ w ∈ W, matU g *ᵥ w ∈ W) {w : Fin 3 → F} (hw : w ∈ W) {i : Fin 3}
    (hi : w i ≠ 0) : (Pi.single i 1 : Fin 3 → F) ∈ W := by
  have hmem := W.smul_mem (w i)⁻¹ (single_mem hp2 hF hB hW hw i)
  convert hmem using 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp [hi]
  · simp [Pi.single_eq_of_ne hj]

abbrev HasCoord (W : Submodule F (Fin 3 → F)) (i : Fin 3) : Prop := ∃ w ∈ W, w i ≠ 0

theorem hasCoord_swap (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hB : leviU hF ≤ Y)
    (hW : ∀ g ∈ Y, ∀ w ∈ W, matU g *ᵥ w ∈ W) : HasCoord W 0 ↔ HasCoord W 1 := by
  have hs := hB (swapU_mem_leviU hp2 hF)
  constructor
  · rintro ⟨w, hw, h0⟩
    refine ⟨matU (swapU hF) *ᵥ w, hW _ hs w hw, ?_⟩
    simpa [matU_swapU, swapMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h0
  · rintro ⟨w, hw, h1⟩
    refine ⟨matU (swapU hF) *ᵥ w, hW _ hs w hw, ?_⟩
    simpa [matU_swapU, swapMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using h1

theorem hasCoord_cases [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2) (hB : leviU hF ≤ Y)
    (hW : ∀ g ∈ Y, ∀ w ∈ W, matU g *ᵥ w ∈ W) (hbot : W ≠ ⊥) (htop : W ≠ ⊤) :
    (HasCoord W 0 ∧ HasCoord W 1 ∧ ¬ HasCoord W 2) ∨
      (¬ HasCoord W 0 ∧ ¬ HasCoord W 1 ∧ HasCoord W 2) := by
  have hsw := hasCoord_swap hp2 hF hB hW
  have hex : ∃ i, HasCoord W i := by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
    by_contra hno
    apply hw0
    funext i
    by_contra hi
    exact hno ⟨i, w, hw, hi⟩
  have hnotall : ¬ (HasCoord W 0 ∧ HasCoord W 1 ∧ HasCoord W 2) := by
    rintro ⟨⟨w0, hw0, h0⟩, ⟨w1, hw1, h1⟩, ⟨w2, hw2, h2⟩⟩
    apply htop
    rw [Submodule.eq_top_iff']
    intro v
    have hv : v = ∑ i, (Pi.single i (v i) : Fin 3 → F) := (Finset.univ_sum_single v).symm
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => ?_
    have he : (Pi.single i 1 : Fin 3 → F) ∈ W := by
      fin_cases i
      · exact single_one_mem hp2 hF hB hW hw0 h0
      · exact single_one_mem hp2 hF hB hW hw1 h1
      · exact single_one_mem hp2 hF hB hW hw2 h2
    have := W.smul_mem (v i) he
    convert this using 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Pi.single_eq_of_ne hj]
  by_cases h2 : HasCoord W 2
  · right
    refine ⟨fun h0 => hnotall ⟨h0, hsw.mp h0, h2⟩, fun h1 => hnotall ⟨hsw.mpr h1, h1, h2⟩, h2⟩
  · left
    obtain ⟨i, hi⟩ := hex
    have h01 : HasCoord W 0 ∧ HasCoord W 1 := by
      fin_cases i
      · exact ⟨hi, hsw.mp hi⟩
      · exact ⟨hsw.mpr hi, hi⟩
      · exact absurd hi h2
    exact ⟨h01.1, h01.2, h2⟩

end Coordinates

theorem bar_last_ne_zero (hF : Nat.card F = p ^ 2) (g : SU3F p F) (h02 : matU g 0 2 = 0)
    (h12 : matU g 1 2 = 0) : (uniData hF).bar (matU g 2 2) ≠ 0 := by
  intro h
  have := unitary_cols hF g 2 2
  simp [Fin.sum_univ_three, h02, h12, h] at this

theorem entries_of_cols (hF : Nat.card F = p ^ 2) (g : SU3F p F) (h02 : matU g 0 2 = 0)
    (h12 : matU g 1 2 = 0) : matU g 2 0 = 0 ∧ matU g 2 1 = 0 := by
  have hne := bar_last_ne_zero hF g h02 h12
  have e0 := unitary_cols hF g 2 0
  have e1 := unitary_cols hF g 2 1
  simp only [Fin.sum_univ_three, h02, h12, map_zero, zero_mul, zero_add] at e0 e1
  simp only [show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    ite_false] at e0 e1
  exact ⟨(mul_eq_zero.mp e0).resolve_left hne, (mul_eq_zero.mp e1).resolve_left hne⟩

theorem entries_of_rows (hF : Nat.card F = p ^ 2) (g : SU3F p F) (h20 : matU g 2 0 = 0)
    (h21 : matU g 2 1 = 0) : matU g 0 2 = 0 ∧ matU g 1 2 = 0 := by
  have hne : (uniData hF).bar (matU g 2 2) ≠ 0 := by
    intro h
    have := unitary_rows hF g 2 2
    simp [Fin.sum_univ_three, h20, h21, h] at this
  have e0 := unitary_rows hF g 0 2
  have e1 := unitary_rows hF g 1 2
  simp only [Fin.sum_univ_three, h20, h21, map_zero, mul_zero, zero_add] at e0 e1
  simp only [show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    ite_false] at e0 e1
  exact ⟨(mul_eq_zero.mp e0).resolve_right hne, (mul_eq_zero.mp e1).resolve_right hne⟩

theorem le_leviU_of_invariant [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {Y : Subgroup (SU3F p F)} (hB : leviU hF ≤ Y) {W : Submodule F (Fin 3 → F)}
    (hW : ∀ g ∈ Y, ∀ w ∈ W, matU g *ᵥ w ∈ W) (hbot : W ≠ ⊥) (htop : W ≠ ⊤) : Y ≤ leviU hF := by
  intro g hg
  rw [mem_leviU_iff hp2 hF]
  rcases hasCoord_cases hp2 hF hB hW hbot htop with ⟨h0, h1, h2⟩ | ⟨h0, h1, ⟨w, hw, hwi⟩⟩
  ·
    obtain ⟨w0, hw0, hi0⟩ := h0
    obtain ⟨w1, hw1, hi1⟩ := h1
    have he0 := single_one_mem hp2 hF hB hW hw0 hi0
    have he1 := single_one_mem hp2 hF hB hW hw1 hi1
    have h20 : matU g 2 0 = 0 := by
      by_contra hne
      exact h2 ⟨matU g *ᵥ Pi.single 0 1, hW g hg _ he0,
        by simpa [Matrix.mulVec_single_one] using hne⟩
    have h21 : matU g 2 1 = 0 := by
      by_contra hne
      exact h2 ⟨matU g *ᵥ Pi.single 1 1, hW g hg _ he1,
        by simpa [Matrix.mulVec_single_one] using hne⟩
    obtain ⟨h02, h12⟩ := entries_of_rows hF g h20 h21
    exact ⟨h02, h12, h20, h21⟩
  ·
    have he2 := single_one_mem hp2 hF hB hW hw hwi
    have h02 : matU g 0 2 = 0 := by
      by_contra hne
      exact h0 ⟨matU g *ᵥ Pi.single 2 1, hW g hg _ he2,
        by simpa [Matrix.mulVec_single_one] using hne⟩
    have h12 : matU g 1 2 = 0 := by
      by_contra hne
      exact h1 ⟨matU g *ᵥ Pi.single 2 1, hW g hg _ he2,
        by simpa [Matrix.mulVec_single_one] using hne⟩
    obtain ⟨h20, h21⟩ := entries_of_cols hF g h02 h12
    exact ⟨h02, h12, h20, h21⟩

theorem le_leviU_of_not_irr [Finite F] (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    {Y : Subgroup (SU3F p F)} (hB : leviU hF ≤ Y)
    (hred : ¬ IsIrrIn (StatedSU 3 (p ^ 1) F) Y) : Y ≤ leviU hF := by
  obtain ⟨W, hW, hbot, htop⟩ := exists_invariant_of_not_irr (p := p) hred
  exact le_leviU_of_invariant hp2 hF hB hW hbot htop

end CFSG.Quasithin.E2P.Asc80
