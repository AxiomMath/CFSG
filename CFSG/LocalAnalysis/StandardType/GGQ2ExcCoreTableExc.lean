module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreTable

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section


private def excTableCoverCheck {r : ℕ} (art : List (List ℤ)) (n : ℕ)
    (g : Fin n → Fin r → ℤ) : Bool :=
  art.all fun l => (List.finRange n).any fun i =>
    l == List.ofFn (g i) || l == List.ofFn (fun k => - g i k)

private theorem excMem_of_coverCheck {r n : ℕ} {g : Fin n → Fin r → ℤ} {art : List (List ℤ)}
    (h : excTableCoverCheck art n g = true) :
    ∀ l ∈ art, ∃ i, l = List.ofFn (g i) ∨ l = List.ofFn (fun k => - g i k) := by
  intro l hl
  simp only [excTableCoverCheck, List.all_eq_true] at h
  have h1 := h l hl
  rw [List.any_eq_true] at h1
  obtain ⟨i, -, hi⟩ := h1
  simp only [Bool.or_eq_true, beq_iff_eq] at hi
  exact ⟨i, hi⟩

private def excF4Roots : List (List ℤ) :=
  [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1],
   [1, 1, 1, 1], [0, 1, 2, 1], [0, 1, 1, 0], [1, 1, 1, 0], [1, 1, 2, 1], [1, 2, 2, 1],
   [1, 2, 3, 1], [1, 2, 3, 2], [1, 1, 0, 0], [0, 1, 2, 0], [1, 1, 2, 0], [0, 1, 2, 2],
   [1, 1, 2, 2], [1, 2, 2, 2], [1, 2, 4, 2], [1, 2, 2, 0], [1, 3, 4, 2], [2, 3, 4, 2]]

private def excF4Gamma (i : ExcRaw.Root 0) (k : Fin Tag.F4.rank) : ℤ :=
  ((excF4Roots.getD i []).getD k 0)

private theorem excF4_isRoot : ∀ i, IsRoot Tag.F4 (excF4Gamma i) := by
  intro i
  rw [isRoot_iff_mem_artifactRoots]
  revert i
  decide +kernel

private theorem excF4_cover : ∀ δ, IsRoot Tag.F4 δ →
    ∃ i, δ = excF4Gamma i ∨ δ = -excF4Gamma i := by
  intro δ hδ
  rw [isRoot_iff_mem_artifactRoots] at hδ
  obtain ⟨i, hi | hi⟩ := excMem_of_coverCheck (art := Tag.F4.artifactRoots)
    (g := excF4Gamma) (by decide +kernel) (List.ofFn δ) hδ
  · exact ⟨i, Or.inl (List.ofFn_injective hi)⟩
  · exact ⟨i, Or.inr (List.ofFn_injective hi)⟩

private theorem excF4_inj : ∀ i j : ExcRaw.Root 0,
    (excF4Gamma i = excF4Gamma j ∨ excF4Gamma i = -excF4Gamma j) → i = j := by
  decide +kernel

private theorem excF4_F : ∀ (i : ExcRaw.Root 0) (k : Fin (ExcRaw.dim 0)),
    ExcRaw.F 0 i k = corootPair
      (Pi.single (Fin.cast (by rfl : ExcRaw.dim 0 = Tag.F4.rank) k) 1) (excF4Gamma i) := by
  decide +kernel

private theorem excF4_H : ∀ (i : ExcRaw.Root 0) (j : Fin Tag.F4.rank),
    corootPair (excF4Gamma i) (Pi.single j 1) =
      ∑ k, ExcRaw.H 0 i k * corootPair
        (Pi.single (Fin.cast (by rfl : ExcRaw.dim 0 = Tag.F4.rank) k) 1) (Pi.single j 1) := by
  decide +kernel

private def excF4Cinv : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (ZMod 3) :=
  !![2, 0, 1, 2; 0, 0, 2, 1; 2, 1, 0, 0; 1, 2, 0, 2]

private theorem excF4_Cinv : ∀ j l : Fin Tag.F4.rank,
    ∑ k, excF4Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
      if j = l then 1 else 0 := by
  decide +kernel

private def excE7Gamma (i : ExcRaw.Root 4) (k : Fin Tag.E7.rank) : ℤ :=
  ExcRaw.H 4 i (Fin.cast (by rfl : Tag.E7.rank = ExcRaw.dim 4) k)

private theorem excE7_isRoot : ∀ i, IsRoot Tag.E7 (excE7Gamma i) := by
  intro i
  rw [isRoot_iff_mem_artifactRoots]
  revert i
  decide +kernel

private theorem excE7_cover : ∀ δ, IsRoot Tag.E7 δ →
    ∃ i, δ = excE7Gamma i ∨ δ = -excE7Gamma i := by
  intro δ hδ
  rw [isRoot_iff_mem_artifactRoots] at hδ
  obtain ⟨i, hi | hi⟩ := excMem_of_coverCheck (art := Tag.E7.artifactRoots)
    (g := excE7Gamma) (by decide +kernel) (List.ofFn δ) hδ
  · exact ⟨i, Or.inl (List.ofFn_injective hi)⟩
  · exact ⟨i, Or.inr (List.ofFn_injective hi)⟩

private theorem excE7_inj : ∀ i j : ExcRaw.Root 4,
    (excE7Gamma i = excE7Gamma j ∨ excE7Gamma i = -excE7Gamma j) → i = j := by
  decide +kernel

private theorem excE7_F : ∀ (i : ExcRaw.Root 4) (k : Fin (ExcRaw.dim 4)),
    ExcRaw.F 4 i k = corootPair
      (Pi.single (Fin.cast (by rfl : ExcRaw.dim 4 = Tag.E7.rank) k) 1) (excE7Gamma i) := by
  decide +kernel

private theorem excE7_H : ∀ (i : ExcRaw.Root 4) (j : Fin Tag.E7.rank),
    corootPair (excE7Gamma i) (Pi.single j 1) =
      ∑ k, ExcRaw.H 4 i k * corootPair
        (Pi.single (Fin.cast (by rfl : ExcRaw.dim 4 = Tag.E7.rank) k) 1) (Pi.single j 1) := by
  decide +kernel

private def excE7Cinv : Matrix (Fin Tag.E7.rank) (Fin Tag.E7.rank) (ZMod 3) :=
  !![2, 2, 0, 1, 0, 2, 1; 2, 2, 1, 0, 0, 0, 0; 0, 1, 0, 2, 0, 1, 2;
     1, 0, 2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 2, 1; 2, 0, 1, 0, 2, 1, 2;
     1, 0, 2, 0, 1, 2, 0]

private theorem excE7_Cinv : ∀ j l : Fin Tag.E7.rank,
    ∑ k, excE7Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
      if j = l then 1 else 0 := by
  decide +kernel

private def excE8Gamma (i : ExcRaw.Root 5) (k : Fin Tag.E8.rank) : ℤ :=
  ExcRaw.H 5 i (Fin.cast (by rfl : Tag.E8.rank = ExcRaw.dim 5) k)

private theorem excE8_isRoot : ∀ i, IsRoot Tag.E8 (excE8Gamma i) := by
  intro i
  rw [isRoot_iff_mem_artifactRoots]
  revert i
  decide +kernel

private theorem excE8_cover : ∀ δ, IsRoot Tag.E8 δ →
    ∃ i, δ = excE8Gamma i ∨ δ = -excE8Gamma i := by
  intro δ hδ
  rw [isRoot_iff_mem_artifactRoots] at hδ
  obtain ⟨i, hi | hi⟩ := excMem_of_coverCheck (art := Tag.E8.artifactRoots)
    (g := excE8Gamma) (by decide +kernel) (List.ofFn δ) hδ
  · exact ⟨i, Or.inl (List.ofFn_injective hi)⟩
  · exact ⟨i, Or.inr (List.ofFn_injective hi)⟩

private theorem excE8_inj : ∀ i j : ExcRaw.Root 5,
    (excE8Gamma i = excE8Gamma j ∨ excE8Gamma i = -excE8Gamma j) → i = j := by
  decide +kernel

private theorem excE8_F : ∀ (i : ExcRaw.Root 5) (k : Fin (ExcRaw.dim 5)),
    ExcRaw.F 5 i k = corootPair
      (Pi.single (Fin.cast (by rfl : ExcRaw.dim 5 = Tag.E8.rank) k) 1) (excE8Gamma i) := by
  decide +kernel

private theorem excE8_H : ∀ (i : ExcRaw.Root 5) (j : Fin Tag.E8.rank),
    corootPair (excE8Gamma i) (Pi.single j 1) =
      ∑ k, ExcRaw.H 5 i k * corootPair
        (Pi.single (Fin.cast (by rfl : ExcRaw.dim 5 = Tag.E8.rank) k) 1) (Pi.single j 1) := by
  decide +kernel

private def excE8Cinv : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 3) :=
  !![1, 2, 1, 1, 2, 0, 1, 2; 2, 2, 1, 0, 0, 0, 0, 0; 1, 1, 2, 2, 1, 0, 2, 1;
     1, 0, 2, 0, 0, 0, 0, 0; 2, 0, 1, 0, 2, 0, 1, 2; 0, 0, 0, 0, 0, 0, 2, 1;
     1, 0, 2, 0, 1, 2, 0, 0; 2, 0, 1, 0, 2, 1, 0, 2]

private theorem excE8_Cinv : ∀ j l : Fin Tag.E8.rank,
    ∑ k, excE8Cinv j k * ((corootPair (Pi.single l 1) (Pi.single k 1) : ℤ) : ZMod 3) =
      if j = l then 1 else 0 := by
  decide +kernel

theorem excCoreDatum_F4 : ExcCoreDatum 0 .F4 := by
  intro L _ _ p S hS
  exact nonempty_excCoordDatum_of_table (hτ := Or.inl rfl) (hm := by decide)
    (hdim := (by rfl : ExcRaw.dim 0 = Tag.F4.rank)) excF4Gamma excF4_isRoot excF4_cover
    excF4_inj excF4_F excF4_H excF4Cinv excF4_Cinv S hS

theorem excCoreDatum_E7 : ExcCoreDatum 4 .E7 := by
  intro L _ _ p S hS
  exact nonempty_excCoordDatum_of_table (hτ := Or.inr (Or.inr (Or.inl rfl))) (hm := by decide)
    (hdim := (by rfl : ExcRaw.dim 4 = Tag.E7.rank)) excE7Gamma excE7_isRoot excE7_cover
    excE7_inj excE7_F excE7_H excE7Cinv excE7_Cinv S hS

theorem excCoreDatum_E8 : ExcCoreDatum 5 .E8 := by
  intro L _ _ p S hS
  exact nonempty_excCoordDatum_of_table (hτ := Or.inr (Or.inr (Or.inr rfl))) (hm := by decide)
    (hdim := (by rfl : ExcRaw.dim 5 = Tag.E8.rank)) excE8Gamma excE8_isRoot excE8_cover
    excE8_inj excE8_F excE8_H excE8Cinv excE8_Cinv S hS

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
