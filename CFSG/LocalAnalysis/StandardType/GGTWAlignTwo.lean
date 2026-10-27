module

public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGTWSurvDefs
public import CFSG.LocalAnalysis.StandardType.GGTWAlign
public import CFSG.LocalAnalysis.StandardType.GGTWPositions
public import CFSG.LocalAnalysis.StandardType.GGResConjWire

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTW_align_two {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L J K : Subgroup G} (hBs : IsElemAbelian p Bs) {N : ℕ} (hN5 : 5 ≤ N)
    (hXL : GGResXDatumA p Bs L (N - 1)) {n : ℕ} (hXK : GGResXDatumA p Bs K n)
    (hLd : GGResTwoNodeSideDatum p Bs L J) (hK : GGResTwoNodeSideDatum p Bs K J) :
    GGTWAligned p N 2 Bs L J K := by
  obtain ⟨ΛL, i1L, i2L, ML0, CL0, VL, i3L, i4L, ιL, φL0, hL0, αL0, eL, hMLeqL, hWML0,
    hIntL0, hlinL0, hreflL0, hpairL0, hfL0ex, hclosL0⟩ := hXL
  letI := i1L; letI := i2L; letI := i3L; letI := i4L
  obtain ⟨fL0, hfL0⟩ := hfL0ex
  have hXKcard : Nat.card (ggAutomizer K Bs) = (n + 1).factorial := hXK.card_automizer
  obtain ⟨ΛK, i1K, i2K, MK0, CK0, VK, i3K, i4K, ιK, φK0, hK0, αK0, eK0, hMKeqK, hWMK0,
    hIntK0, hlinK0, hreflK0, hpairK0, hfK0ex, hclosK0⟩ := hXK
  letI := i1K; letI := i2K; letI := i3K; letI := i4K
  obtain ⟨fK0, hfK0⟩ := hfK0ex
  obtain ⟨Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α,
    hb, hcard, hWML, hIntL, hWMK, hIntK, hlin, hrefl, hpairL, hpairK, hfLex, hfKex,
    hclosL, hclosK, hdel, hclosJ⟩ :=
    ggResTwoNodeDatum_of_sides_card_two ggWeylSimpleSystemsConjInput_holds hp2 hLd hK
  letI := i1; letI := i2; letI := i1a; letI := i2a; letI := i3; letI := i4
  obtain ⟨fL, hfL⟩ := hfLex
  obtain ⟨fK, hfK⟩ := hfKex
  have hN2 : 2 ≤ N - 1 := by omega
  obtain ⟨e, hMLeq⟩ :=
    ggTW_typeA_of_datum (p := p) (n := N - 1) hp2 hN2 hBs (ggAutomizer L Bs)
      (Λ₁ := ΛL) (M₁ := ML0) eL hMLeqL hWML0 fL0 φL0 hfL0 hreflL0
      (Λ₂ := Λ) (M₂ := ML) hWML fL (fun i => φ (Sum.inl i)) (fun i => hfL i)
      (fun i => hrefl (Sum.inl i))
  obtain ⟨pos, e', hMLeq', hInJ⟩ := ggTW_positions hN5 e hMLeq hb hdel
  have hn2 : 2 ≤ n := by
    classical
    have h3MK : 3 ≤ Nat.card MK.Group := by
      haveI : Finite ↥(ggAutomizer K Bs) :=
        Nat.finite_of_card_ne_zero (by rw [hXKcard]; exact Nat.factorial_ne_zero _)
      haveI : Finite MK.Group :=
        Finite.of_injective (fK : MK.Group → ↥(ggAutomizer K Bs)) fK.injective
      obtain ⟨a₁, a₂, ha⟩ :=
        (Fintype.one_lt_card_iff (α := Λa)).mp
          (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
      have hs₁ : MK.simple (Sum.inr a₁) ≠ 1 := MK.toCoxeterSystem.simple_ne_one _
      have hs₂ : MK.simple (Sum.inr a₂) ≠ 1 := MK.toCoxeterSystem.simple_ne_one _
      have hst : MK.simple (Sum.inr a₁) ≠ MK.simple (Sum.inr a₂) := fun h =>
        ha (Sum.inr_injective (MK.toCoxeterSystem.simple_injective h))
      have hfinset : ({1, MK.simple (Sum.inr a₁), MK.simple (Sum.inr a₂)} :
          Finset MK.Group).card = 3 :=
        (Finset.card_eq_three).mpr ⟨1, _, _, hs₁.symm, hs₂.symm, hst, rfl⟩
      calc 3 = _ := hfinset.symm
        _ ≤ Nat.card MK.Group := Finset.card_le_natCard _
    have h3K : 3 ≤ (n + 1).factorial := by
      rw [← hXKcard]
      exact h3MK.trans (le_of_eq (Nat.card_congr fK.toEquiv))
    by_contra h
    have hn : n < 2 := by omega
    interval_cases n <;> norm_num at h3K
  obtain ⟨eK, hMKeq⟩ :=
    ggTW_typeA_of_datum (p := p) (n := n) hp2 hn2 hBs (ggAutomizer K Bs)
      (Λ₁ := ΛK) (M₁ := MK0) eK0 hMKeqK hWMK0 fK0 φK0 hfK0 hreflK0
      (Λ₂ := {i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) (M₂ := MK) hWMK fK
      (fun o => φ (o.map Subtype.val id)) (fun o => hfK o)
      (fun o => hrefl (o.map Subtype.val id))
  have hΛcard : Nat.card Λ = N - 1 := by
    rw [← Nat.card_congr e, Nat.card_fin]
  have hcard_sub : Nat.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} = N - 3 := by
    have h2 : Fintype.card {i : Λ // i = b₁ ∨ i = b₂} = 2 :=
      Fintype.card_subtype_eq_or_eq_of_ne hb
    have hcompl : Fintype.card {i : Λ // ¬(i = b₁ ∨ i = b₂)} = Fintype.card Λ - 2 := by
      rw [Fintype.card_subtype_compl, h2]
    have heq : Nat.card {i : Λ // i ≠ b₁ ∧ i ≠ b₂} =
        Nat.card {i : Λ // ¬(i = b₁ ∨ i = b₂)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun i => by simp [not_or]))
    rw [heq, Nat.card_eq_fintype_card, hcompl, ← Nat.card_eq_fintype_card, hΛcard]
    omega
  have hcard_sum : Nat.card ({i : Λ // i ≠ b₁ ∧ i ≠ b₂} ⊕ Λa) = N - 1 := by
    rw [Nat.card_sum, hcard_sub, hcard]
    omega
  have hn_eq : n = N - 1 := by
    have h := Nat.card_congr eK
    rw [Nat.card_fin, hcard_sum] at h
    exact h
  subst n
  exact ⟨pos, Λ, i1, i2, b₁, b₂, Λa, i1a, i2a, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, e',
    hb, hcard, hInJ, hMLeq', hWML, hIntL, hWMK, hIntK, (fun _ => ⟨eK, hMKeq⟩),
    hlin, hrefl, hpairL, hpairK, hclosL, hclosK, hclosJ⟩

end CFSG.StandardType
