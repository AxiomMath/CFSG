module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.UC2TenNine
public import CFSG.Quasithin.H13.A5S1327j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem seventeen_sixtyseven_of_mem_calL2Star
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL2Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro _ p hp L hL X hXeq hX2
  have hXp : X ∉ calLp D p := hX2.2.1
  have hne : X ≠ L := by
    intro h
    exact hXp (h ▸ hL)
  have hne' : conjClosure D.M L ≠ L := fun h => hne (hXeq ▸ h)
  obtain ⟨n, x, -, -, hXne, hshape, -⟩ := p42_alt2_of_ne h42 hp hL.1 hne'
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fun h => hXne (hXeq ▸ h), n,
    hshape.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩)))

theorem seventeen_sixtyseven_of_mem_calL3Star
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL3Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro _ p hp L hL X hXeq hX3
  have hA5 : IsA5xA5 (Bar2 X) := hX3.2
  have hne : X ≠ L := by
    intro h
    exact not_isQuasisimple_of_isA5xA5 (h ▸ hA5) hL.1.2.2
  have hne' : conjClosure D.M L ≠ L := fun h => hne (hXeq ▸ h)
  obtain ⟨n, x, -, -, hXne, hshape, -⟩ := p42_alt2_of_ne h42 hp hL.1 hne'
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨fun h => hXne (hXeq ▸ h), n,
    hshape.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩)))

theorem seventeen_sixtyseven_of_mem_calL4Star {D : Data G} {V₀ V : Subgroup G} :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL4Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro _ _ _ _ _ _ _ hX4
  obtain ⟨⟨n, hshape⟩, -⟩ := hX4.2
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2 ^ n, ⟨n, rfl⟩, hshape⟩)))

theorem seventeen_sixtyseven_of_mem_calL5Star
    {D : Data G} {V₀ V : Subgroup G} :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL5Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro _ _ _ _ _ _ _ hX5
  obtain ⟨e⟩ := hX5.2
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨2, ⟨1, by norm_num⟩, Or.inl (CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e)⟩)))

theorem seventeen_sixtyseven_of_mem_calLjStar_of_two_le
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → ∀ j : ℕ, 2 ≤ j → j ≤ 5 → X ∈ calLjStar D p j →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro hV0 p hp L hL X hXeq j hj2 hj5 hj
  interval_cases j
  · exact seventeen_sixtyseven_of_mem_calL2Star h42 hV0 p hp L hL X hXeq
      (by simpa [calLjStar] using hj)
  · exact seventeen_sixtyseven_of_mem_calL3Star h42 hV0 p hp L hL X hXeq
      (by simpa [calLjStar] using hj)
  · exact seventeen_sixtyseven_of_mem_calL4Star (V := V) hV0 p hp L hL X hXeq
      (by simpa [calLjStar] using hj)
  · exact seventeen_sixtyseven_of_mem_calL5Star (V := V) hV0 p hp L hL X hXeq
      (by simpa [calLjStar] using hj)

theorem seventeen_sixtyseven_of_mem_calL0Star_of_not_calL1Star
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) :
    V₀ ≠ ⊥ → ∀ p : ℕ, p ∈ D.sig → ∀ L ∈ calLp D p, ∀ X : Subgroup G,
      X = conjClosure D.M L → X ∈ calL0Star D p → X ∉ calL1Star D p →
        IsU5 (Bar2 X) 2 ∨
        (∃ n : ℕ, IsPowTwo n ∧ IsU4 (Bar2 X) n) ∨
        (∃ n : ℕ, IsSp4 (Bar2 X) n ∧ SwapsParabolics D.T X) ∨
        (X ≠ L ∧ ∃ n : ℕ, IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) ∨
        (∃ n : ℕ, IsPowTwo n ∧ (IsL2 (Bar2 X) n ∨ IsU3 (Bar2 X) n)) := by
  intro hV0 p hp L hL X hXeq hX0 hX1
  obtain ⟨hj1, hj5, -, -⟩ := jM_mem_of_nonempty (D := D) (p := p) ⟨X, hX0⟩
  have hXj : X ∈ calLjStar D p (jM D p) := by simpa [calL0Star] using hX0
  have hj2 : 2 ≤ jM D p := by
    rcases Nat.eq_or_lt_of_le hj1 with h | h
    · have h1 : jM D p = 1 := h.symm
      exact absurd (by simpa [h1, calLjStar] using hXj) hX1
    · omega
  exact seventeen_sixtyseven_of_mem_calLjStar_of_two_le h42 hV0 p hp L hL X hXeq
    (jM D p) hj2 hj5 hXj

theorem eq_self_of_mem_calL1Star_of_simple {D : Data G} {p : ℕ} {L X : Subgroup G}
    (hL : L ∈ calLp D p) (hXeq : X = conjClosure D.M L) (hX1 : X ∈ calL1Star D p)
    (hs : IsSimpleGroup (Bar2 X)) : X = L := by
  have hs' : IsSimpleGroup (Bar2 (conjClosure D.M L)) := by rwa [hXeq] at hs
  exact hXeq.trans (conjClosure_eq_self_of_isSimpleGroup_bar2 hL.1 hs')

theorem subgroupOf_normal_of_mem_calL1Star {D : Data G} {p : ℕ} {L X : Subgroup G}
    (hL : L ∈ calLp D p) (hXeq : X = conjClosure D.M L) (hX1 : X ∈ calL1Star D p)
    (hs : IsSimpleGroup (Bar2 X)) : (L.subgroupOf D.M).Normal := by
  have hXL : X = L := eq_self_of_mem_calL1Star_of_simple hL hXeq hX1 hs
  have hnormX : D.M ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXeq]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
  have hnormL : D.M ≤ Subgroup.normalizer (L : Set G) := hXL ▸ hnormX
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.1.le).2 hnormL

theorem uniqueMax_sup_T_of_mem_calL1Star {D : Data G} {p : ℕ} {L X : Subgroup G}
    (h869 : F08.R869 D) (hL : L ∈ calLp D p) (hXeq : X = conjClosure D.M L)
    (hX1 : X ∈ calL1Star D p) (hs : IsSimpleGroup (Bar2 X)) (hnt : ¬ F08.Thin8 L) :
    UniqueMax D.M (L ⊔ D.T) := by
  have hXL : X = L := eq_self_of_mem_calL1Star_of_simple hL hXeq hX1 hs
  have hUX : UniqueMax D.M X := by
    rw [hXeq]
    exact uniqueMax_conjClosure_of_not_thin h869 hL.1 hnt
  have hUL : UniqueMax D.M L := hXL ▸ hUX
  exact uc22p22u_uniqueMax_mono D le_sup_left (sup_le hL.1.1.le D.sylowM.le) hUL

theorem seventeen_sixtyseven_l1_false_of_torusElement {D : Data G} {V₀ V : Subgroup G}
    (h109 : Inputs1719.UC2_10_9 D) (hV : Hyp125 D V₀ V) (hV0 : V₀ ≠ ⊥)
    (h869 : F08.R869 D) {p : ℕ} {L X : Subgroup G} (hL : L ∈ calLp D p)
    (hXeq : X = conjClosure D.M L) (hX1 : X ∈ calL1Star D p)
    (hs : IsSimpleGroup (Bar2 X)) (hnt : ¬ F08.Thin8 L)
    {s r : ℕ} (hso : Odd s) (hr : r.Prime) (hdvd : r ∣ 2 ^ s - 1)
    {B : Subgroup G} (hBL : B ≤ L) (hBT : B ≤ Subgroup.normalizer (D.T : Set G))
    (hcard : Nat.card B = r) (hBU : UC6.InU D.M B) : False := by
  have hnormal : (L.subgroupOf D.M).Normal :=
    subgroupOf_normal_of_mem_calL1Star hL hXeq hX1 hs
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.1.le).1 hnormal
  have hUL : UniqueMax D.M (L ⊔ D.T) :=
    uniqueMax_sup_T_of_mem_calL1Star h869 hL hXeq hX1 hs hnt
  exact hV0 (v0_eq_bot_of_uc2_10_9_of_normal h109 hV hL.1 hLN hUL hso hr hdvd
    hBL hBT hcard hBU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
