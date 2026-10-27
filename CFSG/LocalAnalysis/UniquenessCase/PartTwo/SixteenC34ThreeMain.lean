module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Z3Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Even
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Z7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c34_isDirectProdOfConj_self {A : Type*} [Group A] (X N : Subgroup A)
    (hN : N ≤ Subgroup.normalizer (X : Set A)) : IsDirectProdOfConj X X N := by
  have hmap : ∀ n ∈ N, X.map (MulAut.conj n).toMonoidHom = X := by
    intro n hn
    have hn' := Subgroup.mem_normalizer_iff.1 (hN hn)
    have hn'' := Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hn))
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hn' y).1 hy
    · intro hx
      refine ⟨n⁻¹ * x * n, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (hn'' x).1 hx
      simpa using this
  have hset : conjSet X N = {X} := by
    ext Y
    simp only [conjSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact hmap n hn
    · rintro rfl
      exact ⟨1, N.one_mem, (hmap 1 N.one_mem).symm⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y hY
    rw [hset] at hY
    exact (Set.mem_singleton_iff.1 hY).le
  · rw [hset]
    simp
  · intro Y hY Z hZ hYZ
    rw [hset] at hY hZ
    exact absurd ((Set.mem_singleton_iff.1 hY).trans (Set.mem_singleton_iff.1 hZ).symm) hYZ
  · intro Y hY
    rw [hset] at hY ⊢
    rw [Set.mem_singleton_iff.1 hY]
    simp

theorem r16_3_four_gamma_le_three (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1217 : R1217 D) (h153 : R15_3Small D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (h136 : Conc4_136 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) :
    Concl163 D V₀ V hV L := by
  by_cases hev : Even (Nat.card ↥(barSub V₀ V hV L))
  · exact Or.inl (Or.inl
      (s16c34_desc153_of_even D h1217 h153 h.hyp151 h.hyp16.small hL hγ hev))
  · have hodd : Odd (Nat.card ↥(barSub V₀ V hV L)) := Nat.not_even_iff_odd.mp hev
    have hrk : rk ↥(commSub ⊤ (lBar V₀ V hV L)) ≤ 3 := by
      have h1 := s16c34_rk_wTil_eq_gamma_of_odd D h.hyp151 hodd
      change rk ↥(wTil V₀ V hV L) ≤ 3
      omega
    have hdvd : Nat.card ↥(lBar V₀ V hV L) ∣ 168 :=
      s16c34_card_lBar_dvd_168 D h1217 h.hyp151 hL hγ
    obtain ⟨t, -, -, -, -, hW⟩ := h136
    rcases s16c34_conc4_136W_odd hW hodd hdvd hrk with ⟨hcyc, hrk2⟩ | ⟨hcyc, hrk3⟩
    · refine Or.inl (Or.inl (Or.inr (Or.inr ⟨⟨L, le_rfl, hcyc, ?_, ?_⟩, Or.inl h.hyp16.small⟩)))
      · exact s16c34_isDirectProdOfConj_self _ _ inf_le_right
      · exact s16c34_alternatingNatural_of_cyclic_three (s15_Infra_vtil_sq_eq_one V₀ V hV)
          hcyc hrk2
    · unfold Concl163
      iterate 12 right
      exact ⟨hcyc, hrk3, s16c34_one_lt_s15_of_rk_wTil_le_three D hx h61 h127 h1217 h hL
        (le_of_eq hrk3)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
