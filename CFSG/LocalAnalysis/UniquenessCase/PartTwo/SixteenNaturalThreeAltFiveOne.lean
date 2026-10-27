module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeAltFiveVector
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
  {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_exists_good_vector_of_threeNat_alt_five
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hK : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) = 168)
    (h3 : 3 ∈ D.sig)
    (hV₀ : V₀ = ⊥) :
    ∃ v ∈ V, v ≠ 1 ∧ (∀ t ∈ D.T, t * v = v * t) ∧
      Subgroup.centralizer ({v} : Set G) ≤ D.M := by
  classical
  subst V₀
  have hD5 : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
      (lBar (⊥ : Subgroup G) V hV L)
      (commSub ⊤ (lBar (⊥ : Subgroup G) V hV L))
      (commSub ⊤ (lBar (⊥ : Subgroup G) V hV L) ⊓
        fixV (lBar (⊥ : Subgroup G) V hV L)) 3 := by
    simpa only [wTil, lBar] using hsum
  obtain ⟨w, hw1, hwT, E, hE, hEab, hEcard⟩ :=
    hT.exists_fixed_vector_alt_five hA5 hD5 h7 hK
  obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV w
  have hx0 : x.val ∉ (⊥ : Subgroup G) := by
    intro hxbot
    apply hw1
    exact (QuotientGroup.eq_one_iff (N := modNull (⊥ : Subgroup G) V hV) x).2 hxbot
  have hxne : x.val ≠ 1 := by
    intro hx1
    exact hx0 (by rw [hx1]; exact Subgroup.one_mem (⊥ : Subgroup G))
  have hTle : D.T ≤ stabTil (⊥ : Subgroup G) V :=
    D.sylowM.le.trans c.m_le_stabTil
  have hcomm : ∀ t ∈ D.T, t * x.val = x.val * t := by
    intro t ht
    exact mul_inv_eq_iff_eq_mul.mp
      ((s16c7_mem_fixV_barSub_iff V hV hTle x).1 hwT t ht)
  have hEpt : E ≤ ptCent (Mbar D.M (⊥ : Subgroup G) V hV)
      (mkTil (⊥ : Subgroup G) V hV x) := by
    simpa only [ptCent] using hE
  have hEc : ¬ IsCyclic ↥E := by
    refine s16c7_not_isCyclic_of_elemAbelian Nat.prime_three hEab ?_
    rw [hEcard]
    norm_num
  refine ⟨x.val, x.val_mem, hxne, hcomm, ?_⟩
  exact centralizer_le_of_noncyclic_bar D c.std.h61 Nat.prime_three (by norm_num) h3 hV
    c.setting.hyp16.hyp125.pairFacts (Or.inl rfl) (by rw [Subgroup.card_bot]; norm_num)
    x hx0 hEpt hEab.isPGroup hEc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
