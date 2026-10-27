module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSection

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_sumOfNat_alternating_star
    (c : S168e3Ctx D V₀ V L hV) {n k : ℕ}
    (hS : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) k) :
    SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ k := by
  obtain ⟨-, -, -, himg, hker⟩ := s168e3_section_kappa_data c
  let κ := s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have hZbot : (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)).map κ = ⊥ :=
    s168e3_den_map_eq_bot c
  have h := sumOfNat_map_of_inf_ker_le (hS := hS) (ρ := κ)
    (N := fun H U Z => AlternatingNatural H U Z n)
    (N' := fun H U Z => AlternatingNatural H U Z n)
    (H := lBar V₀ V hV L) (H' := lStar D.M V₀ V hV L)
    (U := wTil V₀ V hV L) (Z := wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) (k := k)
    hker.le
    (fun I _ hIU hNI => by
      rw [hZbot]
      exact s168e3_realizes_map_of_kappa c hIU hNI)
  rwa [himg, hZbot] at h

theorem s168e3_sumOfNat_binarySL_star
    (c : S168e3Ctx D V₀ V L hV) {n a k : ℕ}
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n a)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) k) :
    SumOfNat (fun H U Z => BinaryNaturalSL H U Z n a)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ k := by
  obtain ⟨-, -, -, himg, hker⟩ := s168e3_section_kappa_data c
  let κ := s15T7Kappa V₀ (v1Sub D.M V₀ V hV L) V hV (s15_Infra_le_v1Sub D.M V₀ V hV L)
  have hZbot : (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)).map κ = ⊥ :=
    s168e3_den_map_eq_bot c
  have h := sumOfNat_map_of_inf_ker_le (hS := hS) (ρ := κ)
    (N := fun H U Z => BinaryNaturalSL H U Z n a)
    (N' := fun H U Z => BinaryNaturalSL H U Z n a)
    (H := lBar V₀ V hV L) (H' := lStar D.M V₀ V hV L)
    (U := wTil V₀ V hV L) (Z := wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) (k := k)
    hker.le
    (fun I _ hIU hNI => by
      obtain ⟨K, hF, hFin, hcard, hR⟩ := hNI
      rw [hZbot]
      exact ⟨K, hF, hFin, hcard, s168e3_realizes_map_of_kappa c hIU hR⟩)
  rwa [himg, hZbot] at h

theorem s168e3_case162_1_of_sum_two_alternating
    (c : S168e3Ctx D V₀ V L hV) (hs : 2 ≤ s15 D.M V₀ V hV L)
    {n : ℕ} (hn5 : 5 ≤ n) (hn8 : n ≤ 8)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hS : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_1 D V₀ V hV L :=
  ⟨Or.inl ⟨n, hn5, hn8, hA, s168e3_sumOfNat_alternating_star c hS⟩, hs⟩

theorem s168e3_case162_1_of_sum_two_l3
    (c : S168e3Ctx D V₀ V L hV) (hs : 2 ≤ s15 D.M V₀ V hV L)
    (hL : IsL3 ↥(lBar V₀ V hV L) 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_1 D V₀ V hV L :=
  ⟨Or.inr ⟨hL, s168e3_sumOfNat_binarySL_star c hS⟩, hs⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
