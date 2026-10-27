module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem S168e3Ctx.toS16kStar (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 1) : S16kStar D V₀ V L hV := by
  obtain ⟨ρ, θ, hρsurj, hequiv, hker⟩ := s168e3_star c hs
  have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊤ :=
    wTil_eq_top_of_case163_2 c.conc hs
  have hstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  refine ⟨ρ, θ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact θ.surjective
  · intro h w
    exact hequiv h w
  · rw [hker, hcomm, top_inf_eq]
  · rw [hcomm, Subgroup.map_top_of_surjective ρ hρsurj, hstar]

theorem s168e3_case162_2_of_star_natSL
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hstar := c.toS16kStar hs
  exact ⟨hs, Or.inr (Or.inl ⟨n, h3, h5, s16k_isLn_of_isSLn h3 hSL,
    hstar.sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_binaryNaturalSL_map hI ρ hk θ hθ he) hsum⟩)⟩

theorem s168e3_case162_2_of_star_alt
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    {n : ℕ} (h5 : 5 ≤ n) (h11 : n ≤ 11)
    (hAlt : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hstar := c.toS16kStar hs
  exact ⟨hs, Or.inl ⟨n, h5, h11, hAlt,
    hstar.sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_alternatingNatural_map hI ρ hk θ hθ he) hsum⟩⟩

theorem s168e3_case162_2_of_star_natSp6
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatSpn H U Z 6 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hstar := c.toS16kStar hs
  exact ⟨hs, Or.inr (Or.inr (Or.inl ⟨hSp,
    hstar.sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_natSpn_map hI ρ hk θ hθ he) hsum⟩))⟩

theorem s168e3_case162_2_of_star_natOmegaMinus_six
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hstar := c.toS16kStar hs
  exact ⟨hs, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOm,
    hstar.sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_natOmegaMinus_map hI ρ hk θ hθ he) hsum⟩)))⟩

theorem s168e3_case162_2_of_star_natOmegaMinus_eight
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hsum : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L := by
  have hstar := c.toS16kStar hs
  exact ⟨hs, Or.inr (Or.inr (Or.inr (Or.inr ⟨hOm,
    hstar.sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_natOmegaMinus_map hI ρ hk θ hθ he) hsum⟩)))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
