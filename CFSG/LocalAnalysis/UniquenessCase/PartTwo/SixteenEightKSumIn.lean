module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConvEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_case162_2_of_sl (h : S16kBase D V₀ V L hV) {n : ℕ} (h3 : 3 ≤ n) (h5 : n ≤ 5)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inr (Or.inl ⟨n, h3, h5, s16k_isLn_of_isSLn h3 hSL,
    (s16k_star h).sumOfNat_map
      (fun ρ θ hθ he hk I _ hI => s16k_binaryNaturalSL_map hI ρ hk θ hθ he) hS⟩)⟩

theorem s16k_case162_2_of_sp_six (h : S16kBase D V₀ V L hV)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1)
    (hS : SumOfNat (fun H U Z => NatSpn H U Z 6 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inr (Or.inr (Or.inl ⟨hSp, (s16k_star h).sumOfNat_map
    (fun ρ θ hθ he hk I _ hI => s16k_natSpn_map hI ρ hk θ hθ he) hS⟩))⟩

theorem s16k_case162_2_of_omegaMinus_six (h : S16kBase D V₀ V L hV)
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 6 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inr (Or.inr (Or.inr (Or.inl ⟨hΩ, (s16k_star h).sumOfNat_map
    (fun ρ θ hθ he hk I _ hI => s16k_natOmegaMinus_map hI ρ hk θ hθ he) hS⟩)))⟩

theorem s16k_case162_2_of_omegaMinus_eight (h : S16kBase D V₀ V L hV)
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 8 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inr (Or.inr (Or.inr (Or.inr ⟨hΩ, (s16k_star h).sumOfNat_map
    (fun ρ θ hθ he hk I _ hI => s16k_natOmegaMinus_map hI ρ hk θ hθ he) hS⟩)))⟩

theorem s16k_case162_2_of_alt (h : S16kBase D V₀ V L hV) {n : ℕ} (h5 : 5 ≤ n) (h11 : n ≤ 11)
    (hA : IsAlt ↥(lBar V₀ V hV L) n)
    (hS : SumOfNat (fun H U Z => AlternatingNatural H U Z n) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inl ⟨n, h5, h11, hA, (s16k_star h).sumOfNat_map
    (fun ρ θ hθ he hk I _ hI => s16k_alternatingNatural_map hI ρ hk θ hθ he) hS⟩⟩

theorem s16k_case162_2_of_omegaMinus_four (h : S16kBase D V₀ V L hV)
    (hΩ : IsOmegaMinus ↥(lBar V₀ V hV L) 4 1)
    (hS : SumOfNat (fun H U Z => NatOmegaMinus H U Z 4 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inl ⟨5, le_rfl, by norm_num, s16k_isAlt_five_of_isOmegaMinus_four hΩ,
    (s16k_star h).sumOfNat_map (fun ρ θ hθ he hk I _ hI =>
      s16k_alternatingNatural_five_of_natOmegaMinus_four
        (s16k_natOmegaMinus_map hI ρ hk θ hθ he)) hS⟩⟩

theorem s16k_case162_2_of_omegaPlus_six (h : S16kBase D V₀ V L hV)
    (hΩ : IsOmegaPlus ↥(lBar V₀ V hV L) 6 1)
    (hS : SumOfNat (fun H U Z => NatOmegaPlus H U Z 6 1) (lBar V₀ V hV L)
      (commSub ⊤ (lBar V₀ V hV L)) (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 2) :
    Case162_2 D V₀ V hV L :=
  ⟨h.s1, Or.inl ⟨8, by norm_num, by norm_num, s15k_omp6_isAlt8 hΩ,
    (s16k_star h).sumOfNat_map (fun ρ θ hθ he hk I _ hI =>
      s16k_alternatingNatural_eight_of_natOmegaPlus_six
        (s16k_natOmegaPlus_map hI ρ hk θ hθ he)) hS⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
