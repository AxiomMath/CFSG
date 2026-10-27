module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FModel
public import CFSG.RankThree.PartTwo.Sec8.Hering88Cases

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


namespace Hering88F


theorem classB_x_eq_c (h45 : Sec4.Item4_5) (hF : KF84Field) (h47 : Sec4.Inputs47ClassesD4)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G}
    {X : Subgroup G} {n : ℕ} (h : Sec8Pair G A c L a b X n) (hn2 : 2 ≤ n)
    (hKL2 : Nonempty (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({b} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n))))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hIJ : sec8I L a ⊔ sec8J X a ≤ Y)
    (hxY : KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField)
    {A₀ : Subgroup G} {d' : G} {m : ℕ} (hodd : Odd m) (hm2 : 2 ≤ m)
    (hc1 : Case83One Y c A₀ d' m)
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers c) Y) m)
    {d : G} (hdcl : d ∈ Subgroup.closure ({c, b} : Set G)) (hdc : d ∉ Subgroup.zpowers c)
    (hdA : d ∈ A) (hd3 : d ^ 3 = 1) (hdN : d ∈ Subgroup.normalizer (Y : Set G))
    (hin : KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)))
    (hne : Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1) :
    Nonempty (imageModTheta Y (inSubgroup perfectResidual
      (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * m))) := by
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    hxY.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hcout : Sec4.InducesOuterTheta c Y := by
    rcases hxY with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hc3 : c ^ 3 = 1 := hA3 c h.mem_A
  have hcd : c * d = d * c := hAc c h.mem_A d hdA
  refine classB_core_c h45 hF h hn2 hKL2 hY hIJ hcN hm2 hG2 hdcl hdc hdA hd3 hdN ?_
  rcases hc1.1 with hD | hG
  · obtain ⟨-, K, _, _, σ, hK, hσ, ⟨e⟩⟩ := Item812Res7.exists_trialityD4_model hD
    exact classBDichotomy_d4 h47 hcN hdN hcd hc3 hd3 hcout hin hne hm2 hodd hK hσ e hG2
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG
    exact classBDichotomy_g2 hcN hdN hcd hc3 hd3 hcout hin hne hm2 hodd hK e

end Hering88F

end CFSG.RankThree.PartTwo.Sec8
